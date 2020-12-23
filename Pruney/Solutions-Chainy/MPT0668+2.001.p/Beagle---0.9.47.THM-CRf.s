%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:18 EST 2020

% Result     : Theorem 12.95s
% Output     : CNFRefutation 13.60s
% Verified   : 
% Statistics : Number of formulae       :  432 (77126 expanded)
%              Number of leaves         :   23 (26074 expanded)
%              Depth                    :   46
%              Number of atoms          : 1132 (364317 expanded)
%              Number of equality atoms :  218 (84087 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k8_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ( B = k8_relat_1(A,C)
            <=> ( ! [D] :
                    ( r2_hidden(D,k1_relat_1(B))
                  <=> ( r2_hidden(D,k1_relat_1(C))
                      & r2_hidden(k1_funct_1(C,D),A) ) )
                & ! [D] :
                    ( r2_hidden(D,k1_relat_1(B))
                   => k1_funct_1(B,D) = k1_funct_1(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_39,axiom,(
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

tff(c_112,plain,(
    ! [D_35] :
      ( k8_relat_1('#skF_5','#skF_7') = '#skF_6'
      | r2_hidden(D_35,k1_relat_1('#skF_7'))
      | ~ r2_hidden(D_35,k1_relat_1('#skF_6')) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_163,plain,(
    k8_relat_1('#skF_5','#skF_7') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_54,plain,
    ( ~ r2_hidden('#skF_8',k1_relat_1('#skF_6'))
    | r2_hidden('#skF_9',k1_relat_1('#skF_6'))
    | r2_hidden('#skF_10',k1_relat_1('#skF_6'))
    | k8_relat_1('#skF_5','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_183,plain,
    ( ~ r2_hidden('#skF_8',k1_relat_1('#skF_6'))
    | r2_hidden('#skF_9',k1_relat_1('#skF_6'))
    | r2_hidden('#skF_10',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_54])).

tff(c_184,plain,(
    ~ r2_hidden('#skF_8',k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_183])).

tff(c_46,plain,
    ( r2_hidden('#skF_8',k1_relat_1('#skF_7'))
    | r2_hidden('#skF_9',k1_relat_1('#skF_6'))
    | k1_funct_1('#skF_7','#skF_10') != k1_funct_1('#skF_6','#skF_10')
    | k8_relat_1('#skF_5','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_257,plain,
    ( r2_hidden('#skF_8',k1_relat_1('#skF_7'))
    | r2_hidden('#skF_9',k1_relat_1('#skF_6'))
    | k1_funct_1('#skF_7','#skF_10') != k1_funct_1('#skF_6','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_46])).

tff(c_258,plain,(
    k1_funct_1('#skF_7','#skF_10') != k1_funct_1('#skF_6','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_257])).

tff(c_58,plain,
    ( r2_hidden('#skF_8',k1_relat_1('#skF_7'))
    | r2_hidden('#skF_9',k1_relat_1('#skF_6'))
    | r2_hidden('#skF_10',k1_relat_1('#skF_6'))
    | k8_relat_1('#skF_5','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_186,plain,
    ( r2_hidden('#skF_8',k1_relat_1('#skF_7'))
    | r2_hidden('#skF_9',k1_relat_1('#skF_6'))
    | r2_hidden('#skF_10',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_58])).

tff(c_187,plain,(
    r2_hidden('#skF_10',k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_32,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_30,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_20,plain,(
    ! [A_19,C_21] :
      ( r2_hidden(k4_tarski(A_19,k1_funct_1(C_21,A_19)),C_21)
      | ~ r2_hidden(A_19,k1_relat_1(C_21))
      | ~ v1_funct_1(C_21)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_28,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_26,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_213,plain,(
    ! [D_52,E_53,B_54,A_55] :
      ( r2_hidden(k4_tarski(D_52,E_53),B_54)
      | ~ r2_hidden(k4_tarski(D_52,E_53),k8_relat_1(A_55,B_54))
      | ~ v1_relat_1(k8_relat_1(A_55,B_54))
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_220,plain,(
    ! [D_52,E_53] :
      ( r2_hidden(k4_tarski(D_52,E_53),'#skF_7')
      | ~ r2_hidden(k4_tarski(D_52,E_53),'#skF_6')
      | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_7'))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_213])).

tff(c_224,plain,(
    ! [D_56,E_57] :
      ( r2_hidden(k4_tarski(D_56,E_57),'#skF_7')
      | ~ r2_hidden(k4_tarski(D_56,E_57),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_163,c_220])).

tff(c_22,plain,(
    ! [C_21,A_19,B_20] :
      ( k1_funct_1(C_21,A_19) = B_20
      | ~ r2_hidden(k4_tarski(A_19,B_20),C_21)
      | ~ v1_funct_1(C_21)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_230,plain,(
    ! [D_56,E_57] :
      ( k1_funct_1('#skF_7',D_56) = E_57
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(k4_tarski(D_56,E_57),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_224,c_22])).

tff(c_259,plain,(
    ! [D_61,E_62] :
      ( k1_funct_1('#skF_7',D_61) = E_62
      | ~ r2_hidden(k4_tarski(D_61,E_62),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_230])).

tff(c_263,plain,(
    ! [A_19] :
      ( k1_funct_1('#skF_7',A_19) = k1_funct_1('#skF_6',A_19)
      | ~ r2_hidden(A_19,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_20,c_259])).

tff(c_267,plain,(
    ! [A_63] :
      ( k1_funct_1('#skF_7',A_63) = k1_funct_1('#skF_6',A_63)
      | ~ r2_hidden(A_63,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_263])).

tff(c_270,plain,(
    k1_funct_1('#skF_7','#skF_10') = k1_funct_1('#skF_6','#skF_10') ),
    inference(resolution,[status(thm)],[c_187,c_267])).

tff(c_278,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_258,c_270])).

tff(c_279,plain,
    ( r2_hidden('#skF_9',k1_relat_1('#skF_6'))
    | r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_257])).

tff(c_297,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_279])).

tff(c_44,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_8'),'#skF_5')
    | r2_hidden('#skF_9',k1_relat_1('#skF_6'))
    | k1_funct_1('#skF_7','#skF_10') != k1_funct_1('#skF_6','#skF_10')
    | k8_relat_1('#skF_5','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_282,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_8'),'#skF_5')
    | r2_hidden('#skF_9',k1_relat_1('#skF_6'))
    | k1_funct_1('#skF_7','#skF_10') != k1_funct_1('#skF_6','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_44])).

tff(c_283,plain,(
    k1_funct_1('#skF_7','#skF_10') != k1_funct_1('#skF_6','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_282])).

tff(c_280,plain,(
    k1_funct_1('#skF_7','#skF_10') = k1_funct_1('#skF_6','#skF_10') ),
    inference(splitRight,[status(thm)],[c_257])).

tff(c_284,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_283,c_280])).

tff(c_285,plain,
    ( r2_hidden('#skF_9',k1_relat_1('#skF_6'))
    | r2_hidden(k1_funct_1('#skF_7','#skF_8'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_282])).

tff(c_298,plain,(
    r2_hidden(k1_funct_1('#skF_7','#skF_8'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_285])).

tff(c_346,plain,(
    ! [D_67,E_68,A_69,B_70] :
      ( r2_hidden(k4_tarski(D_67,E_68),k8_relat_1(A_69,B_70))
      | ~ r2_hidden(k4_tarski(D_67,E_68),B_70)
      | ~ r2_hidden(E_68,A_69)
      | ~ v1_relat_1(k8_relat_1(A_69,B_70))
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_361,plain,(
    ! [D_67,E_68] :
      ( r2_hidden(k4_tarski(D_67,E_68),'#skF_6')
      | ~ r2_hidden(k4_tarski(D_67,E_68),'#skF_7')
      | ~ r2_hidden(E_68,'#skF_5')
      | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_7'))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_346])).

tff(c_368,plain,(
    ! [D_71,E_72] :
      ( r2_hidden(k4_tarski(D_71,E_72),'#skF_6')
      | ~ r2_hidden(k4_tarski(D_71,E_72),'#skF_7')
      | ~ r2_hidden(E_72,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_163,c_361])).

tff(c_378,plain,(
    ! [A_19] :
      ( r2_hidden(k4_tarski(A_19,k1_funct_1('#skF_7',A_19)),'#skF_6')
      | ~ r2_hidden(k1_funct_1('#skF_7',A_19),'#skF_5')
      | ~ r2_hidden(A_19,k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_20,c_368])).

tff(c_423,plain,(
    ! [A_73] :
      ( r2_hidden(k4_tarski(A_73,k1_funct_1('#skF_7',A_73)),'#skF_6')
      | ~ r2_hidden(k1_funct_1('#skF_7',A_73),'#skF_5')
      | ~ r2_hidden(A_73,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_378])).

tff(c_24,plain,(
    ! [A_19,C_21,B_20] :
      ( r2_hidden(A_19,k1_relat_1(C_21))
      | ~ r2_hidden(k4_tarski(A_19,B_20),C_21)
      | ~ v1_funct_1(C_21)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_435,plain,(
    ! [A_73] :
      ( r2_hidden(A_73,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(k1_funct_1('#skF_7',A_73),'#skF_5')
      | ~ r2_hidden(A_73,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_423,c_24])).

tff(c_456,plain,(
    ! [A_74] :
      ( r2_hidden(A_74,k1_relat_1('#skF_6'))
      | ~ r2_hidden(k1_funct_1('#skF_7',A_74),'#skF_5')
      | ~ r2_hidden(A_74,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_435])).

tff(c_459,plain,
    ( r2_hidden('#skF_8',k1_relat_1('#skF_6'))
    | ~ r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_298,c_456])).

tff(c_465,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_459])).

tff(c_467,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_184,c_465])).

tff(c_469,plain,(
    ~ r2_hidden(k1_funct_1('#skF_7','#skF_8'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_285])).

tff(c_468,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_285])).

tff(c_227,plain,(
    ! [D_56,E_57] :
      ( r2_hidden(D_56,k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(k4_tarski(D_56,E_57),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_224,c_24])).

tff(c_237,plain,(
    ! [D_58,E_59] :
      ( r2_hidden(D_58,k1_relat_1('#skF_7'))
      | ~ r2_hidden(k4_tarski(D_58,E_59),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_227])).

tff(c_241,plain,(
    ! [A_19] :
      ( r2_hidden(A_19,k1_relat_1('#skF_7'))
      | ~ r2_hidden(A_19,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_20,c_237])).

tff(c_244,plain,(
    ! [A_19] :
      ( r2_hidden(A_19,k1_relat_1('#skF_7'))
      | ~ r2_hidden(A_19,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_241])).

tff(c_470,plain,(
    ! [D_75,E_76] :
      ( k1_funct_1('#skF_7',D_75) = E_76
      | ~ r2_hidden(k4_tarski(D_75,E_76),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_230])).

tff(c_474,plain,(
    ! [A_19] :
      ( k1_funct_1('#skF_7',A_19) = k1_funct_1('#skF_6',A_19)
      | ~ r2_hidden(A_19,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_20,c_470])).

tff(c_478,plain,(
    ! [A_77] :
      ( k1_funct_1('#skF_7',A_77) = k1_funct_1('#skF_6',A_77)
      | ~ r2_hidden(A_77,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_474])).

tff(c_489,plain,(
    k1_funct_1('#skF_7','#skF_9') = k1_funct_1('#skF_6','#skF_9') ),
    inference(resolution,[status(thm)],[c_468,c_478])).

tff(c_497,plain,
    ( r2_hidden(k4_tarski('#skF_9',k1_funct_1('#skF_6','#skF_9')),'#skF_7')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_489,c_20])).

tff(c_501,plain,
    ( r2_hidden(k4_tarski('#skF_9',k1_funct_1('#skF_6','#skF_9')),'#skF_7')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_497])).

tff(c_526,plain,(
    ~ r2_hidden('#skF_9',k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_501])).

tff(c_529,plain,(
    ~ r2_hidden('#skF_9',k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_244,c_526])).

tff(c_533,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_529])).

tff(c_535,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_501])).

tff(c_188,plain,(
    ! [E_45,A_46,D_47,B_48] :
      ( r2_hidden(E_45,A_46)
      | ~ r2_hidden(k4_tarski(D_47,E_45),k8_relat_1(A_46,B_48))
      | ~ v1_relat_1(k8_relat_1(A_46,B_48))
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_195,plain,(
    ! [E_45,D_47] :
      ( r2_hidden(E_45,'#skF_5')
      | ~ r2_hidden(k4_tarski(D_47,E_45),'#skF_6')
      | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_7'))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_188])).

tff(c_199,plain,(
    ! [E_49,D_50] :
      ( r2_hidden(E_49,'#skF_5')
      | ~ r2_hidden(k4_tarski(D_50,E_49),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_163,c_195])).

tff(c_203,plain,(
    ! [A_19] :
      ( r2_hidden(k1_funct_1('#skF_6',A_19),'#skF_5')
      | ~ r2_hidden(A_19,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_20,c_199])).

tff(c_206,plain,(
    ! [A_19] :
      ( r2_hidden(k1_funct_1('#skF_6',A_19),'#skF_5')
      | ~ r2_hidden(A_19,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_203])).

tff(c_534,plain,(
    r2_hidden(k4_tarski('#skF_9',k1_funct_1('#skF_6','#skF_9')),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_501])).

tff(c_552,plain,(
    ! [D_78,E_79,A_80,B_81] :
      ( r2_hidden(k4_tarski(D_78,E_79),k8_relat_1(A_80,B_81))
      | ~ r2_hidden(k4_tarski(D_78,E_79),B_81)
      | ~ r2_hidden(E_79,A_80)
      | ~ v1_relat_1(k8_relat_1(A_80,B_81))
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_567,plain,(
    ! [D_78,E_79] :
      ( r2_hidden(k4_tarski(D_78,E_79),'#skF_6')
      | ~ r2_hidden(k4_tarski(D_78,E_79),'#skF_7')
      | ~ r2_hidden(E_79,'#skF_5')
      | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_7'))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_552])).

tff(c_574,plain,(
    ! [D_82,E_83] :
      ( r2_hidden(k4_tarski(D_82,E_83),'#skF_6')
      | ~ r2_hidden(k4_tarski(D_82,E_83),'#skF_7')
      | ~ r2_hidden(E_83,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_163,c_567])).

tff(c_588,plain,
    ( r2_hidden(k4_tarski('#skF_9',k1_funct_1('#skF_6','#skF_9')),'#skF_6')
    | ~ r2_hidden(k1_funct_1('#skF_6','#skF_9'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_534,c_574])).

tff(c_633,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_9'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_588])).

tff(c_638,plain,(
    ~ r2_hidden('#skF_9',k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_206,c_633])).

tff(c_642,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_638])).

tff(c_644,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_9'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_588])).

tff(c_38,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_8'),'#skF_5')
    | ~ r2_hidden(k1_funct_1('#skF_7','#skF_9'),'#skF_5')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_7'))
    | k1_funct_1('#skF_7','#skF_10') != k1_funct_1('#skF_6','#skF_10')
    | k8_relat_1('#skF_5','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_778,plain,(
    r2_hidden(k1_funct_1('#skF_7','#skF_8'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_280,c_535,c_644,c_489,c_38])).

tff(c_779,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_469,c_778])).

tff(c_781,plain,(
    ~ r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_279])).

tff(c_780,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_279])).

tff(c_787,plain,(
    ! [D_90,E_91] :
      ( k1_funct_1('#skF_7',D_90) = E_91
      | ~ r2_hidden(k4_tarski(D_90,E_91),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_230])).

tff(c_791,plain,(
    ! [A_19] :
      ( k1_funct_1('#skF_7',A_19) = k1_funct_1('#skF_6',A_19)
      | ~ r2_hidden(A_19,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_20,c_787])).

tff(c_797,plain,(
    ! [A_92] :
      ( k1_funct_1('#skF_7',A_92) = k1_funct_1('#skF_6',A_92)
      | ~ r2_hidden(A_92,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_791])).

tff(c_808,plain,(
    k1_funct_1('#skF_7','#skF_9') = k1_funct_1('#skF_6','#skF_9') ),
    inference(resolution,[status(thm)],[c_780,c_797])).

tff(c_815,plain,
    ( r2_hidden(k4_tarski('#skF_9',k1_funct_1('#skF_6','#skF_9')),'#skF_7')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_808,c_20])).

tff(c_819,plain,
    ( r2_hidden(k4_tarski('#skF_9',k1_funct_1('#skF_6','#skF_9')),'#skF_7')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_815])).

tff(c_844,plain,(
    ~ r2_hidden('#skF_9',k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_819])).

tff(c_847,plain,(
    ~ r2_hidden('#skF_9',k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_244,c_844])).

tff(c_851,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_780,c_847])).

tff(c_853,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_819])).

tff(c_852,plain,(
    r2_hidden(k4_tarski('#skF_9',k1_funct_1('#skF_6','#skF_9')),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_819])).

tff(c_871,plain,(
    ! [D_93,E_94,A_95,B_96] :
      ( r2_hidden(k4_tarski(D_93,E_94),k8_relat_1(A_95,B_96))
      | ~ r2_hidden(k4_tarski(D_93,E_94),B_96)
      | ~ r2_hidden(E_94,A_95)
      | ~ v1_relat_1(k8_relat_1(A_95,B_96))
      | ~ v1_relat_1(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_886,plain,(
    ! [D_93,E_94] :
      ( r2_hidden(k4_tarski(D_93,E_94),'#skF_6')
      | ~ r2_hidden(k4_tarski(D_93,E_94),'#skF_7')
      | ~ r2_hidden(E_94,'#skF_5')
      | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_7'))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_871])).

tff(c_893,plain,(
    ! [D_97,E_98] :
      ( r2_hidden(k4_tarski(D_97,E_98),'#skF_6')
      | ~ r2_hidden(k4_tarski(D_97,E_98),'#skF_7')
      | ~ r2_hidden(E_98,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_163,c_886])).

tff(c_907,plain,
    ( r2_hidden(k4_tarski('#skF_9',k1_funct_1('#skF_6','#skF_9')),'#skF_6')
    | ~ r2_hidden(k1_funct_1('#skF_6','#skF_9'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_852,c_893])).

tff(c_953,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_9'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_907])).

tff(c_956,plain,(
    ~ r2_hidden('#skF_9',k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_206,c_953])).

tff(c_960,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_780,c_956])).

tff(c_962,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_9'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_907])).

tff(c_40,plain,
    ( r2_hidden('#skF_8',k1_relat_1('#skF_7'))
    | ~ r2_hidden(k1_funct_1('#skF_7','#skF_9'),'#skF_5')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_7'))
    | k1_funct_1('#skF_7','#skF_10') != k1_funct_1('#skF_6','#skF_10')
    | k8_relat_1('#skF_5','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1073,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_280,c_853,c_962,c_808,c_40])).

tff(c_1074,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_781,c_1073])).

tff(c_1075,plain,
    ( r2_hidden('#skF_9',k1_relat_1('#skF_6'))
    | r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_1077,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1075])).

tff(c_1076,plain,(
    ~ r2_hidden('#skF_10',k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_56,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_8'),'#skF_5')
    | r2_hidden('#skF_9',k1_relat_1('#skF_6'))
    | r2_hidden('#skF_10',k1_relat_1('#skF_6'))
    | k8_relat_1('#skF_5','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1098,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_8'),'#skF_5')
    | r2_hidden('#skF_9',k1_relat_1('#skF_6'))
    | r2_hidden('#skF_10',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_56])).

tff(c_1099,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_8'),'#skF_5')
    | r2_hidden('#skF_9',k1_relat_1('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_1076,c_1098])).

tff(c_1100,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1099])).

tff(c_1105,plain,(
    ! [D_109,E_110,B_111,A_112] :
      ( r2_hidden(k4_tarski(D_109,E_110),B_111)
      | ~ r2_hidden(k4_tarski(D_109,E_110),k8_relat_1(A_112,B_111))
      | ~ v1_relat_1(k8_relat_1(A_112,B_111))
      | ~ v1_relat_1(B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1112,plain,(
    ! [D_109,E_110] :
      ( r2_hidden(k4_tarski(D_109,E_110),'#skF_7')
      | ~ r2_hidden(k4_tarski(D_109,E_110),'#skF_6')
      | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_7'))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_1105])).

tff(c_1118,plain,(
    ! [D_113,E_114] :
      ( r2_hidden(k4_tarski(D_113,E_114),'#skF_7')
      | ~ r2_hidden(k4_tarski(D_113,E_114),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_163,c_1112])).

tff(c_1121,plain,(
    ! [D_113,E_114] :
      ( r2_hidden(D_113,k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(k4_tarski(D_113,E_114),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1118,c_24])).

tff(c_1131,plain,(
    ! [D_115,E_116] :
      ( r2_hidden(D_115,k1_relat_1('#skF_7'))
      | ~ r2_hidden(k4_tarski(D_115,E_116),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1121])).

tff(c_1135,plain,(
    ! [A_19] :
      ( r2_hidden(A_19,k1_relat_1('#skF_7'))
      | ~ r2_hidden(A_19,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_20,c_1131])).

tff(c_1138,plain,(
    ! [A_19] :
      ( r2_hidden(A_19,k1_relat_1('#skF_7'))
      | ~ r2_hidden(A_19,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1135])).

tff(c_1124,plain,(
    ! [D_113,E_114] :
      ( k1_funct_1('#skF_7',D_113) = E_114
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(k4_tarski(D_113,E_114),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1118,c_22])).

tff(c_1152,plain,(
    ! [D_118,E_119] :
      ( k1_funct_1('#skF_7',D_118) = E_119
      | ~ r2_hidden(k4_tarski(D_118,E_119),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1124])).

tff(c_1156,plain,(
    ! [A_19] :
      ( k1_funct_1('#skF_7',A_19) = k1_funct_1('#skF_6',A_19)
      | ~ r2_hidden(A_19,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_20,c_1152])).

tff(c_1160,plain,(
    ! [A_120] :
      ( k1_funct_1('#skF_7',A_120) = k1_funct_1('#skF_6',A_120)
      | ~ r2_hidden(A_120,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1156])).

tff(c_1168,plain,(
    k1_funct_1('#skF_7','#skF_9') = k1_funct_1('#skF_6','#skF_9') ),
    inference(resolution,[status(thm)],[c_1100,c_1160])).

tff(c_1173,plain,
    ( r2_hidden(k4_tarski('#skF_9',k1_funct_1('#skF_6','#skF_9')),'#skF_7')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1168,c_20])).

tff(c_1177,plain,
    ( r2_hidden(k4_tarski('#skF_9',k1_funct_1('#skF_6','#skF_9')),'#skF_7')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1173])).

tff(c_1179,plain,(
    ~ r2_hidden('#skF_9',k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1177])).

tff(c_1182,plain,(
    ~ r2_hidden('#skF_9',k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_1138,c_1179])).

tff(c_1186,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1100,c_1182])).

tff(c_1188,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1177])).

tff(c_1078,plain,(
    ! [E_102,A_103,D_104,B_105] :
      ( r2_hidden(E_102,A_103)
      | ~ r2_hidden(k4_tarski(D_104,E_102),k8_relat_1(A_103,B_105))
      | ~ v1_relat_1(k8_relat_1(A_103,B_105))
      | ~ v1_relat_1(B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1085,plain,(
    ! [E_102,D_104] :
      ( r2_hidden(E_102,'#skF_5')
      | ~ r2_hidden(k4_tarski(D_104,E_102),'#skF_6')
      | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_7'))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_1078])).

tff(c_1089,plain,(
    ! [E_106,D_107] :
      ( r2_hidden(E_106,'#skF_5')
      | ~ r2_hidden(k4_tarski(D_107,E_106),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_163,c_1085])).

tff(c_1093,plain,(
    ! [A_19] :
      ( r2_hidden(k1_funct_1('#skF_6',A_19),'#skF_5')
      | ~ r2_hidden(A_19,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_20,c_1089])).

tff(c_1096,plain,(
    ! [A_19] :
      ( r2_hidden(k1_funct_1('#skF_6',A_19),'#skF_5')
      | ~ r2_hidden(A_19,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1093])).

tff(c_1187,plain,(
    r2_hidden(k4_tarski('#skF_9',k1_funct_1('#skF_6','#skF_9')),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_1177])).

tff(c_1212,plain,(
    ! [D_121,E_122,A_123,B_124] :
      ( r2_hidden(k4_tarski(D_121,E_122),k8_relat_1(A_123,B_124))
      | ~ r2_hidden(k4_tarski(D_121,E_122),B_124)
      | ~ r2_hidden(E_122,A_123)
      | ~ v1_relat_1(k8_relat_1(A_123,B_124))
      | ~ v1_relat_1(B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1227,plain,(
    ! [D_121,E_122] :
      ( r2_hidden(k4_tarski(D_121,E_122),'#skF_6')
      | ~ r2_hidden(k4_tarski(D_121,E_122),'#skF_7')
      | ~ r2_hidden(E_122,'#skF_5')
      | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_7'))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_1212])).

tff(c_1234,plain,(
    ! [D_125,E_126] :
      ( r2_hidden(k4_tarski(D_125,E_126),'#skF_6')
      | ~ r2_hidden(k4_tarski(D_125,E_126),'#skF_7')
      | ~ r2_hidden(E_126,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_163,c_1227])).

tff(c_1245,plain,
    ( r2_hidden(k4_tarski('#skF_9',k1_funct_1('#skF_6','#skF_9')),'#skF_6')
    | ~ r2_hidden(k1_funct_1('#skF_6','#skF_9'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_1187,c_1234])).

tff(c_1250,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_9'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1245])).

tff(c_1253,plain,(
    ~ r2_hidden('#skF_9',k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_1096,c_1250])).

tff(c_1257,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1100,c_1253])).

tff(c_1259,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_9'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_1245])).

tff(c_50,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_8'),'#skF_5')
    | ~ r2_hidden(k1_funct_1('#skF_7','#skF_9'),'#skF_5')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_7'))
    | r2_hidden('#skF_10',k1_relat_1('#skF_6'))
    | k8_relat_1('#skF_5','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1346,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_8'),'#skF_5')
    | r2_hidden('#skF_10',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_1188,c_1259,c_1168,c_50])).

tff(c_1347,plain,(
    r2_hidden(k1_funct_1('#skF_7','#skF_8'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_1076,c_1346])).

tff(c_1244,plain,(
    ! [A_19] :
      ( r2_hidden(k4_tarski(A_19,k1_funct_1('#skF_7',A_19)),'#skF_6')
      | ~ r2_hidden(k1_funct_1('#skF_7',A_19),'#skF_5')
      | ~ r2_hidden(A_19,k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_20,c_1234])).

tff(c_1291,plain,(
    ! [A_127] :
      ( r2_hidden(k4_tarski(A_127,k1_funct_1('#skF_7',A_127)),'#skF_6')
      | ~ r2_hidden(k1_funct_1('#skF_7',A_127),'#skF_5')
      | ~ r2_hidden(A_127,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1244])).

tff(c_1303,plain,(
    ! [A_127] :
      ( r2_hidden(A_127,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(k1_funct_1('#skF_7',A_127),'#skF_5')
      | ~ r2_hidden(A_127,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_1291,c_24])).

tff(c_1316,plain,(
    ! [A_127] :
      ( r2_hidden(A_127,k1_relat_1('#skF_6'))
      | ~ r2_hidden(k1_funct_1('#skF_7',A_127),'#skF_5')
      | ~ r2_hidden(A_127,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1303])).

tff(c_1353,plain,
    ( r2_hidden('#skF_8',k1_relat_1('#skF_6'))
    | ~ r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_1347,c_1316])).

tff(c_1359,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1077,c_1353])).

tff(c_1361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_184,c_1359])).

tff(c_1362,plain,(
    r2_hidden(k1_funct_1('#skF_7','#skF_8'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_1099])).

tff(c_1442,plain,(
    ! [D_143,E_144,A_145,B_146] :
      ( r2_hidden(k4_tarski(D_143,E_144),k8_relat_1(A_145,B_146))
      | ~ r2_hidden(k4_tarski(D_143,E_144),B_146)
      | ~ r2_hidden(E_144,A_145)
      | ~ v1_relat_1(k8_relat_1(A_145,B_146))
      | ~ v1_relat_1(B_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1457,plain,(
    ! [D_143,E_144] :
      ( r2_hidden(k4_tarski(D_143,E_144),'#skF_6')
      | ~ r2_hidden(k4_tarski(D_143,E_144),'#skF_7')
      | ~ r2_hidden(E_144,'#skF_5')
      | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_7'))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_1442])).

tff(c_1464,plain,(
    ! [D_147,E_148] :
      ( r2_hidden(k4_tarski(D_147,E_148),'#skF_6')
      | ~ r2_hidden(k4_tarski(D_147,E_148),'#skF_7')
      | ~ r2_hidden(E_148,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_163,c_1457])).

tff(c_1471,plain,(
    ! [A_19] :
      ( r2_hidden(k4_tarski(A_19,k1_funct_1('#skF_7',A_19)),'#skF_6')
      | ~ r2_hidden(k1_funct_1('#skF_7',A_19),'#skF_5')
      | ~ r2_hidden(A_19,k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_20,c_1464])).

tff(c_1476,plain,(
    ! [A_149] :
      ( r2_hidden(k4_tarski(A_149,k1_funct_1('#skF_7',A_149)),'#skF_6')
      | ~ r2_hidden(k1_funct_1('#skF_7',A_149),'#skF_5')
      | ~ r2_hidden(A_149,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1471])).

tff(c_1488,plain,(
    ! [A_149] :
      ( r2_hidden(A_149,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(k1_funct_1('#skF_7',A_149),'#skF_5')
      | ~ r2_hidden(A_149,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_1476,c_24])).

tff(c_1503,plain,(
    ! [A_150] :
      ( r2_hidden(A_150,k1_relat_1('#skF_6'))
      | ~ r2_hidden(k1_funct_1('#skF_7',A_150),'#skF_5')
      | ~ r2_hidden(A_150,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1488])).

tff(c_1506,plain,
    ( r2_hidden('#skF_8',k1_relat_1('#skF_6'))
    | ~ r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_1362,c_1503])).

tff(c_1509,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1077,c_1506])).

tff(c_1511,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_184,c_1509])).

tff(c_1512,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1075])).

tff(c_1517,plain,(
    ! [E_151,A_152,D_153,B_154] :
      ( r2_hidden(E_151,A_152)
      | ~ r2_hidden(k4_tarski(D_153,E_151),k8_relat_1(A_152,B_154))
      | ~ v1_relat_1(k8_relat_1(A_152,B_154))
      | ~ v1_relat_1(B_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1524,plain,(
    ! [E_151,D_153] :
      ( r2_hidden(E_151,'#skF_5')
      | ~ r2_hidden(k4_tarski(D_153,E_151),'#skF_6')
      | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_7'))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_1517])).

tff(c_1528,plain,(
    ! [E_155,D_156] :
      ( r2_hidden(E_155,'#skF_5')
      | ~ r2_hidden(k4_tarski(D_156,E_155),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_163,c_1524])).

tff(c_1532,plain,(
    ! [A_19] :
      ( r2_hidden(k1_funct_1('#skF_6',A_19),'#skF_5')
      | ~ r2_hidden(A_19,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_20,c_1528])).

tff(c_1535,plain,(
    ! [A_19] :
      ( r2_hidden(k1_funct_1('#skF_6',A_19),'#skF_5')
      | ~ r2_hidden(A_19,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1532])).

tff(c_1513,plain,(
    ~ r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1075])).

tff(c_1538,plain,(
    ! [D_158,E_159,B_160,A_161] :
      ( r2_hidden(k4_tarski(D_158,E_159),B_160)
      | ~ r2_hidden(k4_tarski(D_158,E_159),k8_relat_1(A_161,B_160))
      | ~ v1_relat_1(k8_relat_1(A_161,B_160))
      | ~ v1_relat_1(B_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1545,plain,(
    ! [D_158,E_159] :
      ( r2_hidden(k4_tarski(D_158,E_159),'#skF_7')
      | ~ r2_hidden(k4_tarski(D_158,E_159),'#skF_6')
      | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_7'))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_1538])).

tff(c_1551,plain,(
    ! [D_162,E_163] :
      ( r2_hidden(k4_tarski(D_162,E_163),'#skF_7')
      | ~ r2_hidden(k4_tarski(D_162,E_163),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_163,c_1545])).

tff(c_1554,plain,(
    ! [D_162,E_163] :
      ( r2_hidden(D_162,k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(k4_tarski(D_162,E_163),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1551,c_24])).

tff(c_1564,plain,(
    ! [D_164,E_165] :
      ( r2_hidden(D_164,k1_relat_1('#skF_7'))
      | ~ r2_hidden(k4_tarski(D_164,E_165),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1554])).

tff(c_1568,plain,(
    ! [A_19] :
      ( r2_hidden(A_19,k1_relat_1('#skF_7'))
      | ~ r2_hidden(A_19,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_20,c_1564])).

tff(c_1571,plain,(
    ! [A_19] :
      ( r2_hidden(A_19,k1_relat_1('#skF_7'))
      | ~ r2_hidden(A_19,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1568])).

tff(c_1557,plain,(
    ! [D_162,E_163] :
      ( k1_funct_1('#skF_7',D_162) = E_163
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(k4_tarski(D_162,E_163),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1551,c_22])).

tff(c_1590,plain,(
    ! [D_167,E_168] :
      ( k1_funct_1('#skF_7',D_167) = E_168
      | ~ r2_hidden(k4_tarski(D_167,E_168),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1557])).

tff(c_1594,plain,(
    ! [A_19] :
      ( k1_funct_1('#skF_7',A_19) = k1_funct_1('#skF_6',A_19)
      | ~ r2_hidden(A_19,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_20,c_1590])).

tff(c_1598,plain,(
    ! [A_169] :
      ( k1_funct_1('#skF_7',A_169) = k1_funct_1('#skF_6',A_169)
      | ~ r2_hidden(A_169,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1594])).

tff(c_1606,plain,(
    k1_funct_1('#skF_7','#skF_9') = k1_funct_1('#skF_6','#skF_9') ),
    inference(resolution,[status(thm)],[c_1512,c_1598])).

tff(c_1611,plain,
    ( r2_hidden(k4_tarski('#skF_9',k1_funct_1('#skF_6','#skF_9')),'#skF_7')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1606,c_20])).

tff(c_1615,plain,
    ( r2_hidden(k4_tarski('#skF_9',k1_funct_1('#skF_6','#skF_9')),'#skF_7')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1611])).

tff(c_1617,plain,(
    ~ r2_hidden('#skF_9',k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1615])).

tff(c_1620,plain,(
    ~ r2_hidden('#skF_9',k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_1571,c_1617])).

tff(c_1624,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1512,c_1620])).

tff(c_1626,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1615])).

tff(c_52,plain,
    ( r2_hidden('#skF_8',k1_relat_1('#skF_7'))
    | ~ r2_hidden(k1_funct_1('#skF_7','#skF_9'),'#skF_5')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_7'))
    | r2_hidden('#skF_10',k1_relat_1('#skF_6'))
    | k8_relat_1('#skF_5','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1693,plain,
    ( r2_hidden('#skF_8',k1_relat_1('#skF_7'))
    | ~ r2_hidden(k1_funct_1('#skF_6','#skF_9'),'#skF_5')
    | r2_hidden('#skF_10',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_1626,c_1606,c_52])).

tff(c_1694,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_9'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_1076,c_1513,c_1693])).

tff(c_1697,plain,(
    ~ r2_hidden('#skF_9',k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_1535,c_1694])).

tff(c_1701,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1512,c_1697])).

tff(c_1702,plain,
    ( r2_hidden('#skF_10',k1_relat_1('#skF_6'))
    | r2_hidden('#skF_9',k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_1704,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1702])).

tff(c_1707,plain,(
    ! [E_176,A_177,D_178,B_179] :
      ( r2_hidden(E_176,A_177)
      | ~ r2_hidden(k4_tarski(D_178,E_176),k8_relat_1(A_177,B_179))
      | ~ v1_relat_1(k8_relat_1(A_177,B_179))
      | ~ v1_relat_1(B_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1714,plain,(
    ! [E_176,D_178] :
      ( r2_hidden(E_176,'#skF_5')
      | ~ r2_hidden(k4_tarski(D_178,E_176),'#skF_6')
      | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_7'))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_1707])).

tff(c_1719,plain,(
    ! [E_180,D_181] :
      ( r2_hidden(E_180,'#skF_5')
      | ~ r2_hidden(k4_tarski(D_181,E_180),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_163,c_1714])).

tff(c_1723,plain,(
    ! [A_19] :
      ( r2_hidden(k1_funct_1('#skF_6',A_19),'#skF_5')
      | ~ r2_hidden(A_19,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_20,c_1719])).

tff(c_1726,plain,(
    ! [A_19] :
      ( r2_hidden(k1_funct_1('#skF_6',A_19),'#skF_5')
      | ~ r2_hidden(A_19,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1723])).

tff(c_1732,plain,(
    ! [D_183,E_184,B_185,A_186] :
      ( r2_hidden(k4_tarski(D_183,E_184),B_185)
      | ~ r2_hidden(k4_tarski(D_183,E_184),k8_relat_1(A_186,B_185))
      | ~ v1_relat_1(k8_relat_1(A_186,B_185))
      | ~ v1_relat_1(B_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1739,plain,(
    ! [D_183,E_184] :
      ( r2_hidden(k4_tarski(D_183,E_184),'#skF_7')
      | ~ r2_hidden(k4_tarski(D_183,E_184),'#skF_6')
      | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_7'))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_1732])).

tff(c_1743,plain,(
    ! [D_187,E_188] :
      ( r2_hidden(k4_tarski(D_187,E_188),'#skF_7')
      | ~ r2_hidden(k4_tarski(D_187,E_188),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_163,c_1739])).

tff(c_1746,plain,(
    ! [D_187,E_188] :
      ( r2_hidden(D_187,k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(k4_tarski(D_187,E_188),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1743,c_24])).

tff(c_1756,plain,(
    ! [D_189,E_190] :
      ( r2_hidden(D_189,k1_relat_1('#skF_7'))
      | ~ r2_hidden(k4_tarski(D_189,E_190),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1746])).

tff(c_1760,plain,(
    ! [A_19] :
      ( r2_hidden(A_19,k1_relat_1('#skF_7'))
      | ~ r2_hidden(A_19,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_20,c_1756])).

tff(c_1763,plain,(
    ! [A_19] :
      ( r2_hidden(A_19,k1_relat_1('#skF_7'))
      | ~ r2_hidden(A_19,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1760])).

tff(c_1749,plain,(
    ! [D_187,E_188] :
      ( k1_funct_1('#skF_7',D_187) = E_188
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(k4_tarski(D_187,E_188),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1743,c_22])).

tff(c_1775,plain,(
    ! [D_192,E_193] :
      ( k1_funct_1('#skF_7',D_192) = E_193
      | ~ r2_hidden(k4_tarski(D_192,E_193),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1749])).

tff(c_1779,plain,(
    ! [A_19] :
      ( k1_funct_1('#skF_7',A_19) = k1_funct_1('#skF_6',A_19)
      | ~ r2_hidden(A_19,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_20,c_1775])).

tff(c_1785,plain,(
    ! [A_194] :
      ( k1_funct_1('#skF_7',A_194) = k1_funct_1('#skF_6',A_194)
      | ~ r2_hidden(A_194,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1779])).

tff(c_1796,plain,(
    k1_funct_1('#skF_7','#skF_9') = k1_funct_1('#skF_6','#skF_9') ),
    inference(resolution,[status(thm)],[c_1704,c_1785])).

tff(c_1811,plain,
    ( r2_hidden(k4_tarski('#skF_9',k1_funct_1('#skF_6','#skF_9')),'#skF_7')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1796,c_20])).

tff(c_1815,plain,
    ( r2_hidden(k4_tarski('#skF_9',k1_funct_1('#skF_6','#skF_9')),'#skF_7')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1811])).

tff(c_1841,plain,(
    ~ r2_hidden('#skF_9',k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1815])).

tff(c_1846,plain,(
    ~ r2_hidden('#skF_9',k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_1763,c_1841])).

tff(c_1850,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1704,c_1846])).

tff(c_1852,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1815])).

tff(c_1703,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_48,plain,
    ( ~ r2_hidden('#skF_8',k1_relat_1('#skF_6'))
    | ~ r2_hidden(k1_funct_1('#skF_7','#skF_9'),'#skF_5')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_7'))
    | r2_hidden('#skF_10',k1_relat_1('#skF_6'))
    | k8_relat_1('#skF_5','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1892,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_6','#skF_9'),'#skF_5')
    | r2_hidden('#skF_10',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_1852,c_1796,c_1703,c_48])).

tff(c_1893,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_9'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1892])).

tff(c_1896,plain,(
    ~ r2_hidden('#skF_9',k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_1726,c_1893])).

tff(c_1900,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1704,c_1896])).

tff(c_1901,plain,(
    r2_hidden('#skF_10',k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1892])).

tff(c_1782,plain,(
    ! [A_19] :
      ( k1_funct_1('#skF_7',A_19) = k1_funct_1('#skF_6',A_19)
      | ~ r2_hidden(A_19,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1779])).

tff(c_1906,plain,(
    k1_funct_1('#skF_7','#skF_10') = k1_funct_1('#skF_6','#skF_10') ),
    inference(resolution,[status(thm)],[c_1901,c_1782])).

tff(c_1902,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_9'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_1892])).

tff(c_36,plain,
    ( ~ r2_hidden('#skF_8',k1_relat_1('#skF_6'))
    | ~ r2_hidden(k1_funct_1('#skF_7','#skF_9'),'#skF_5')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_7'))
    | k1_funct_1('#skF_7','#skF_10') != k1_funct_1('#skF_6','#skF_10')
    | k8_relat_1('#skF_5','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2169,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_1906,c_1852,c_1902,c_1796,c_1703,c_36])).

tff(c_2171,plain,(
    ~ r2_hidden('#skF_9',k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1702])).

tff(c_2200,plain,
    ( r2_hidden('#skF_8',k1_relat_1('#skF_7'))
    | r2_hidden('#skF_9',k1_relat_1('#skF_6'))
    | k1_funct_1('#skF_7','#skF_10') != k1_funct_1('#skF_6','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_46])).

tff(c_2201,plain,
    ( r2_hidden('#skF_8',k1_relat_1('#skF_7'))
    | k1_funct_1('#skF_7','#skF_10') != k1_funct_1('#skF_6','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_2171,c_2200])).

tff(c_2202,plain,(
    k1_funct_1('#skF_7','#skF_10') != k1_funct_1('#skF_6','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_2201])).

tff(c_2170,plain,(
    r2_hidden('#skF_10',k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1702])).

tff(c_2203,plain,(
    ! [D_211,E_212,B_213,A_214] :
      ( r2_hidden(k4_tarski(D_211,E_212),B_213)
      | ~ r2_hidden(k4_tarski(D_211,E_212),k8_relat_1(A_214,B_213))
      | ~ v1_relat_1(k8_relat_1(A_214,B_213))
      | ~ v1_relat_1(B_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2210,plain,(
    ! [D_211,E_212] :
      ( r2_hidden(k4_tarski(D_211,E_212),'#skF_7')
      | ~ r2_hidden(k4_tarski(D_211,E_212),'#skF_6')
      | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_7'))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_2203])).

tff(c_2217,plain,(
    ! [D_215,E_216] :
      ( r2_hidden(k4_tarski(D_215,E_216),'#skF_7')
      | ~ r2_hidden(k4_tarski(D_215,E_216),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_163,c_2210])).

tff(c_2223,plain,(
    ! [D_215,E_216] :
      ( k1_funct_1('#skF_7',D_215) = E_216
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(k4_tarski(D_215,E_216),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2217,c_22])).

tff(c_2252,plain,(
    ! [D_220,E_221] :
      ( k1_funct_1('#skF_7',D_220) = E_221
      | ~ r2_hidden(k4_tarski(D_220,E_221),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_2223])).

tff(c_2256,plain,(
    ! [A_19] :
      ( k1_funct_1('#skF_7',A_19) = k1_funct_1('#skF_6',A_19)
      | ~ r2_hidden(A_19,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_20,c_2252])).

tff(c_2260,plain,(
    ! [A_222] :
      ( k1_funct_1('#skF_7',A_222) = k1_funct_1('#skF_6',A_222)
      | ~ r2_hidden(A_222,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_2256])).

tff(c_2263,plain,(
    k1_funct_1('#skF_7','#skF_10') = k1_funct_1('#skF_6','#skF_10') ),
    inference(resolution,[status(thm)],[c_2170,c_2260])).

tff(c_2274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2202,c_2263])).

tff(c_2276,plain,(
    k1_funct_1('#skF_7','#skF_10') = k1_funct_1('#skF_6','#skF_10') ),
    inference(splitRight,[status(thm)],[c_2201])).

tff(c_42,plain,
    ( ~ r2_hidden('#skF_8',k1_relat_1('#skF_6'))
    | r2_hidden('#skF_9',k1_relat_1('#skF_6'))
    | k1_funct_1('#skF_7','#skF_10') != k1_funct_1('#skF_6','#skF_10')
    | k8_relat_1('#skF_5','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2320,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_2276,c_1703,c_42])).

tff(c_2321,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2171,c_2320])).

tff(c_2323,plain,(
    k8_relat_1('#skF_5','#skF_7') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_10,plain,(
    ! [A_1,B_2,C_12] :
      ( r2_hidden(k4_tarski('#skF_1'(A_1,B_2,C_12),'#skF_2'(A_1,B_2,C_12)),B_2)
      | r2_hidden(k4_tarski('#skF_3'(A_1,B_2,C_12),'#skF_4'(A_1,B_2,C_12)),C_12)
      | k8_relat_1(A_1,B_2) = C_12
      | ~ v1_relat_1(C_12)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2991,plain,(
    ! [A_313,B_314,C_315] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_313,B_314,C_315),'#skF_2'(A_313,B_314,C_315)),C_315)
      | r2_hidden(k4_tarski('#skF_3'(A_313,B_314,C_315),'#skF_4'(A_313,B_314,C_315)),C_315)
      | k8_relat_1(A_313,B_314) = C_315
      | ~ v1_relat_1(C_315)
      | ~ v1_relat_1(B_314) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3017,plain,(
    ! [A_316,B_317] :
      ( r2_hidden(k4_tarski('#skF_3'(A_316,B_317,B_317),'#skF_4'(A_316,B_317,B_317)),B_317)
      | k8_relat_1(A_316,B_317) = B_317
      | ~ v1_relat_1(B_317) ) ),
    inference(resolution,[status(thm)],[c_10,c_2991])).

tff(c_3056,plain,(
    ! [A_316,B_317] :
      ( r2_hidden('#skF_3'(A_316,B_317,B_317),k1_relat_1(B_317))
      | ~ v1_funct_1(B_317)
      | k8_relat_1(A_316,B_317) = B_317
      | ~ v1_relat_1(B_317) ) ),
    inference(resolution,[status(thm)],[c_3017,c_24])).

tff(c_3055,plain,(
    ! [B_317,A_316] :
      ( k1_funct_1(B_317,'#skF_3'(A_316,B_317,B_317)) = '#skF_4'(A_316,B_317,B_317)
      | ~ v1_funct_1(B_317)
      | k8_relat_1(A_316,B_317) = B_317
      | ~ v1_relat_1(B_317) ) ),
    inference(resolution,[status(thm)],[c_3017,c_22])).

tff(c_3057,plain,(
    ! [A_318,B_319] :
      ( r2_hidden('#skF_3'(A_318,B_319,B_319),k1_relat_1(B_319))
      | ~ v1_funct_1(B_319)
      | k8_relat_1(A_318,B_319) = B_319
      | ~ v1_relat_1(B_319) ) ),
    inference(resolution,[status(thm)],[c_3017,c_24])).

tff(c_60,plain,(
    ! [D_36] :
      ( k8_relat_1('#skF_5','#skF_7') = '#skF_6'
      | k1_funct_1('#skF_7',D_36) = k1_funct_1('#skF_6',D_36)
      | ~ r2_hidden(D_36,k1_relat_1('#skF_6')) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2339,plain,(
    ! [D_36] :
      ( k1_funct_1('#skF_7',D_36) = k1_funct_1('#skF_6',D_36)
      | ~ r2_hidden(D_36,k1_relat_1('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2323,c_60])).

tff(c_3069,plain,(
    ! [A_318] :
      ( k1_funct_1('#skF_7','#skF_3'(A_318,'#skF_6','#skF_6')) = k1_funct_1('#skF_6','#skF_3'(A_318,'#skF_6','#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | k8_relat_1(A_318,'#skF_6') = '#skF_6'
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_3057,c_2339])).

tff(c_3075,plain,(
    ! [A_320] :
      ( k1_funct_1('#skF_7','#skF_3'(A_320,'#skF_6','#skF_6')) = k1_funct_1('#skF_6','#skF_3'(A_320,'#skF_6','#skF_6'))
      | k8_relat_1(A_320,'#skF_6') = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_3069])).

tff(c_86,plain,(
    ! [D_35] :
      ( k8_relat_1('#skF_5','#skF_7') = '#skF_6'
      | r2_hidden(k1_funct_1('#skF_7',D_35),'#skF_5')
      | ~ r2_hidden(D_35,k1_relat_1('#skF_6')) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2325,plain,(
    ! [D_35] :
      ( r2_hidden(k1_funct_1('#skF_7',D_35),'#skF_5')
      | ~ r2_hidden(D_35,k1_relat_1('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2323,c_86])).

tff(c_3148,plain,(
    ! [A_324] :
      ( r2_hidden(k1_funct_1('#skF_6','#skF_3'(A_324,'#skF_6','#skF_6')),'#skF_5')
      | ~ r2_hidden('#skF_3'(A_324,'#skF_6','#skF_6'),k1_relat_1('#skF_6'))
      | k8_relat_1(A_324,'#skF_6') = '#skF_6' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3075,c_2325])).

tff(c_3155,plain,(
    ! [A_316] :
      ( r2_hidden('#skF_4'(A_316,'#skF_6','#skF_6'),'#skF_5')
      | ~ r2_hidden('#skF_3'(A_316,'#skF_6','#skF_6'),k1_relat_1('#skF_6'))
      | k8_relat_1(A_316,'#skF_6') = '#skF_6'
      | ~ v1_funct_1('#skF_6')
      | k8_relat_1(A_316,'#skF_6') = '#skF_6'
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3055,c_3148])).

tff(c_3165,plain,(
    ! [A_325] :
      ( r2_hidden('#skF_4'(A_325,'#skF_6','#skF_6'),'#skF_5')
      | ~ r2_hidden('#skF_3'(A_325,'#skF_6','#skF_6'),k1_relat_1('#skF_6'))
      | k8_relat_1(A_325,'#skF_6') = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_3155])).

tff(c_3169,plain,(
    ! [A_316] :
      ( r2_hidden('#skF_4'(A_316,'#skF_6','#skF_6'),'#skF_5')
      | ~ v1_funct_1('#skF_6')
      | k8_relat_1(A_316,'#skF_6') = '#skF_6'
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_3056,c_3165])).

tff(c_3186,plain,(
    ! [A_316] :
      ( r2_hidden('#skF_4'(A_316,'#skF_6','#skF_6'),'#skF_5')
      | k8_relat_1(A_316,'#skF_6') = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_3169])).

tff(c_12,plain,(
    ! [A_1,B_2,C_12] :
      ( r2_hidden('#skF_2'(A_1,B_2,C_12),A_1)
      | r2_hidden(k4_tarski('#skF_3'(A_1,B_2,C_12),'#skF_4'(A_1,B_2,C_12)),C_12)
      | k8_relat_1(A_1,B_2) = C_12
      | ~ v1_relat_1(C_12)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3197,plain,(
    ! [A_327,B_328,C_329] :
      ( r2_hidden('#skF_2'(A_327,B_328,C_329),A_327)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_327,B_328,C_329),'#skF_4'(A_327,B_328,C_329)),B_328)
      | ~ r2_hidden('#skF_4'(A_327,B_328,C_329),A_327)
      | k8_relat_1(A_327,B_328) = C_329
      | ~ v1_relat_1(C_329)
      | ~ v1_relat_1(B_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3229,plain,(
    ! [A_330,C_331] :
      ( ~ r2_hidden('#skF_4'(A_330,C_331,C_331),A_330)
      | r2_hidden('#skF_2'(A_330,C_331,C_331),A_330)
      | k8_relat_1(A_330,C_331) = C_331
      | ~ v1_relat_1(C_331) ) ),
    inference(resolution,[status(thm)],[c_12,c_3197])).

tff(c_3233,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_6','#skF_6'),'#skF_5')
    | ~ v1_relat_1('#skF_6')
    | k8_relat_1('#skF_5','#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3186,c_3229])).

tff(c_3244,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_6','#skF_6'),'#skF_5')
    | k8_relat_1('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3233])).

tff(c_3247,plain,(
    k8_relat_1('#skF_5','#skF_6') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_3244])).

tff(c_2409,plain,(
    ! [A_262,B_263,C_264] :
      ( r2_hidden('#skF_2'(A_262,B_263,C_264),A_262)
      | r2_hidden(k4_tarski('#skF_3'(A_262,B_263,C_264),'#skF_4'(A_262,B_263,C_264)),C_264)
      | k8_relat_1(A_262,B_263) = C_264
      | ~ v1_relat_1(C_264)
      | ~ v1_relat_1(B_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [D_17,E_18,B_2,A_1] :
      ( r2_hidden(k4_tarski(D_17,E_18),B_2)
      | ~ r2_hidden(k4_tarski(D_17,E_18),k8_relat_1(A_1,B_2))
      | ~ v1_relat_1(k8_relat_1(A_1,B_2))
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5815,plain,(
    ! [A_461,B_462,A_463,B_464] :
      ( r2_hidden(k4_tarski('#skF_3'(A_461,B_462,k8_relat_1(A_463,B_464)),'#skF_4'(A_461,B_462,k8_relat_1(A_463,B_464))),B_464)
      | ~ v1_relat_1(B_464)
      | r2_hidden('#skF_2'(A_461,B_462,k8_relat_1(A_463,B_464)),A_461)
      | k8_relat_1(A_463,B_464) = k8_relat_1(A_461,B_462)
      | ~ v1_relat_1(k8_relat_1(A_463,B_464))
      | ~ v1_relat_1(B_462) ) ),
    inference(resolution,[status(thm)],[c_2409,c_16])).

tff(c_5877,plain,(
    ! [A_461,B_462] :
      ( r2_hidden(k4_tarski('#skF_3'(A_461,B_462,'#skF_6'),'#skF_4'(A_461,B_462,k8_relat_1('#skF_5','#skF_6'))),'#skF_6')
      | ~ v1_relat_1('#skF_6')
      | r2_hidden('#skF_2'(A_461,B_462,k8_relat_1('#skF_5','#skF_6')),A_461)
      | k8_relat_1(A_461,B_462) = k8_relat_1('#skF_5','#skF_6')
      | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6'))
      | ~ v1_relat_1(B_462) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3247,c_5815])).

tff(c_6297,plain,(
    ! [A_474,B_475] :
      ( r2_hidden(k4_tarski('#skF_3'(A_474,B_475,'#skF_6'),'#skF_4'(A_474,B_475,'#skF_6')),'#skF_6')
      | r2_hidden('#skF_2'(A_474,B_475,'#skF_6'),A_474)
      | k8_relat_1(A_474,B_475) = '#skF_6'
      | ~ v1_relat_1(B_475) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3247,c_3247,c_3247,c_32,c_3247,c_5877])).

tff(c_6323,plain,(
    ! [A_474,B_475] :
      ( k1_funct_1('#skF_6','#skF_3'(A_474,B_475,'#skF_6')) = '#skF_4'(A_474,B_475,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | r2_hidden('#skF_2'(A_474,B_475,'#skF_6'),A_474)
      | k8_relat_1(A_474,B_475) = '#skF_6'
      | ~ v1_relat_1(B_475) ) ),
    inference(resolution,[status(thm)],[c_6297,c_22])).

tff(c_6348,plain,(
    ! [A_474,B_475] :
      ( k1_funct_1('#skF_6','#skF_3'(A_474,B_475,'#skF_6')) = '#skF_4'(A_474,B_475,'#skF_6')
      | r2_hidden('#skF_2'(A_474,B_475,'#skF_6'),A_474)
      | k8_relat_1(A_474,B_475) = '#skF_6'
      | ~ v1_relat_1(B_475) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_6323])).

tff(c_2663,plain,(
    ! [A_292,B_293,C_294] :
      ( r2_hidden(k4_tarski('#skF_1'(A_292,B_293,C_294),'#skF_2'(A_292,B_293,C_294)),B_293)
      | r2_hidden(k4_tarski('#skF_3'(A_292,B_293,C_294),'#skF_4'(A_292,B_293,C_294)),C_294)
      | k8_relat_1(A_292,B_293) = C_294
      | ~ v1_relat_1(C_294)
      | ~ v1_relat_1(B_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_7019,plain,(
    ! [A_513,B_514,A_515,B_516] :
      ( r2_hidden(k4_tarski('#skF_3'(A_513,B_514,k8_relat_1(A_515,B_516)),'#skF_4'(A_513,B_514,k8_relat_1(A_515,B_516))),B_516)
      | ~ v1_relat_1(B_516)
      | r2_hidden(k4_tarski('#skF_1'(A_513,B_514,k8_relat_1(A_515,B_516)),'#skF_2'(A_513,B_514,k8_relat_1(A_515,B_516))),B_514)
      | k8_relat_1(A_515,B_516) = k8_relat_1(A_513,B_514)
      | ~ v1_relat_1(k8_relat_1(A_515,B_516))
      | ~ v1_relat_1(B_514) ) ),
    inference(resolution,[status(thm)],[c_2663,c_16])).

tff(c_7134,plain,(
    ! [A_513,B_514] :
      ( r2_hidden(k4_tarski('#skF_3'(A_513,B_514,k8_relat_1('#skF_5','#skF_6')),'#skF_4'(A_513,B_514,k8_relat_1('#skF_5','#skF_6'))),'#skF_6')
      | ~ v1_relat_1('#skF_6')
      | r2_hidden(k4_tarski('#skF_1'(A_513,B_514,k8_relat_1('#skF_5','#skF_6')),'#skF_2'(A_513,B_514,'#skF_6')),B_514)
      | k8_relat_1(A_513,B_514) = k8_relat_1('#skF_5','#skF_6')
      | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6'))
      | ~ v1_relat_1(B_514) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3247,c_7019])).

tff(c_7625,plain,(
    ! [A_534,B_535] :
      ( r2_hidden(k4_tarski('#skF_3'(A_534,B_535,'#skF_6'),'#skF_4'(A_534,B_535,'#skF_6')),'#skF_6')
      | r2_hidden(k4_tarski('#skF_1'(A_534,B_535,'#skF_6'),'#skF_2'(A_534,B_535,'#skF_6')),B_535)
      | k8_relat_1(A_534,B_535) = '#skF_6'
      | ~ v1_relat_1(B_535) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3247,c_3247,c_3247,c_32,c_3247,c_3247,c_7134])).

tff(c_7694,plain,(
    ! [A_536,B_537] :
      ( r2_hidden('#skF_1'(A_536,B_537,'#skF_6'),k1_relat_1(B_537))
      | ~ v1_funct_1(B_537)
      | r2_hidden(k4_tarski('#skF_3'(A_536,B_537,'#skF_6'),'#skF_4'(A_536,B_537,'#skF_6')),'#skF_6')
      | k8_relat_1(A_536,B_537) = '#skF_6'
      | ~ v1_relat_1(B_537) ) ),
    inference(resolution,[status(thm)],[c_7625,c_24])).

tff(c_7720,plain,(
    ! [A_536,B_537] :
      ( k1_funct_1('#skF_6','#skF_3'(A_536,B_537,'#skF_6')) = '#skF_4'(A_536,B_537,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | r2_hidden('#skF_1'(A_536,B_537,'#skF_6'),k1_relat_1(B_537))
      | ~ v1_funct_1(B_537)
      | k8_relat_1(A_536,B_537) = '#skF_6'
      | ~ v1_relat_1(B_537) ) ),
    inference(resolution,[status(thm)],[c_7694,c_22])).

tff(c_7745,plain,(
    ! [A_536,B_537] :
      ( k1_funct_1('#skF_6','#skF_3'(A_536,B_537,'#skF_6')) = '#skF_4'(A_536,B_537,'#skF_6')
      | r2_hidden('#skF_1'(A_536,B_537,'#skF_6'),k1_relat_1(B_537))
      | ~ v1_funct_1(B_537)
      | k8_relat_1(A_536,B_537) = '#skF_6'
      | ~ v1_relat_1(B_537) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_7720])).

tff(c_8146,plain,(
    ! [B_554,A_555] :
      ( k1_funct_1(B_554,'#skF_1'(A_555,B_554,'#skF_6')) = '#skF_2'(A_555,B_554,'#skF_6')
      | ~ v1_funct_1(B_554)
      | r2_hidden(k4_tarski('#skF_3'(A_555,B_554,'#skF_6'),'#skF_4'(A_555,B_554,'#skF_6')),'#skF_6')
      | k8_relat_1(A_555,B_554) = '#skF_6'
      | ~ v1_relat_1(B_554) ) ),
    inference(resolution,[status(thm)],[c_7625,c_22])).

tff(c_8176,plain,(
    ! [A_555,B_554] :
      ( k1_funct_1('#skF_6','#skF_3'(A_555,B_554,'#skF_6')) = '#skF_4'(A_555,B_554,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | k1_funct_1(B_554,'#skF_1'(A_555,B_554,'#skF_6')) = '#skF_2'(A_555,B_554,'#skF_6')
      | ~ v1_funct_1(B_554)
      | k8_relat_1(A_555,B_554) = '#skF_6'
      | ~ v1_relat_1(B_554) ) ),
    inference(resolution,[status(thm)],[c_8146,c_22])).

tff(c_8297,plain,(
    ! [A_558,B_559] :
      ( k1_funct_1('#skF_6','#skF_3'(A_558,B_559,'#skF_6')) = '#skF_4'(A_558,B_559,'#skF_6')
      | k1_funct_1(B_559,'#skF_1'(A_558,B_559,'#skF_6')) = '#skF_2'(A_558,B_559,'#skF_6')
      | ~ v1_funct_1(B_559)
      | k8_relat_1(A_558,B_559) = '#skF_6'
      | ~ v1_relat_1(B_559) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_8176])).

tff(c_138,plain,(
    ! [D_35] :
      ( k8_relat_1('#skF_5','#skF_7') = '#skF_6'
      | r2_hidden(D_35,k1_relat_1('#skF_6'))
      | ~ r2_hidden(k1_funct_1('#skF_7',D_35),'#skF_5')
      | ~ r2_hidden(D_35,k1_relat_1('#skF_7')) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2356,plain,(
    ! [D_35] :
      ( r2_hidden(D_35,k1_relat_1('#skF_6'))
      | ~ r2_hidden(k1_funct_1('#skF_7',D_35),'#skF_5')
      | ~ r2_hidden(D_35,k1_relat_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2323,c_138])).

tff(c_8391,plain,(
    ! [A_558] :
      ( r2_hidden('#skF_1'(A_558,'#skF_7','#skF_6'),k1_relat_1('#skF_6'))
      | ~ r2_hidden('#skF_2'(A_558,'#skF_7','#skF_6'),'#skF_5')
      | ~ r2_hidden('#skF_1'(A_558,'#skF_7','#skF_6'),k1_relat_1('#skF_7'))
      | k1_funct_1('#skF_6','#skF_3'(A_558,'#skF_7','#skF_6')) = '#skF_4'(A_558,'#skF_7','#skF_6')
      | ~ v1_funct_1('#skF_7')
      | k8_relat_1(A_558,'#skF_7') = '#skF_6'
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8297,c_2356])).

tff(c_11120,plain,(
    ! [A_654] :
      ( r2_hidden('#skF_1'(A_654,'#skF_7','#skF_6'),k1_relat_1('#skF_6'))
      | ~ r2_hidden('#skF_2'(A_654,'#skF_7','#skF_6'),'#skF_5')
      | ~ r2_hidden('#skF_1'(A_654,'#skF_7','#skF_6'),k1_relat_1('#skF_7'))
      | k1_funct_1('#skF_6','#skF_3'(A_654,'#skF_7','#skF_6')) = '#skF_4'(A_654,'#skF_7','#skF_6')
      | k8_relat_1(A_654,'#skF_7') = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_8391])).

tff(c_11124,plain,(
    ! [A_536] :
      ( r2_hidden('#skF_1'(A_536,'#skF_7','#skF_6'),k1_relat_1('#skF_6'))
      | ~ r2_hidden('#skF_2'(A_536,'#skF_7','#skF_6'),'#skF_5')
      | k1_funct_1('#skF_6','#skF_3'(A_536,'#skF_7','#skF_6')) = '#skF_4'(A_536,'#skF_7','#skF_6')
      | ~ v1_funct_1('#skF_7')
      | k8_relat_1(A_536,'#skF_7') = '#skF_6'
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_7745,c_11120])).

tff(c_11160,plain,(
    ! [A_655] :
      ( r2_hidden('#skF_1'(A_655,'#skF_7','#skF_6'),k1_relat_1('#skF_6'))
      | ~ r2_hidden('#skF_2'(A_655,'#skF_7','#skF_6'),'#skF_5')
      | k1_funct_1('#skF_6','#skF_3'(A_655,'#skF_7','#skF_6')) = '#skF_4'(A_655,'#skF_7','#skF_6')
      | k8_relat_1(A_655,'#skF_7') = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_11124])).

tff(c_11181,plain,(
    ! [A_656] :
      ( k1_funct_1('#skF_7','#skF_1'(A_656,'#skF_7','#skF_6')) = k1_funct_1('#skF_6','#skF_1'(A_656,'#skF_7','#skF_6'))
      | ~ r2_hidden('#skF_2'(A_656,'#skF_7','#skF_6'),'#skF_5')
      | k1_funct_1('#skF_6','#skF_3'(A_656,'#skF_7','#skF_6')) = '#skF_4'(A_656,'#skF_7','#skF_6')
      | k8_relat_1(A_656,'#skF_7') = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_11160,c_2339])).

tff(c_11185,plain,
    ( k1_funct_1('#skF_7','#skF_1'('#skF_5','#skF_7','#skF_6')) = k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_7','#skF_6'))
    | k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_7','#skF_6')) = '#skF_4'('#skF_5','#skF_7','#skF_6')
    | k8_relat_1('#skF_5','#skF_7') = '#skF_6'
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_6348,c_11181])).

tff(c_11202,plain,
    ( k1_funct_1('#skF_7','#skF_1'('#skF_5','#skF_7','#skF_6')) = k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_7','#skF_6'))
    | k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_7','#skF_6')) = '#skF_4'('#skF_5','#skF_7','#skF_6')
    | k8_relat_1('#skF_5','#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_11185])).

tff(c_11203,plain,
    ( k1_funct_1('#skF_7','#skF_1'('#skF_5','#skF_7','#skF_6')) = k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_7','#skF_6'))
    | k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_7','#skF_6')) = '#skF_4'('#skF_5','#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_2323,c_11202])).

tff(c_11212,plain,(
    k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_7','#skF_6')) = '#skF_4'('#skF_5','#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_11203])).

tff(c_2362,plain,(
    ! [E_243,A_244,D_245,B_246] :
      ( r2_hidden(E_243,A_244)
      | ~ r2_hidden(k4_tarski(D_245,E_243),k8_relat_1(A_244,B_246))
      | ~ v1_relat_1(k8_relat_1(A_244,B_246))
      | ~ v1_relat_1(B_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2367,plain,(
    ! [A_244,B_246,A_19] :
      ( r2_hidden(k1_funct_1(k8_relat_1(A_244,B_246),A_19),A_244)
      | ~ v1_relat_1(B_246)
      | ~ r2_hidden(A_19,k1_relat_1(k8_relat_1(A_244,B_246)))
      | ~ v1_funct_1(k8_relat_1(A_244,B_246))
      | ~ v1_relat_1(k8_relat_1(A_244,B_246)) ) ),
    inference(resolution,[status(thm)],[c_20,c_2362])).

tff(c_3263,plain,(
    ! [A_19] :
      ( r2_hidden(k1_funct_1('#skF_6',A_19),'#skF_5')
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(A_19,k1_relat_1(k8_relat_1('#skF_5','#skF_6')))
      | ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6'))
      | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3247,c_2367])).

tff(c_3284,plain,(
    ! [A_19] :
      ( r2_hidden(k1_funct_1('#skF_6',A_19),'#skF_5')
      | ~ r2_hidden(A_19,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3247,c_30,c_3247,c_3247,c_32,c_3263])).

tff(c_11227,plain,
    ( r2_hidden('#skF_4'('#skF_5','#skF_7','#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_3'('#skF_5','#skF_7','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11212,c_3284])).

tff(c_11584,plain,(
    ~ r2_hidden('#skF_3'('#skF_5','#skF_7','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_11227])).

tff(c_2435,plain,(
    ! [A_262,B_263,C_264] :
      ( r2_hidden('#skF_3'(A_262,B_263,C_264),k1_relat_1(C_264))
      | ~ v1_funct_1(C_264)
      | r2_hidden('#skF_2'(A_262,B_263,C_264),A_262)
      | k8_relat_1(A_262,B_263) = C_264
      | ~ v1_relat_1(C_264)
      | ~ v1_relat_1(B_263) ) ),
    inference(resolution,[status(thm)],[c_2409,c_24])).

tff(c_11597,plain,
    ( ~ v1_funct_1('#skF_6')
    | r2_hidden('#skF_2'('#skF_5','#skF_7','#skF_6'),'#skF_5')
    | k8_relat_1('#skF_5','#skF_7') = '#skF_6'
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_2435,c_11584])).

tff(c_11612,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_7','#skF_6'),'#skF_5')
    | k8_relat_1('#skF_5','#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_30,c_11597])).

tff(c_11613,plain,(
    r2_hidden('#skF_2'('#skF_5','#skF_7','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_2323,c_11612])).

tff(c_7723,plain,(
    ! [A_536,B_537] :
      ( r2_hidden('#skF_3'(A_536,B_537,'#skF_6'),k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | r2_hidden('#skF_1'(A_536,B_537,'#skF_6'),k1_relat_1(B_537))
      | ~ v1_funct_1(B_537)
      | k8_relat_1(A_536,B_537) = '#skF_6'
      | ~ v1_relat_1(B_537) ) ),
    inference(resolution,[status(thm)],[c_7694,c_24])).

tff(c_7748,plain,(
    ! [A_536,B_537] :
      ( r2_hidden('#skF_3'(A_536,B_537,'#skF_6'),k1_relat_1('#skF_6'))
      | r2_hidden('#skF_1'(A_536,B_537,'#skF_6'),k1_relat_1(B_537))
      | ~ v1_funct_1(B_537)
      | k8_relat_1(A_536,B_537) = '#skF_6'
      | ~ v1_relat_1(B_537) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_7723])).

tff(c_2830,plain,(
    ! [A_303,B_304,C_305] :
      ( r2_hidden('#skF_3'(A_303,B_304,C_305),k1_relat_1(C_305))
      | ~ v1_funct_1(C_305)
      | r2_hidden(k4_tarski('#skF_1'(A_303,B_304,C_305),'#skF_2'(A_303,B_304,C_305)),B_304)
      | k8_relat_1(A_303,B_304) = C_305
      | ~ v1_relat_1(C_305)
      | ~ v1_relat_1(B_304) ) ),
    inference(resolution,[status(thm)],[c_2663,c_24])).

tff(c_2868,plain,(
    ! [B_304,A_303,C_305] :
      ( k1_funct_1(B_304,'#skF_1'(A_303,B_304,C_305)) = '#skF_2'(A_303,B_304,C_305)
      | ~ v1_funct_1(B_304)
      | r2_hidden('#skF_3'(A_303,B_304,C_305),k1_relat_1(C_305))
      | ~ v1_funct_1(C_305)
      | k8_relat_1(A_303,B_304) = C_305
      | ~ v1_relat_1(C_305)
      | ~ v1_relat_1(B_304) ) ),
    inference(resolution,[status(thm)],[c_2830,c_22])).

tff(c_11593,plain,
    ( k1_funct_1('#skF_7','#skF_1'('#skF_5','#skF_7','#skF_6')) = '#skF_2'('#skF_5','#skF_7','#skF_6')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_6')
    | k8_relat_1('#skF_5','#skF_7') = '#skF_6'
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_2868,c_11584])).

tff(c_11608,plain,
    ( k1_funct_1('#skF_7','#skF_1'('#skF_5','#skF_7','#skF_6')) = '#skF_2'('#skF_5','#skF_7','#skF_6')
    | k8_relat_1('#skF_5','#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_30,c_26,c_11593])).

tff(c_11609,plain,(
    k1_funct_1('#skF_7','#skF_1'('#skF_5','#skF_7','#skF_6')) = '#skF_2'('#skF_5','#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_2323,c_11608])).

tff(c_11648,plain,
    ( r2_hidden('#skF_1'('#skF_5','#skF_7','#skF_6'),k1_relat_1('#skF_6'))
    | ~ r2_hidden('#skF_2'('#skF_5','#skF_7','#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_5','#skF_7','#skF_6'),k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11609,c_2356])).

tff(c_11686,plain,
    ( r2_hidden('#skF_1'('#skF_5','#skF_7','#skF_6'),k1_relat_1('#skF_6'))
    | ~ r2_hidden('#skF_1'('#skF_5','#skF_7','#skF_6'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11613,c_11648])).

tff(c_11704,plain,(
    ~ r2_hidden('#skF_1'('#skF_5','#skF_7','#skF_6'),k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_11686])).

tff(c_11710,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_7','#skF_6'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_7')
    | k8_relat_1('#skF_5','#skF_7') = '#skF_6'
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_7748,c_11704])).

tff(c_11729,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_7','#skF_6'),k1_relat_1('#skF_6'))
    | k8_relat_1('#skF_5','#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_11710])).

tff(c_11731,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2323,c_11584,c_11729])).

tff(c_11732,plain,(
    r2_hidden('#skF_1'('#skF_5','#skF_7','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_11686])).

tff(c_11748,plain,(
    k1_funct_1('#skF_7','#skF_1'('#skF_5','#skF_7','#skF_6')) = k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_11732,c_2339])).

tff(c_11762,plain,(
    k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_7','#skF_6')) = '#skF_2'('#skF_5','#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11609,c_11748])).

tff(c_2369,plain,(
    ! [D_247,E_248,B_249,A_250] :
      ( r2_hidden(k4_tarski(D_247,E_248),B_249)
      | ~ r2_hidden(k4_tarski(D_247,E_248),k8_relat_1(A_250,B_249))
      | ~ v1_relat_1(k8_relat_1(A_250,B_249))
      | ~ v1_relat_1(B_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2374,plain,(
    ! [A_19,A_250,B_249] :
      ( r2_hidden(k4_tarski(A_19,k1_funct_1(k8_relat_1(A_250,B_249),A_19)),B_249)
      | ~ v1_relat_1(B_249)
      | ~ r2_hidden(A_19,k1_relat_1(k8_relat_1(A_250,B_249)))
      | ~ v1_funct_1(k8_relat_1(A_250,B_249))
      | ~ v1_relat_1(k8_relat_1(A_250,B_249)) ) ),
    inference(resolution,[status(thm)],[c_20,c_2369])).

tff(c_3260,plain,(
    ! [A_19] :
      ( r2_hidden(k4_tarski(A_19,k1_funct_1('#skF_6',A_19)),'#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(A_19,k1_relat_1(k8_relat_1('#skF_5','#skF_6')))
      | ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6'))
      | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3247,c_2374])).

tff(c_3282,plain,(
    ! [A_19] :
      ( r2_hidden(k4_tarski(A_19,k1_funct_1('#skF_6',A_19)),'#skF_6')
      | ~ r2_hidden(A_19,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3247,c_30,c_3247,c_3247,c_32,c_3260])).

tff(c_11929,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_5','#skF_7','#skF_6'),'#skF_2'('#skF_5','#skF_7','#skF_6')),'#skF_6')
    | ~ r2_hidden('#skF_1'('#skF_5','#skF_7','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11762,c_3282])).

tff(c_11946,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_5','#skF_7','#skF_6'),'#skF_2'('#skF_5','#skF_7','#skF_6')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11732,c_11929])).

tff(c_14,plain,(
    ! [D_17,E_18,A_1,B_2] :
      ( r2_hidden(k4_tarski(D_17,E_18),k8_relat_1(A_1,B_2))
      | ~ r2_hidden(k4_tarski(D_17,E_18),B_2)
      | ~ r2_hidden(E_18,A_1)
      | ~ v1_relat_1(k8_relat_1(A_1,B_2))
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8951,plain,(
    ! [A_587,B_588,A_589,B_590] :
      ( r2_hidden(k4_tarski('#skF_3'(A_587,B_588,k8_relat_1(A_589,B_590)),'#skF_4'(A_587,B_588,k8_relat_1(A_589,B_590))),k8_relat_1(A_589,B_590))
      | k8_relat_1(A_589,B_590) = k8_relat_1(A_587,B_588)
      | ~ v1_relat_1(B_588)
      | ~ r2_hidden(k4_tarski('#skF_1'(A_587,B_588,k8_relat_1(A_589,B_590)),'#skF_2'(A_587,B_588,k8_relat_1(A_589,B_590))),B_590)
      | ~ r2_hidden('#skF_2'(A_587,B_588,k8_relat_1(A_589,B_590)),A_589)
      | ~ v1_relat_1(k8_relat_1(A_589,B_590))
      | ~ v1_relat_1(B_590) ) ),
    inference(resolution,[status(thm)],[c_14,c_2991])).

tff(c_9012,plain,(
    ! [A_587,B_588] :
      ( r2_hidden(k4_tarski('#skF_3'(A_587,B_588,k8_relat_1('#skF_5','#skF_6')),'#skF_4'(A_587,B_588,k8_relat_1('#skF_5','#skF_6'))),'#skF_6')
      | k8_relat_1(A_587,B_588) = k8_relat_1('#skF_5','#skF_6')
      | ~ v1_relat_1(B_588)
      | ~ r2_hidden(k4_tarski('#skF_1'(A_587,B_588,k8_relat_1('#skF_5','#skF_6')),'#skF_2'(A_587,B_588,k8_relat_1('#skF_5','#skF_6'))),'#skF_6')
      | ~ r2_hidden('#skF_2'(A_587,B_588,k8_relat_1('#skF_5','#skF_6')),'#skF_5')
      | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3247,c_8951])).

tff(c_9031,plain,(
    ! [A_587,B_588] :
      ( r2_hidden(k4_tarski('#skF_3'(A_587,B_588,'#skF_6'),'#skF_4'(A_587,B_588,'#skF_6')),'#skF_6')
      | k8_relat_1(A_587,B_588) = '#skF_6'
      | ~ v1_relat_1(B_588)
      | ~ r2_hidden(k4_tarski('#skF_1'(A_587,B_588,'#skF_6'),'#skF_2'(A_587,B_588,'#skF_6')),'#skF_6')
      | ~ r2_hidden('#skF_2'(A_587,B_588,'#skF_6'),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32,c_3247,c_3247,c_3247,c_3247,c_3247,c_3247,c_3247,c_9012])).

tff(c_11960,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_5','#skF_7','#skF_6'),'#skF_4'('#skF_5','#skF_7','#skF_6')),'#skF_6')
    | k8_relat_1('#skF_5','#skF_7') = '#skF_6'
    | ~ v1_relat_1('#skF_7')
    | ~ r2_hidden('#skF_2'('#skF_5','#skF_7','#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_11946,c_9031])).

tff(c_11983,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_5','#skF_7','#skF_6'),'#skF_4'('#skF_5','#skF_7','#skF_6')),'#skF_6')
    | k8_relat_1('#skF_5','#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11613,c_28,c_11960])).

tff(c_11984,plain,(
    r2_hidden(k4_tarski('#skF_3'('#skF_5','#skF_7','#skF_6'),'#skF_4'('#skF_5','#skF_7','#skF_6')),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_2323,c_11983])).

tff(c_12023,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_7','#skF_6'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_11984,c_24])).

tff(c_12038,plain,(
    r2_hidden('#skF_3'('#skF_5','#skF_7','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_12023])).

tff(c_12040,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11584,c_12038])).

tff(c_12041,plain,(
    r2_hidden('#skF_4'('#skF_5','#skF_7','#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_11227])).

tff(c_12042,plain,(
    r2_hidden('#skF_3'('#skF_5','#skF_7','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_11227])).

tff(c_2322,plain,(
    ! [D_35] :
      ( r2_hidden(D_35,k1_relat_1('#skF_7'))
      | ~ r2_hidden(D_35,k1_relat_1('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_12055,plain,(
    k1_funct_1('#skF_7','#skF_3'('#skF_5','#skF_7','#skF_6')) = k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_12042,c_2339])).

tff(c_12059,plain,(
    k1_funct_1('#skF_7','#skF_3'('#skF_5','#skF_7','#skF_6')) = '#skF_4'('#skF_5','#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11212,c_12055])).

tff(c_12073,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_5','#skF_7','#skF_6'),'#skF_4'('#skF_5','#skF_7','#skF_6')),'#skF_7')
    | ~ r2_hidden('#skF_3'('#skF_5','#skF_7','#skF_6'),k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_12059,c_20])).

tff(c_12087,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_5','#skF_7','#skF_6'),'#skF_4'('#skF_5','#skF_7','#skF_6')),'#skF_7')
    | ~ r2_hidden('#skF_3'('#skF_5','#skF_7','#skF_6'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_12073])).

tff(c_12608,plain,(
    ~ r2_hidden('#skF_3'('#skF_5','#skF_7','#skF_6'),k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_12087])).

tff(c_12611,plain,(
    ~ r2_hidden('#skF_3'('#skF_5','#skF_7','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_2322,c_12608])).

tff(c_12615,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12042,c_12611])).

tff(c_12616,plain,(
    r2_hidden(k4_tarski('#skF_3'('#skF_5','#skF_7','#skF_6'),'#skF_4'('#skF_5','#skF_7','#skF_6')),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_12087])).

tff(c_3521,plain,(
    ! [A_345,B_346,C_347] :
      ( r2_hidden(k4_tarski('#skF_1'(A_345,B_346,C_347),'#skF_2'(A_345,B_346,C_347)),B_346)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_345,B_346,C_347),'#skF_4'(A_345,B_346,C_347)),B_346)
      | ~ r2_hidden('#skF_4'(A_345,B_346,C_347),A_345)
      | k8_relat_1(A_345,B_346) = C_347
      | ~ v1_relat_1(C_347)
      | ~ v1_relat_1(B_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3572,plain,(
    ! [A_345,B_346,C_347] :
      ( r2_hidden('#skF_1'(A_345,B_346,C_347),k1_relat_1(B_346))
      | ~ v1_funct_1(B_346)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_345,B_346,C_347),'#skF_4'(A_345,B_346,C_347)),B_346)
      | ~ r2_hidden('#skF_4'(A_345,B_346,C_347),A_345)
      | k8_relat_1(A_345,B_346) = C_347
      | ~ v1_relat_1(C_347)
      | ~ v1_relat_1(B_346) ) ),
    inference(resolution,[status(thm)],[c_3521,c_24])).

tff(c_12634,plain,
    ( r2_hidden('#skF_1'('#skF_5','#skF_7','#skF_6'),k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ r2_hidden('#skF_4'('#skF_5','#skF_7','#skF_6'),'#skF_5')
    | k8_relat_1('#skF_5','#skF_7') = '#skF_6'
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_12616,c_3572])).

tff(c_12656,plain,
    ( r2_hidden('#skF_1'('#skF_5','#skF_7','#skF_6'),k1_relat_1('#skF_7'))
    | k8_relat_1('#skF_5','#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_12041,c_26,c_12634])).

tff(c_12657,plain,(
    r2_hidden('#skF_1'('#skF_5','#skF_7','#skF_6'),k1_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_2323,c_12656])).

tff(c_6,plain,(
    ! [A_1,B_2,C_12] :
      ( r2_hidden('#skF_2'(A_1,B_2,C_12),A_1)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_1,B_2,C_12),'#skF_4'(A_1,B_2,C_12)),B_2)
      | ~ r2_hidden('#skF_4'(A_1,B_2,C_12),A_1)
      | k8_relat_1(A_1,B_2) = C_12
      | ~ v1_relat_1(C_12)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12637,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_7','#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_4'('#skF_5','#skF_7','#skF_6'),'#skF_5')
    | k8_relat_1('#skF_5','#skF_7') = '#skF_6'
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_12616,c_6])).

tff(c_12660,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_7','#skF_6'),'#skF_5')
    | k8_relat_1('#skF_5','#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_12041,c_12637])).

tff(c_12661,plain,(
    r2_hidden('#skF_2'('#skF_5','#skF_7','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_2323,c_12660])).

tff(c_3571,plain,(
    ! [B_346,A_345,C_347] :
      ( k1_funct_1(B_346,'#skF_1'(A_345,B_346,C_347)) = '#skF_2'(A_345,B_346,C_347)
      | ~ v1_funct_1(B_346)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_345,B_346,C_347),'#skF_4'(A_345,B_346,C_347)),B_346)
      | ~ r2_hidden('#skF_4'(A_345,B_346,C_347),A_345)
      | k8_relat_1(A_345,B_346) = C_347
      | ~ v1_relat_1(C_347)
      | ~ v1_relat_1(B_346) ) ),
    inference(resolution,[status(thm)],[c_3521,c_22])).

tff(c_12631,plain,
    ( k1_funct_1('#skF_7','#skF_1'('#skF_5','#skF_7','#skF_6')) = '#skF_2'('#skF_5','#skF_7','#skF_6')
    | ~ v1_funct_1('#skF_7')
    | ~ r2_hidden('#skF_4'('#skF_5','#skF_7','#skF_6'),'#skF_5')
    | k8_relat_1('#skF_5','#skF_7') = '#skF_6'
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_12616,c_3571])).

tff(c_12652,plain,
    ( k1_funct_1('#skF_7','#skF_1'('#skF_5','#skF_7','#skF_6')) = '#skF_2'('#skF_5','#skF_7','#skF_6')
    | k8_relat_1('#skF_5','#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_12041,c_26,c_12631])).

tff(c_12653,plain,(
    k1_funct_1('#skF_7','#skF_1'('#skF_5','#skF_7','#skF_6')) = '#skF_2'('#skF_5','#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_2323,c_12652])).

tff(c_12713,plain,
    ( r2_hidden('#skF_1'('#skF_5','#skF_7','#skF_6'),k1_relat_1('#skF_6'))
    | ~ r2_hidden('#skF_2'('#skF_5','#skF_7','#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_5','#skF_7','#skF_6'),k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12653,c_2356])).

tff(c_12751,plain,(
    r2_hidden('#skF_1'('#skF_5','#skF_7','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12657,c_12661,c_12713])).

tff(c_12850,plain,(
    k1_funct_1('#skF_7','#skF_1'('#skF_5','#skF_7','#skF_6')) = k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_12751,c_2339])).

tff(c_12864,plain,(
    k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_7','#skF_6')) = '#skF_2'('#skF_5','#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12653,c_12850])).

tff(c_12874,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_5','#skF_7','#skF_6'),'#skF_2'('#skF_5','#skF_7','#skF_6')),'#skF_6')
    | ~ r2_hidden('#skF_1'('#skF_5','#skF_7','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12864,c_3282])).

tff(c_12891,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_5','#skF_7','#skF_6'),'#skF_2'('#skF_5','#skF_7','#skF_6')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12751,c_12874])).

tff(c_2,plain,(
    ! [A_1,B_2,C_12] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_1,B_2,C_12),'#skF_2'(A_1,B_2,C_12)),C_12)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_1,B_2,C_12),'#skF_4'(A_1,B_2,C_12)),B_2)
      | ~ r2_hidden('#skF_4'(A_1,B_2,C_12),A_1)
      | k8_relat_1(A_1,B_2) = C_12
      | ~ v1_relat_1(C_12)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12936,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3'('#skF_5','#skF_7','#skF_6'),'#skF_4'('#skF_5','#skF_7','#skF_6')),'#skF_7')
    | ~ r2_hidden('#skF_4'('#skF_5','#skF_7','#skF_6'),'#skF_5')
    | k8_relat_1('#skF_5','#skF_7') = '#skF_6'
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_12891,c_2])).

tff(c_12961,plain,(
    k8_relat_1('#skF_5','#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_12041,c_12616,c_12936])).

tff(c_12963,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2323,c_12961])).

tff(c_12965,plain,(
    k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_7','#skF_6')) != '#skF_4'('#skF_5','#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_11203])).

tff(c_11146,plain,(
    ! [A_536] :
      ( r2_hidden('#skF_1'(A_536,'#skF_7','#skF_6'),k1_relat_1('#skF_6'))
      | ~ r2_hidden('#skF_2'(A_536,'#skF_7','#skF_6'),'#skF_5')
      | k1_funct_1('#skF_6','#skF_3'(A_536,'#skF_7','#skF_6')) = '#skF_4'(A_536,'#skF_7','#skF_6')
      | k8_relat_1(A_536,'#skF_7') = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_11124])).

tff(c_12964,plain,(
    k1_funct_1('#skF_7','#skF_1'('#skF_5','#skF_7','#skF_6')) = k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_7','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_11203])).

tff(c_8204,plain,(
    ! [A_555,B_554] :
      ( k1_funct_1('#skF_6','#skF_3'(A_555,B_554,'#skF_6')) = '#skF_4'(A_555,B_554,'#skF_6')
      | k1_funct_1(B_554,'#skF_1'(A_555,B_554,'#skF_6')) = '#skF_2'(A_555,B_554,'#skF_6')
      | ~ v1_funct_1(B_554)
      | k8_relat_1(A_555,B_554) = '#skF_6'
      | ~ v1_relat_1(B_554) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_8176])).

tff(c_12973,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_7','#skF_6')) = '#skF_4'('#skF_5','#skF_7','#skF_6')
    | k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_7','#skF_6')) = '#skF_2'('#skF_5','#skF_7','#skF_6')
    | ~ v1_funct_1('#skF_7')
    | k8_relat_1('#skF_5','#skF_7') = '#skF_6'
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_12964,c_8204])).

tff(c_13013,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_7','#skF_6')) = '#skF_4'('#skF_5','#skF_7','#skF_6')
    | k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_7','#skF_6')) = '#skF_2'('#skF_5','#skF_7','#skF_6')
    | k8_relat_1('#skF_5','#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_12973])).

tff(c_13014,plain,(
    k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_7','#skF_6')) = '#skF_2'('#skF_5','#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_2323,c_12965,c_13013])).

tff(c_13037,plain,(
    k1_funct_1('#skF_7','#skF_1'('#skF_5','#skF_7','#skF_6')) = '#skF_2'('#skF_5','#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13014,c_12964])).

tff(c_13244,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_7','#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_5','#skF_7','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13037,c_2325])).

tff(c_13291,plain,(
    ~ r2_hidden('#skF_1'('#skF_5','#skF_7','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_13244])).

tff(c_13294,plain,
    ( ~ r2_hidden('#skF_2'('#skF_5','#skF_7','#skF_6'),'#skF_5')
    | k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_7','#skF_6')) = '#skF_4'('#skF_5','#skF_7','#skF_6')
    | k8_relat_1('#skF_5','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_11146,c_13291])).

tff(c_13297,plain,(
    ~ r2_hidden('#skF_2'('#skF_5','#skF_7','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_2323,c_12965,c_13294])).

tff(c_13300,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_7','#skF_6')) = '#skF_4'('#skF_5','#skF_7','#skF_6')
    | k8_relat_1('#skF_5','#skF_7') = '#skF_6'
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_6348,c_13297])).

tff(c_13312,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_7','#skF_6')) = '#skF_4'('#skF_5','#skF_7','#skF_6')
    | k8_relat_1('#skF_5','#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_13300])).

tff(c_13314,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2323,c_12965,c_13312])).

tff(c_13315,plain,(
    r2_hidden('#skF_2'('#skF_5','#skF_7','#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_13244])).

tff(c_13316,plain,(
    r2_hidden('#skF_1'('#skF_5','#skF_7','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_13244])).

tff(c_13047,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_5','#skF_7','#skF_6'),'#skF_2'('#skF_5','#skF_7','#skF_6')),'#skF_6')
    | ~ r2_hidden('#skF_1'('#skF_5','#skF_7','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13014,c_3282])).

tff(c_13461,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_5','#skF_7','#skF_6'),'#skF_2'('#skF_5','#skF_7','#skF_6')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13316,c_13047])).

tff(c_13466,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_5','#skF_7','#skF_6'),'#skF_4'('#skF_5','#skF_7','#skF_6')),'#skF_6')
    | k8_relat_1('#skF_5','#skF_7') = '#skF_6'
    | ~ v1_relat_1('#skF_7')
    | ~ r2_hidden('#skF_2'('#skF_5','#skF_7','#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_13461,c_9031])).

tff(c_13488,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_5','#skF_7','#skF_6'),'#skF_4'('#skF_5','#skF_7','#skF_6')),'#skF_6')
    | k8_relat_1('#skF_5','#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13315,c_28,c_13466])).

tff(c_13489,plain,(
    r2_hidden(k4_tarski('#skF_3'('#skF_5','#skF_7','#skF_6'),'#skF_4'('#skF_5','#skF_7','#skF_6')),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_2323,c_13488])).

tff(c_13523,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_7','#skF_6')) = '#skF_4'('#skF_5','#skF_7','#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_13489,c_22])).

tff(c_13537,plain,(
    k1_funct_1('#skF_6','#skF_3'('#skF_5','#skF_7','#skF_6')) = '#skF_4'('#skF_5','#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_13523])).

tff(c_13539,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12965,c_13537])).

tff(c_13541,plain,(
    k8_relat_1('#skF_5','#skF_6') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_3244])).

tff(c_3013,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(k4_tarski('#skF_3'(A_1,B_2,B_2),'#skF_4'(A_1,B_2,B_2)),B_2)
      | k8_relat_1(A_1,B_2) = B_2
      | ~ v1_relat_1(B_2) ) ),
    inference(resolution,[status(thm)],[c_10,c_2991])).

tff(c_13956,plain,(
    ! [A_708,B_709,C_710] :
      ( r2_hidden(k4_tarski('#skF_1'(A_708,B_709,C_710),'#skF_2'(A_708,B_709,C_710)),B_709)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_708,B_709,C_710),'#skF_4'(A_708,B_709,C_710)),B_709)
      | ~ r2_hidden('#skF_4'(A_708,B_709,C_710),A_708)
      | k8_relat_1(A_708,B_709) = C_710
      | ~ v1_relat_1(C_710)
      | ~ v1_relat_1(B_709) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14005,plain,(
    ! [A_711,B_712] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(A_711,B_712,B_712),'#skF_4'(A_711,B_712,B_712)),B_712)
      | ~ r2_hidden('#skF_4'(A_711,B_712,B_712),A_711)
      | k8_relat_1(A_711,B_712) = B_712
      | ~ v1_relat_1(B_712) ) ),
    inference(resolution,[status(thm)],[c_13956,c_2])).

tff(c_14043,plain,(
    ! [A_713,B_714] :
      ( ~ r2_hidden('#skF_4'(A_713,B_714,B_714),A_713)
      | k8_relat_1(A_713,B_714) = B_714
      | ~ v1_relat_1(B_714) ) ),
    inference(resolution,[status(thm)],[c_3013,c_14005])).

tff(c_14051,plain,
    ( ~ v1_relat_1('#skF_6')
    | k8_relat_1('#skF_5','#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3186,c_14043])).

tff(c_14063,plain,(
    k8_relat_1('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_14051])).

tff(c_14065,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13541,c_14063])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:22:55 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.95/4.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.14/4.47  
% 13.14/4.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.14/4.47  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k8_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3
% 13.14/4.47  
% 13.14/4.47  %Foreground sorts:
% 13.14/4.47  
% 13.14/4.47  
% 13.14/4.47  %Background operators:
% 13.14/4.47  
% 13.14/4.47  
% 13.14/4.47  %Foreground operators:
% 13.14/4.47  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 13.14/4.47  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 13.14/4.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.14/4.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.14/4.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.14/4.47  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 13.14/4.47  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 13.14/4.47  tff('#skF_7', type, '#skF_7': $i).
% 13.14/4.47  tff('#skF_10', type, '#skF_10': $i).
% 13.14/4.47  tff('#skF_5', type, '#skF_5': $i).
% 13.14/4.47  tff('#skF_6', type, '#skF_6': $i).
% 13.14/4.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 13.14/4.47  tff('#skF_9', type, '#skF_9': $i).
% 13.14/4.47  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 13.14/4.47  tff('#skF_8', type, '#skF_8': $i).
% 13.14/4.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.14/4.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.14/4.47  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 13.14/4.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.14/4.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.14/4.47  
% 13.60/4.52  tff(f_73, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((B = k8_relat_1(A, C)) <=> ((![D]: (r2_hidden(D, k1_relat_1(B)) <=> (r2_hidden(D, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, D), A)))) & (![D]: (r2_hidden(D, k1_relat_1(B)) => (k1_funct_1(B, D) = k1_funct_1(C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_funct_1)).
% 13.60/4.52  tff(f_49, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 13.60/4.52  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k8_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (r2_hidden(E, A) & r2_hidden(k4_tarski(D, E), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_relat_1)).
% 13.60/4.52  tff(c_112, plain, (![D_35]: (k8_relat_1('#skF_5', '#skF_7')='#skF_6' | r2_hidden(D_35, k1_relat_1('#skF_7')) | ~r2_hidden(D_35, k1_relat_1('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.60/4.52  tff(c_163, plain, (k8_relat_1('#skF_5', '#skF_7')='#skF_6'), inference(splitLeft, [status(thm)], [c_112])).
% 13.60/4.52  tff(c_54, plain, (~r2_hidden('#skF_8', k1_relat_1('#skF_6')) | r2_hidden('#skF_9', k1_relat_1('#skF_6')) | r2_hidden('#skF_10', k1_relat_1('#skF_6')) | k8_relat_1('#skF_5', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.60/4.52  tff(c_183, plain, (~r2_hidden('#skF_8', k1_relat_1('#skF_6')) | r2_hidden('#skF_9', k1_relat_1('#skF_6')) | r2_hidden('#skF_10', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_54])).
% 13.60/4.52  tff(c_184, plain, (~r2_hidden('#skF_8', k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_183])).
% 13.60/4.52  tff(c_46, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_7')) | r2_hidden('#skF_9', k1_relat_1('#skF_6')) | k1_funct_1('#skF_7', '#skF_10')!=k1_funct_1('#skF_6', '#skF_10') | k8_relat_1('#skF_5', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.60/4.52  tff(c_257, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_7')) | r2_hidden('#skF_9', k1_relat_1('#skF_6')) | k1_funct_1('#skF_7', '#skF_10')!=k1_funct_1('#skF_6', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_163, c_46])).
% 13.60/4.52  tff(c_258, plain, (k1_funct_1('#skF_7', '#skF_10')!=k1_funct_1('#skF_6', '#skF_10')), inference(splitLeft, [status(thm)], [c_257])).
% 13.60/4.52  tff(c_58, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_7')) | r2_hidden('#skF_9', k1_relat_1('#skF_6')) | r2_hidden('#skF_10', k1_relat_1('#skF_6')) | k8_relat_1('#skF_5', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.60/4.52  tff(c_186, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_7')) | r2_hidden('#skF_9', k1_relat_1('#skF_6')) | r2_hidden('#skF_10', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_58])).
% 13.60/4.52  tff(c_187, plain, (r2_hidden('#skF_10', k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_186])).
% 13.60/4.52  tff(c_32, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.60/4.52  tff(c_30, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.60/4.52  tff(c_20, plain, (![A_19, C_21]: (r2_hidden(k4_tarski(A_19, k1_funct_1(C_21, A_19)), C_21) | ~r2_hidden(A_19, k1_relat_1(C_21)) | ~v1_funct_1(C_21) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.60/4.52  tff(c_28, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.60/4.52  tff(c_26, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.60/4.52  tff(c_213, plain, (![D_52, E_53, B_54, A_55]: (r2_hidden(k4_tarski(D_52, E_53), B_54) | ~r2_hidden(k4_tarski(D_52, E_53), k8_relat_1(A_55, B_54)) | ~v1_relat_1(k8_relat_1(A_55, B_54)) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.60/4.52  tff(c_220, plain, (![D_52, E_53]: (r2_hidden(k4_tarski(D_52, E_53), '#skF_7') | ~r2_hidden(k4_tarski(D_52, E_53), '#skF_6') | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_7')) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_163, c_213])).
% 13.60/4.52  tff(c_224, plain, (![D_56, E_57]: (r2_hidden(k4_tarski(D_56, E_57), '#skF_7') | ~r2_hidden(k4_tarski(D_56, E_57), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_163, c_220])).
% 13.60/4.52  tff(c_22, plain, (![C_21, A_19, B_20]: (k1_funct_1(C_21, A_19)=B_20 | ~r2_hidden(k4_tarski(A_19, B_20), C_21) | ~v1_funct_1(C_21) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.60/4.52  tff(c_230, plain, (![D_56, E_57]: (k1_funct_1('#skF_7', D_56)=E_57 | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(k4_tarski(D_56, E_57), '#skF_6'))), inference(resolution, [status(thm)], [c_224, c_22])).
% 13.60/4.52  tff(c_259, plain, (![D_61, E_62]: (k1_funct_1('#skF_7', D_61)=E_62 | ~r2_hidden(k4_tarski(D_61, E_62), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_230])).
% 13.60/4.52  tff(c_263, plain, (![A_19]: (k1_funct_1('#skF_7', A_19)=k1_funct_1('#skF_6', A_19) | ~r2_hidden(A_19, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_20, c_259])).
% 13.60/4.52  tff(c_267, plain, (![A_63]: (k1_funct_1('#skF_7', A_63)=k1_funct_1('#skF_6', A_63) | ~r2_hidden(A_63, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_263])).
% 13.60/4.52  tff(c_270, plain, (k1_funct_1('#skF_7', '#skF_10')=k1_funct_1('#skF_6', '#skF_10')), inference(resolution, [status(thm)], [c_187, c_267])).
% 13.60/4.52  tff(c_278, plain, $false, inference(negUnitSimplification, [status(thm)], [c_258, c_270])).
% 13.60/4.52  tff(c_279, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_6')) | r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_257])).
% 13.60/4.52  tff(c_297, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_279])).
% 13.60/4.52  tff(c_44, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_8'), '#skF_5') | r2_hidden('#skF_9', k1_relat_1('#skF_6')) | k1_funct_1('#skF_7', '#skF_10')!=k1_funct_1('#skF_6', '#skF_10') | k8_relat_1('#skF_5', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.60/4.52  tff(c_282, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_8'), '#skF_5') | r2_hidden('#skF_9', k1_relat_1('#skF_6')) | k1_funct_1('#skF_7', '#skF_10')!=k1_funct_1('#skF_6', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_163, c_44])).
% 13.60/4.52  tff(c_283, plain, (k1_funct_1('#skF_7', '#skF_10')!=k1_funct_1('#skF_6', '#skF_10')), inference(splitLeft, [status(thm)], [c_282])).
% 13.60/4.52  tff(c_280, plain, (k1_funct_1('#skF_7', '#skF_10')=k1_funct_1('#skF_6', '#skF_10')), inference(splitRight, [status(thm)], [c_257])).
% 13.60/4.52  tff(c_284, plain, $false, inference(negUnitSimplification, [status(thm)], [c_283, c_280])).
% 13.60/4.52  tff(c_285, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_6')) | r2_hidden(k1_funct_1('#skF_7', '#skF_8'), '#skF_5')), inference(splitRight, [status(thm)], [c_282])).
% 13.60/4.52  tff(c_298, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_8'), '#skF_5')), inference(splitLeft, [status(thm)], [c_285])).
% 13.60/4.52  tff(c_346, plain, (![D_67, E_68, A_69, B_70]: (r2_hidden(k4_tarski(D_67, E_68), k8_relat_1(A_69, B_70)) | ~r2_hidden(k4_tarski(D_67, E_68), B_70) | ~r2_hidden(E_68, A_69) | ~v1_relat_1(k8_relat_1(A_69, B_70)) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.60/4.52  tff(c_361, plain, (![D_67, E_68]: (r2_hidden(k4_tarski(D_67, E_68), '#skF_6') | ~r2_hidden(k4_tarski(D_67, E_68), '#skF_7') | ~r2_hidden(E_68, '#skF_5') | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_7')) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_163, c_346])).
% 13.60/4.52  tff(c_368, plain, (![D_71, E_72]: (r2_hidden(k4_tarski(D_71, E_72), '#skF_6') | ~r2_hidden(k4_tarski(D_71, E_72), '#skF_7') | ~r2_hidden(E_72, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_163, c_361])).
% 13.60/4.52  tff(c_378, plain, (![A_19]: (r2_hidden(k4_tarski(A_19, k1_funct_1('#skF_7', A_19)), '#skF_6') | ~r2_hidden(k1_funct_1('#skF_7', A_19), '#skF_5') | ~r2_hidden(A_19, k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_20, c_368])).
% 13.60/4.52  tff(c_423, plain, (![A_73]: (r2_hidden(k4_tarski(A_73, k1_funct_1('#skF_7', A_73)), '#skF_6') | ~r2_hidden(k1_funct_1('#skF_7', A_73), '#skF_5') | ~r2_hidden(A_73, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_378])).
% 13.60/4.52  tff(c_24, plain, (![A_19, C_21, B_20]: (r2_hidden(A_19, k1_relat_1(C_21)) | ~r2_hidden(k4_tarski(A_19, B_20), C_21) | ~v1_funct_1(C_21) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.60/4.52  tff(c_435, plain, (![A_73]: (r2_hidden(A_73, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~r2_hidden(k1_funct_1('#skF_7', A_73), '#skF_5') | ~r2_hidden(A_73, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_423, c_24])).
% 13.60/4.52  tff(c_456, plain, (![A_74]: (r2_hidden(A_74, k1_relat_1('#skF_6')) | ~r2_hidden(k1_funct_1('#skF_7', A_74), '#skF_5') | ~r2_hidden(A_74, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_435])).
% 13.60/4.52  tff(c_459, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_6')) | ~r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_298, c_456])).
% 13.60/4.52  tff(c_465, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_297, c_459])).
% 13.60/4.52  tff(c_467, plain, $false, inference(negUnitSimplification, [status(thm)], [c_184, c_465])).
% 13.60/4.52  tff(c_469, plain, (~r2_hidden(k1_funct_1('#skF_7', '#skF_8'), '#skF_5')), inference(splitRight, [status(thm)], [c_285])).
% 13.60/4.52  tff(c_468, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_285])).
% 13.60/4.52  tff(c_227, plain, (![D_56, E_57]: (r2_hidden(D_56, k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(k4_tarski(D_56, E_57), '#skF_6'))), inference(resolution, [status(thm)], [c_224, c_24])).
% 13.60/4.52  tff(c_237, plain, (![D_58, E_59]: (r2_hidden(D_58, k1_relat_1('#skF_7')) | ~r2_hidden(k4_tarski(D_58, E_59), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_227])).
% 13.60/4.52  tff(c_241, plain, (![A_19]: (r2_hidden(A_19, k1_relat_1('#skF_7')) | ~r2_hidden(A_19, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_20, c_237])).
% 13.60/4.52  tff(c_244, plain, (![A_19]: (r2_hidden(A_19, k1_relat_1('#skF_7')) | ~r2_hidden(A_19, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_241])).
% 13.60/4.52  tff(c_470, plain, (![D_75, E_76]: (k1_funct_1('#skF_7', D_75)=E_76 | ~r2_hidden(k4_tarski(D_75, E_76), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_230])).
% 13.60/4.52  tff(c_474, plain, (![A_19]: (k1_funct_1('#skF_7', A_19)=k1_funct_1('#skF_6', A_19) | ~r2_hidden(A_19, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_20, c_470])).
% 13.60/4.52  tff(c_478, plain, (![A_77]: (k1_funct_1('#skF_7', A_77)=k1_funct_1('#skF_6', A_77) | ~r2_hidden(A_77, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_474])).
% 13.60/4.52  tff(c_489, plain, (k1_funct_1('#skF_7', '#skF_9')=k1_funct_1('#skF_6', '#skF_9')), inference(resolution, [status(thm)], [c_468, c_478])).
% 13.60/4.52  tff(c_497, plain, (r2_hidden(k4_tarski('#skF_9', k1_funct_1('#skF_6', '#skF_9')), '#skF_7') | ~r2_hidden('#skF_9', k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_489, c_20])).
% 13.60/4.52  tff(c_501, plain, (r2_hidden(k4_tarski('#skF_9', k1_funct_1('#skF_6', '#skF_9')), '#skF_7') | ~r2_hidden('#skF_9', k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_497])).
% 13.60/4.52  tff(c_526, plain, (~r2_hidden('#skF_9', k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_501])).
% 13.60/4.52  tff(c_529, plain, (~r2_hidden('#skF_9', k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_244, c_526])).
% 13.60/4.52  tff(c_533, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_468, c_529])).
% 13.60/4.52  tff(c_535, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_501])).
% 13.60/4.52  tff(c_188, plain, (![E_45, A_46, D_47, B_48]: (r2_hidden(E_45, A_46) | ~r2_hidden(k4_tarski(D_47, E_45), k8_relat_1(A_46, B_48)) | ~v1_relat_1(k8_relat_1(A_46, B_48)) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.60/4.52  tff(c_195, plain, (![E_45, D_47]: (r2_hidden(E_45, '#skF_5') | ~r2_hidden(k4_tarski(D_47, E_45), '#skF_6') | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_7')) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_163, c_188])).
% 13.60/4.52  tff(c_199, plain, (![E_49, D_50]: (r2_hidden(E_49, '#skF_5') | ~r2_hidden(k4_tarski(D_50, E_49), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_163, c_195])).
% 13.60/4.52  tff(c_203, plain, (![A_19]: (r2_hidden(k1_funct_1('#skF_6', A_19), '#skF_5') | ~r2_hidden(A_19, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_20, c_199])).
% 13.60/4.52  tff(c_206, plain, (![A_19]: (r2_hidden(k1_funct_1('#skF_6', A_19), '#skF_5') | ~r2_hidden(A_19, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_203])).
% 13.60/4.52  tff(c_534, plain, (r2_hidden(k4_tarski('#skF_9', k1_funct_1('#skF_6', '#skF_9')), '#skF_7')), inference(splitRight, [status(thm)], [c_501])).
% 13.60/4.52  tff(c_552, plain, (![D_78, E_79, A_80, B_81]: (r2_hidden(k4_tarski(D_78, E_79), k8_relat_1(A_80, B_81)) | ~r2_hidden(k4_tarski(D_78, E_79), B_81) | ~r2_hidden(E_79, A_80) | ~v1_relat_1(k8_relat_1(A_80, B_81)) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.60/4.52  tff(c_567, plain, (![D_78, E_79]: (r2_hidden(k4_tarski(D_78, E_79), '#skF_6') | ~r2_hidden(k4_tarski(D_78, E_79), '#skF_7') | ~r2_hidden(E_79, '#skF_5') | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_7')) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_163, c_552])).
% 13.60/4.52  tff(c_574, plain, (![D_82, E_83]: (r2_hidden(k4_tarski(D_82, E_83), '#skF_6') | ~r2_hidden(k4_tarski(D_82, E_83), '#skF_7') | ~r2_hidden(E_83, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_163, c_567])).
% 13.60/4.52  tff(c_588, plain, (r2_hidden(k4_tarski('#skF_9', k1_funct_1('#skF_6', '#skF_9')), '#skF_6') | ~r2_hidden(k1_funct_1('#skF_6', '#skF_9'), '#skF_5')), inference(resolution, [status(thm)], [c_534, c_574])).
% 13.60/4.52  tff(c_633, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_9'), '#skF_5')), inference(splitLeft, [status(thm)], [c_588])).
% 13.60/4.52  tff(c_638, plain, (~r2_hidden('#skF_9', k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_206, c_633])).
% 13.60/4.52  tff(c_642, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_468, c_638])).
% 13.60/4.52  tff(c_644, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_9'), '#skF_5')), inference(splitRight, [status(thm)], [c_588])).
% 13.60/4.52  tff(c_38, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_8'), '#skF_5') | ~r2_hidden(k1_funct_1('#skF_7', '#skF_9'), '#skF_5') | ~r2_hidden('#skF_9', k1_relat_1('#skF_7')) | k1_funct_1('#skF_7', '#skF_10')!=k1_funct_1('#skF_6', '#skF_10') | k8_relat_1('#skF_5', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.60/4.52  tff(c_778, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_8'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_163, c_280, c_535, c_644, c_489, c_38])).
% 13.60/4.52  tff(c_779, plain, $false, inference(negUnitSimplification, [status(thm)], [c_469, c_778])).
% 13.60/4.52  tff(c_781, plain, (~r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_279])).
% 13.60/4.52  tff(c_780, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_279])).
% 13.60/4.52  tff(c_787, plain, (![D_90, E_91]: (k1_funct_1('#skF_7', D_90)=E_91 | ~r2_hidden(k4_tarski(D_90, E_91), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_230])).
% 13.60/4.52  tff(c_791, plain, (![A_19]: (k1_funct_1('#skF_7', A_19)=k1_funct_1('#skF_6', A_19) | ~r2_hidden(A_19, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_20, c_787])).
% 13.60/4.52  tff(c_797, plain, (![A_92]: (k1_funct_1('#skF_7', A_92)=k1_funct_1('#skF_6', A_92) | ~r2_hidden(A_92, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_791])).
% 13.60/4.52  tff(c_808, plain, (k1_funct_1('#skF_7', '#skF_9')=k1_funct_1('#skF_6', '#skF_9')), inference(resolution, [status(thm)], [c_780, c_797])).
% 13.60/4.52  tff(c_815, plain, (r2_hidden(k4_tarski('#skF_9', k1_funct_1('#skF_6', '#skF_9')), '#skF_7') | ~r2_hidden('#skF_9', k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_808, c_20])).
% 13.60/4.52  tff(c_819, plain, (r2_hidden(k4_tarski('#skF_9', k1_funct_1('#skF_6', '#skF_9')), '#skF_7') | ~r2_hidden('#skF_9', k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_815])).
% 13.60/4.52  tff(c_844, plain, (~r2_hidden('#skF_9', k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_819])).
% 13.60/4.52  tff(c_847, plain, (~r2_hidden('#skF_9', k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_244, c_844])).
% 13.60/4.52  tff(c_851, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_780, c_847])).
% 13.60/4.52  tff(c_853, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_819])).
% 13.60/4.52  tff(c_852, plain, (r2_hidden(k4_tarski('#skF_9', k1_funct_1('#skF_6', '#skF_9')), '#skF_7')), inference(splitRight, [status(thm)], [c_819])).
% 13.60/4.52  tff(c_871, plain, (![D_93, E_94, A_95, B_96]: (r2_hidden(k4_tarski(D_93, E_94), k8_relat_1(A_95, B_96)) | ~r2_hidden(k4_tarski(D_93, E_94), B_96) | ~r2_hidden(E_94, A_95) | ~v1_relat_1(k8_relat_1(A_95, B_96)) | ~v1_relat_1(B_96))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.60/4.52  tff(c_886, plain, (![D_93, E_94]: (r2_hidden(k4_tarski(D_93, E_94), '#skF_6') | ~r2_hidden(k4_tarski(D_93, E_94), '#skF_7') | ~r2_hidden(E_94, '#skF_5') | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_7')) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_163, c_871])).
% 13.60/4.52  tff(c_893, plain, (![D_97, E_98]: (r2_hidden(k4_tarski(D_97, E_98), '#skF_6') | ~r2_hidden(k4_tarski(D_97, E_98), '#skF_7') | ~r2_hidden(E_98, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_163, c_886])).
% 13.60/4.52  tff(c_907, plain, (r2_hidden(k4_tarski('#skF_9', k1_funct_1('#skF_6', '#skF_9')), '#skF_6') | ~r2_hidden(k1_funct_1('#skF_6', '#skF_9'), '#skF_5')), inference(resolution, [status(thm)], [c_852, c_893])).
% 13.60/4.52  tff(c_953, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_9'), '#skF_5')), inference(splitLeft, [status(thm)], [c_907])).
% 13.60/4.52  tff(c_956, plain, (~r2_hidden('#skF_9', k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_206, c_953])).
% 13.60/4.52  tff(c_960, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_780, c_956])).
% 13.60/4.52  tff(c_962, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_9'), '#skF_5')), inference(splitRight, [status(thm)], [c_907])).
% 13.60/4.52  tff(c_40, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_7')) | ~r2_hidden(k1_funct_1('#skF_7', '#skF_9'), '#skF_5') | ~r2_hidden('#skF_9', k1_relat_1('#skF_7')) | k1_funct_1('#skF_7', '#skF_10')!=k1_funct_1('#skF_6', '#skF_10') | k8_relat_1('#skF_5', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.60/4.52  tff(c_1073, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_280, c_853, c_962, c_808, c_40])).
% 13.60/4.52  tff(c_1074, plain, $false, inference(negUnitSimplification, [status(thm)], [c_781, c_1073])).
% 13.60/4.52  tff(c_1075, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_6')) | r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_186])).
% 13.60/4.52  tff(c_1077, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_1075])).
% 13.60/4.52  tff(c_1076, plain, (~r2_hidden('#skF_10', k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_186])).
% 13.60/4.52  tff(c_56, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_8'), '#skF_5') | r2_hidden('#skF_9', k1_relat_1('#skF_6')) | r2_hidden('#skF_10', k1_relat_1('#skF_6')) | k8_relat_1('#skF_5', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.60/4.52  tff(c_1098, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_8'), '#skF_5') | r2_hidden('#skF_9', k1_relat_1('#skF_6')) | r2_hidden('#skF_10', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_56])).
% 13.60/4.52  tff(c_1099, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_8'), '#skF_5') | r2_hidden('#skF_9', k1_relat_1('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_1076, c_1098])).
% 13.60/4.52  tff(c_1100, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_1099])).
% 13.60/4.52  tff(c_1105, plain, (![D_109, E_110, B_111, A_112]: (r2_hidden(k4_tarski(D_109, E_110), B_111) | ~r2_hidden(k4_tarski(D_109, E_110), k8_relat_1(A_112, B_111)) | ~v1_relat_1(k8_relat_1(A_112, B_111)) | ~v1_relat_1(B_111))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.60/4.52  tff(c_1112, plain, (![D_109, E_110]: (r2_hidden(k4_tarski(D_109, E_110), '#skF_7') | ~r2_hidden(k4_tarski(D_109, E_110), '#skF_6') | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_7')) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_163, c_1105])).
% 13.60/4.52  tff(c_1118, plain, (![D_113, E_114]: (r2_hidden(k4_tarski(D_113, E_114), '#skF_7') | ~r2_hidden(k4_tarski(D_113, E_114), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_163, c_1112])).
% 13.60/4.52  tff(c_1121, plain, (![D_113, E_114]: (r2_hidden(D_113, k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(k4_tarski(D_113, E_114), '#skF_6'))), inference(resolution, [status(thm)], [c_1118, c_24])).
% 13.60/4.52  tff(c_1131, plain, (![D_115, E_116]: (r2_hidden(D_115, k1_relat_1('#skF_7')) | ~r2_hidden(k4_tarski(D_115, E_116), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_1121])).
% 13.60/4.52  tff(c_1135, plain, (![A_19]: (r2_hidden(A_19, k1_relat_1('#skF_7')) | ~r2_hidden(A_19, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_20, c_1131])).
% 13.60/4.52  tff(c_1138, plain, (![A_19]: (r2_hidden(A_19, k1_relat_1('#skF_7')) | ~r2_hidden(A_19, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1135])).
% 13.60/4.52  tff(c_1124, plain, (![D_113, E_114]: (k1_funct_1('#skF_7', D_113)=E_114 | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(k4_tarski(D_113, E_114), '#skF_6'))), inference(resolution, [status(thm)], [c_1118, c_22])).
% 13.60/4.52  tff(c_1152, plain, (![D_118, E_119]: (k1_funct_1('#skF_7', D_118)=E_119 | ~r2_hidden(k4_tarski(D_118, E_119), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_1124])).
% 13.60/4.52  tff(c_1156, plain, (![A_19]: (k1_funct_1('#skF_7', A_19)=k1_funct_1('#skF_6', A_19) | ~r2_hidden(A_19, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_20, c_1152])).
% 13.60/4.52  tff(c_1160, plain, (![A_120]: (k1_funct_1('#skF_7', A_120)=k1_funct_1('#skF_6', A_120) | ~r2_hidden(A_120, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1156])).
% 13.60/4.52  tff(c_1168, plain, (k1_funct_1('#skF_7', '#skF_9')=k1_funct_1('#skF_6', '#skF_9')), inference(resolution, [status(thm)], [c_1100, c_1160])).
% 13.60/4.52  tff(c_1173, plain, (r2_hidden(k4_tarski('#skF_9', k1_funct_1('#skF_6', '#skF_9')), '#skF_7') | ~r2_hidden('#skF_9', k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1168, c_20])).
% 13.60/4.52  tff(c_1177, plain, (r2_hidden(k4_tarski('#skF_9', k1_funct_1('#skF_6', '#skF_9')), '#skF_7') | ~r2_hidden('#skF_9', k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_1173])).
% 13.60/4.52  tff(c_1179, plain, (~r2_hidden('#skF_9', k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_1177])).
% 13.60/4.52  tff(c_1182, plain, (~r2_hidden('#skF_9', k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_1138, c_1179])).
% 13.60/4.52  tff(c_1186, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1100, c_1182])).
% 13.60/4.52  tff(c_1188, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_1177])).
% 13.60/4.52  tff(c_1078, plain, (![E_102, A_103, D_104, B_105]: (r2_hidden(E_102, A_103) | ~r2_hidden(k4_tarski(D_104, E_102), k8_relat_1(A_103, B_105)) | ~v1_relat_1(k8_relat_1(A_103, B_105)) | ~v1_relat_1(B_105))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.60/4.52  tff(c_1085, plain, (![E_102, D_104]: (r2_hidden(E_102, '#skF_5') | ~r2_hidden(k4_tarski(D_104, E_102), '#skF_6') | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_7')) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_163, c_1078])).
% 13.60/4.52  tff(c_1089, plain, (![E_106, D_107]: (r2_hidden(E_106, '#skF_5') | ~r2_hidden(k4_tarski(D_107, E_106), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_163, c_1085])).
% 13.60/4.52  tff(c_1093, plain, (![A_19]: (r2_hidden(k1_funct_1('#skF_6', A_19), '#skF_5') | ~r2_hidden(A_19, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_20, c_1089])).
% 13.60/4.52  tff(c_1096, plain, (![A_19]: (r2_hidden(k1_funct_1('#skF_6', A_19), '#skF_5') | ~r2_hidden(A_19, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1093])).
% 13.60/4.52  tff(c_1187, plain, (r2_hidden(k4_tarski('#skF_9', k1_funct_1('#skF_6', '#skF_9')), '#skF_7')), inference(splitRight, [status(thm)], [c_1177])).
% 13.60/4.52  tff(c_1212, plain, (![D_121, E_122, A_123, B_124]: (r2_hidden(k4_tarski(D_121, E_122), k8_relat_1(A_123, B_124)) | ~r2_hidden(k4_tarski(D_121, E_122), B_124) | ~r2_hidden(E_122, A_123) | ~v1_relat_1(k8_relat_1(A_123, B_124)) | ~v1_relat_1(B_124))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.60/4.52  tff(c_1227, plain, (![D_121, E_122]: (r2_hidden(k4_tarski(D_121, E_122), '#skF_6') | ~r2_hidden(k4_tarski(D_121, E_122), '#skF_7') | ~r2_hidden(E_122, '#skF_5') | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_7')) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_163, c_1212])).
% 13.60/4.52  tff(c_1234, plain, (![D_125, E_126]: (r2_hidden(k4_tarski(D_125, E_126), '#skF_6') | ~r2_hidden(k4_tarski(D_125, E_126), '#skF_7') | ~r2_hidden(E_126, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_163, c_1227])).
% 13.60/4.52  tff(c_1245, plain, (r2_hidden(k4_tarski('#skF_9', k1_funct_1('#skF_6', '#skF_9')), '#skF_6') | ~r2_hidden(k1_funct_1('#skF_6', '#skF_9'), '#skF_5')), inference(resolution, [status(thm)], [c_1187, c_1234])).
% 13.60/4.52  tff(c_1250, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_9'), '#skF_5')), inference(splitLeft, [status(thm)], [c_1245])).
% 13.60/4.52  tff(c_1253, plain, (~r2_hidden('#skF_9', k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_1096, c_1250])).
% 13.60/4.52  tff(c_1257, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1100, c_1253])).
% 13.60/4.52  tff(c_1259, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_9'), '#skF_5')), inference(splitRight, [status(thm)], [c_1245])).
% 13.60/4.52  tff(c_50, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_8'), '#skF_5') | ~r2_hidden(k1_funct_1('#skF_7', '#skF_9'), '#skF_5') | ~r2_hidden('#skF_9', k1_relat_1('#skF_7')) | r2_hidden('#skF_10', k1_relat_1('#skF_6')) | k8_relat_1('#skF_5', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.60/4.52  tff(c_1346, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_8'), '#skF_5') | r2_hidden('#skF_10', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_1188, c_1259, c_1168, c_50])).
% 13.60/4.52  tff(c_1347, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_8'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_1076, c_1346])).
% 13.60/4.52  tff(c_1244, plain, (![A_19]: (r2_hidden(k4_tarski(A_19, k1_funct_1('#skF_7', A_19)), '#skF_6') | ~r2_hidden(k1_funct_1('#skF_7', A_19), '#skF_5') | ~r2_hidden(A_19, k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_20, c_1234])).
% 13.60/4.52  tff(c_1291, plain, (![A_127]: (r2_hidden(k4_tarski(A_127, k1_funct_1('#skF_7', A_127)), '#skF_6') | ~r2_hidden(k1_funct_1('#skF_7', A_127), '#skF_5') | ~r2_hidden(A_127, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_1244])).
% 13.60/4.52  tff(c_1303, plain, (![A_127]: (r2_hidden(A_127, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~r2_hidden(k1_funct_1('#skF_7', A_127), '#skF_5') | ~r2_hidden(A_127, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_1291, c_24])).
% 13.60/4.52  tff(c_1316, plain, (![A_127]: (r2_hidden(A_127, k1_relat_1('#skF_6')) | ~r2_hidden(k1_funct_1('#skF_7', A_127), '#skF_5') | ~r2_hidden(A_127, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1303])).
% 13.60/4.52  tff(c_1353, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_6')) | ~r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_1347, c_1316])).
% 13.60/4.52  tff(c_1359, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1077, c_1353])).
% 13.60/4.52  tff(c_1361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_184, c_1359])).
% 13.60/4.52  tff(c_1362, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_8'), '#skF_5')), inference(splitRight, [status(thm)], [c_1099])).
% 13.60/4.52  tff(c_1442, plain, (![D_143, E_144, A_145, B_146]: (r2_hidden(k4_tarski(D_143, E_144), k8_relat_1(A_145, B_146)) | ~r2_hidden(k4_tarski(D_143, E_144), B_146) | ~r2_hidden(E_144, A_145) | ~v1_relat_1(k8_relat_1(A_145, B_146)) | ~v1_relat_1(B_146))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.60/4.52  tff(c_1457, plain, (![D_143, E_144]: (r2_hidden(k4_tarski(D_143, E_144), '#skF_6') | ~r2_hidden(k4_tarski(D_143, E_144), '#skF_7') | ~r2_hidden(E_144, '#skF_5') | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_7')) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_163, c_1442])).
% 13.60/4.52  tff(c_1464, plain, (![D_147, E_148]: (r2_hidden(k4_tarski(D_147, E_148), '#skF_6') | ~r2_hidden(k4_tarski(D_147, E_148), '#skF_7') | ~r2_hidden(E_148, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_163, c_1457])).
% 13.60/4.52  tff(c_1471, plain, (![A_19]: (r2_hidden(k4_tarski(A_19, k1_funct_1('#skF_7', A_19)), '#skF_6') | ~r2_hidden(k1_funct_1('#skF_7', A_19), '#skF_5') | ~r2_hidden(A_19, k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_20, c_1464])).
% 13.60/4.52  tff(c_1476, plain, (![A_149]: (r2_hidden(k4_tarski(A_149, k1_funct_1('#skF_7', A_149)), '#skF_6') | ~r2_hidden(k1_funct_1('#skF_7', A_149), '#skF_5') | ~r2_hidden(A_149, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_1471])).
% 13.60/4.52  tff(c_1488, plain, (![A_149]: (r2_hidden(A_149, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~r2_hidden(k1_funct_1('#skF_7', A_149), '#skF_5') | ~r2_hidden(A_149, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_1476, c_24])).
% 13.60/4.52  tff(c_1503, plain, (![A_150]: (r2_hidden(A_150, k1_relat_1('#skF_6')) | ~r2_hidden(k1_funct_1('#skF_7', A_150), '#skF_5') | ~r2_hidden(A_150, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1488])).
% 13.60/4.52  tff(c_1506, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_6')) | ~r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_1362, c_1503])).
% 13.60/4.52  tff(c_1509, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1077, c_1506])).
% 13.60/4.52  tff(c_1511, plain, $false, inference(negUnitSimplification, [status(thm)], [c_184, c_1509])).
% 13.60/4.52  tff(c_1512, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_1075])).
% 13.60/4.52  tff(c_1517, plain, (![E_151, A_152, D_153, B_154]: (r2_hidden(E_151, A_152) | ~r2_hidden(k4_tarski(D_153, E_151), k8_relat_1(A_152, B_154)) | ~v1_relat_1(k8_relat_1(A_152, B_154)) | ~v1_relat_1(B_154))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.60/4.52  tff(c_1524, plain, (![E_151, D_153]: (r2_hidden(E_151, '#skF_5') | ~r2_hidden(k4_tarski(D_153, E_151), '#skF_6') | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_7')) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_163, c_1517])).
% 13.60/4.52  tff(c_1528, plain, (![E_155, D_156]: (r2_hidden(E_155, '#skF_5') | ~r2_hidden(k4_tarski(D_156, E_155), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_163, c_1524])).
% 13.60/4.52  tff(c_1532, plain, (![A_19]: (r2_hidden(k1_funct_1('#skF_6', A_19), '#skF_5') | ~r2_hidden(A_19, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_20, c_1528])).
% 13.60/4.52  tff(c_1535, plain, (![A_19]: (r2_hidden(k1_funct_1('#skF_6', A_19), '#skF_5') | ~r2_hidden(A_19, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1532])).
% 13.60/4.52  tff(c_1513, plain, (~r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_1075])).
% 13.60/4.52  tff(c_1538, plain, (![D_158, E_159, B_160, A_161]: (r2_hidden(k4_tarski(D_158, E_159), B_160) | ~r2_hidden(k4_tarski(D_158, E_159), k8_relat_1(A_161, B_160)) | ~v1_relat_1(k8_relat_1(A_161, B_160)) | ~v1_relat_1(B_160))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.60/4.52  tff(c_1545, plain, (![D_158, E_159]: (r2_hidden(k4_tarski(D_158, E_159), '#skF_7') | ~r2_hidden(k4_tarski(D_158, E_159), '#skF_6') | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_7')) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_163, c_1538])).
% 13.60/4.52  tff(c_1551, plain, (![D_162, E_163]: (r2_hidden(k4_tarski(D_162, E_163), '#skF_7') | ~r2_hidden(k4_tarski(D_162, E_163), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_163, c_1545])).
% 13.60/4.52  tff(c_1554, plain, (![D_162, E_163]: (r2_hidden(D_162, k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(k4_tarski(D_162, E_163), '#skF_6'))), inference(resolution, [status(thm)], [c_1551, c_24])).
% 13.60/4.52  tff(c_1564, plain, (![D_164, E_165]: (r2_hidden(D_164, k1_relat_1('#skF_7')) | ~r2_hidden(k4_tarski(D_164, E_165), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_1554])).
% 13.60/4.52  tff(c_1568, plain, (![A_19]: (r2_hidden(A_19, k1_relat_1('#skF_7')) | ~r2_hidden(A_19, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_20, c_1564])).
% 13.60/4.52  tff(c_1571, plain, (![A_19]: (r2_hidden(A_19, k1_relat_1('#skF_7')) | ~r2_hidden(A_19, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1568])).
% 13.60/4.52  tff(c_1557, plain, (![D_162, E_163]: (k1_funct_1('#skF_7', D_162)=E_163 | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(k4_tarski(D_162, E_163), '#skF_6'))), inference(resolution, [status(thm)], [c_1551, c_22])).
% 13.60/4.52  tff(c_1590, plain, (![D_167, E_168]: (k1_funct_1('#skF_7', D_167)=E_168 | ~r2_hidden(k4_tarski(D_167, E_168), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_1557])).
% 13.60/4.52  tff(c_1594, plain, (![A_19]: (k1_funct_1('#skF_7', A_19)=k1_funct_1('#skF_6', A_19) | ~r2_hidden(A_19, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_20, c_1590])).
% 13.60/4.52  tff(c_1598, plain, (![A_169]: (k1_funct_1('#skF_7', A_169)=k1_funct_1('#skF_6', A_169) | ~r2_hidden(A_169, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1594])).
% 13.60/4.52  tff(c_1606, plain, (k1_funct_1('#skF_7', '#skF_9')=k1_funct_1('#skF_6', '#skF_9')), inference(resolution, [status(thm)], [c_1512, c_1598])).
% 13.60/4.52  tff(c_1611, plain, (r2_hidden(k4_tarski('#skF_9', k1_funct_1('#skF_6', '#skF_9')), '#skF_7') | ~r2_hidden('#skF_9', k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1606, c_20])).
% 13.60/4.52  tff(c_1615, plain, (r2_hidden(k4_tarski('#skF_9', k1_funct_1('#skF_6', '#skF_9')), '#skF_7') | ~r2_hidden('#skF_9', k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_1611])).
% 13.60/4.52  tff(c_1617, plain, (~r2_hidden('#skF_9', k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_1615])).
% 13.60/4.52  tff(c_1620, plain, (~r2_hidden('#skF_9', k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_1571, c_1617])).
% 13.60/4.52  tff(c_1624, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1512, c_1620])).
% 13.60/4.52  tff(c_1626, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_1615])).
% 13.60/4.52  tff(c_52, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_7')) | ~r2_hidden(k1_funct_1('#skF_7', '#skF_9'), '#skF_5') | ~r2_hidden('#skF_9', k1_relat_1('#skF_7')) | r2_hidden('#skF_10', k1_relat_1('#skF_6')) | k8_relat_1('#skF_5', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.60/4.52  tff(c_1693, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_7')) | ~r2_hidden(k1_funct_1('#skF_6', '#skF_9'), '#skF_5') | r2_hidden('#skF_10', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_1626, c_1606, c_52])).
% 13.60/4.52  tff(c_1694, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_9'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_1076, c_1513, c_1693])).
% 13.60/4.52  tff(c_1697, plain, (~r2_hidden('#skF_9', k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_1535, c_1694])).
% 13.60/4.52  tff(c_1701, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1512, c_1697])).
% 13.60/4.52  tff(c_1702, plain, (r2_hidden('#skF_10', k1_relat_1('#skF_6')) | r2_hidden('#skF_9', k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_183])).
% 13.60/4.52  tff(c_1704, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_1702])).
% 13.60/4.52  tff(c_1707, plain, (![E_176, A_177, D_178, B_179]: (r2_hidden(E_176, A_177) | ~r2_hidden(k4_tarski(D_178, E_176), k8_relat_1(A_177, B_179)) | ~v1_relat_1(k8_relat_1(A_177, B_179)) | ~v1_relat_1(B_179))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.60/4.52  tff(c_1714, plain, (![E_176, D_178]: (r2_hidden(E_176, '#skF_5') | ~r2_hidden(k4_tarski(D_178, E_176), '#skF_6') | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_7')) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_163, c_1707])).
% 13.60/4.52  tff(c_1719, plain, (![E_180, D_181]: (r2_hidden(E_180, '#skF_5') | ~r2_hidden(k4_tarski(D_181, E_180), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_163, c_1714])).
% 13.60/4.52  tff(c_1723, plain, (![A_19]: (r2_hidden(k1_funct_1('#skF_6', A_19), '#skF_5') | ~r2_hidden(A_19, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_20, c_1719])).
% 13.60/4.52  tff(c_1726, plain, (![A_19]: (r2_hidden(k1_funct_1('#skF_6', A_19), '#skF_5') | ~r2_hidden(A_19, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1723])).
% 13.60/4.52  tff(c_1732, plain, (![D_183, E_184, B_185, A_186]: (r2_hidden(k4_tarski(D_183, E_184), B_185) | ~r2_hidden(k4_tarski(D_183, E_184), k8_relat_1(A_186, B_185)) | ~v1_relat_1(k8_relat_1(A_186, B_185)) | ~v1_relat_1(B_185))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.60/4.52  tff(c_1739, plain, (![D_183, E_184]: (r2_hidden(k4_tarski(D_183, E_184), '#skF_7') | ~r2_hidden(k4_tarski(D_183, E_184), '#skF_6') | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_7')) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_163, c_1732])).
% 13.60/4.52  tff(c_1743, plain, (![D_187, E_188]: (r2_hidden(k4_tarski(D_187, E_188), '#skF_7') | ~r2_hidden(k4_tarski(D_187, E_188), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_163, c_1739])).
% 13.60/4.52  tff(c_1746, plain, (![D_187, E_188]: (r2_hidden(D_187, k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(k4_tarski(D_187, E_188), '#skF_6'))), inference(resolution, [status(thm)], [c_1743, c_24])).
% 13.60/4.52  tff(c_1756, plain, (![D_189, E_190]: (r2_hidden(D_189, k1_relat_1('#skF_7')) | ~r2_hidden(k4_tarski(D_189, E_190), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_1746])).
% 13.60/4.52  tff(c_1760, plain, (![A_19]: (r2_hidden(A_19, k1_relat_1('#skF_7')) | ~r2_hidden(A_19, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_20, c_1756])).
% 13.60/4.52  tff(c_1763, plain, (![A_19]: (r2_hidden(A_19, k1_relat_1('#skF_7')) | ~r2_hidden(A_19, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1760])).
% 13.60/4.52  tff(c_1749, plain, (![D_187, E_188]: (k1_funct_1('#skF_7', D_187)=E_188 | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(k4_tarski(D_187, E_188), '#skF_6'))), inference(resolution, [status(thm)], [c_1743, c_22])).
% 13.60/4.52  tff(c_1775, plain, (![D_192, E_193]: (k1_funct_1('#skF_7', D_192)=E_193 | ~r2_hidden(k4_tarski(D_192, E_193), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_1749])).
% 13.60/4.52  tff(c_1779, plain, (![A_19]: (k1_funct_1('#skF_7', A_19)=k1_funct_1('#skF_6', A_19) | ~r2_hidden(A_19, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_20, c_1775])).
% 13.60/4.52  tff(c_1785, plain, (![A_194]: (k1_funct_1('#skF_7', A_194)=k1_funct_1('#skF_6', A_194) | ~r2_hidden(A_194, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1779])).
% 13.60/4.52  tff(c_1796, plain, (k1_funct_1('#skF_7', '#skF_9')=k1_funct_1('#skF_6', '#skF_9')), inference(resolution, [status(thm)], [c_1704, c_1785])).
% 13.60/4.52  tff(c_1811, plain, (r2_hidden(k4_tarski('#skF_9', k1_funct_1('#skF_6', '#skF_9')), '#skF_7') | ~r2_hidden('#skF_9', k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1796, c_20])).
% 13.60/4.52  tff(c_1815, plain, (r2_hidden(k4_tarski('#skF_9', k1_funct_1('#skF_6', '#skF_9')), '#skF_7') | ~r2_hidden('#skF_9', k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_1811])).
% 13.60/4.52  tff(c_1841, plain, (~r2_hidden('#skF_9', k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_1815])).
% 13.60/4.52  tff(c_1846, plain, (~r2_hidden('#skF_9', k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_1763, c_1841])).
% 13.60/4.52  tff(c_1850, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1704, c_1846])).
% 13.60/4.52  tff(c_1852, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_1815])).
% 13.60/4.52  tff(c_1703, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_183])).
% 13.60/4.52  tff(c_48, plain, (~r2_hidden('#skF_8', k1_relat_1('#skF_6')) | ~r2_hidden(k1_funct_1('#skF_7', '#skF_9'), '#skF_5') | ~r2_hidden('#skF_9', k1_relat_1('#skF_7')) | r2_hidden('#skF_10', k1_relat_1('#skF_6')) | k8_relat_1('#skF_5', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.60/4.52  tff(c_1892, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_9'), '#skF_5') | r2_hidden('#skF_10', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_1852, c_1796, c_1703, c_48])).
% 13.60/4.52  tff(c_1893, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_9'), '#skF_5')), inference(splitLeft, [status(thm)], [c_1892])).
% 13.60/4.52  tff(c_1896, plain, (~r2_hidden('#skF_9', k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_1726, c_1893])).
% 13.60/4.52  tff(c_1900, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1704, c_1896])).
% 13.60/4.52  tff(c_1901, plain, (r2_hidden('#skF_10', k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_1892])).
% 13.60/4.52  tff(c_1782, plain, (![A_19]: (k1_funct_1('#skF_7', A_19)=k1_funct_1('#skF_6', A_19) | ~r2_hidden(A_19, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1779])).
% 13.60/4.52  tff(c_1906, plain, (k1_funct_1('#skF_7', '#skF_10')=k1_funct_1('#skF_6', '#skF_10')), inference(resolution, [status(thm)], [c_1901, c_1782])).
% 13.60/4.52  tff(c_1902, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_9'), '#skF_5')), inference(splitRight, [status(thm)], [c_1892])).
% 13.60/4.52  tff(c_36, plain, (~r2_hidden('#skF_8', k1_relat_1('#skF_6')) | ~r2_hidden(k1_funct_1('#skF_7', '#skF_9'), '#skF_5') | ~r2_hidden('#skF_9', k1_relat_1('#skF_7')) | k1_funct_1('#skF_7', '#skF_10')!=k1_funct_1('#skF_6', '#skF_10') | k8_relat_1('#skF_5', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.60/4.52  tff(c_2169, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_163, c_1906, c_1852, c_1902, c_1796, c_1703, c_36])).
% 13.60/4.52  tff(c_2171, plain, (~r2_hidden('#skF_9', k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_1702])).
% 13.60/4.52  tff(c_2200, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_7')) | r2_hidden('#skF_9', k1_relat_1('#skF_6')) | k1_funct_1('#skF_7', '#skF_10')!=k1_funct_1('#skF_6', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_163, c_46])).
% 13.60/4.52  tff(c_2201, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_7')) | k1_funct_1('#skF_7', '#skF_10')!=k1_funct_1('#skF_6', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_2171, c_2200])).
% 13.60/4.52  tff(c_2202, plain, (k1_funct_1('#skF_7', '#skF_10')!=k1_funct_1('#skF_6', '#skF_10')), inference(splitLeft, [status(thm)], [c_2201])).
% 13.60/4.52  tff(c_2170, plain, (r2_hidden('#skF_10', k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_1702])).
% 13.60/4.52  tff(c_2203, plain, (![D_211, E_212, B_213, A_214]: (r2_hidden(k4_tarski(D_211, E_212), B_213) | ~r2_hidden(k4_tarski(D_211, E_212), k8_relat_1(A_214, B_213)) | ~v1_relat_1(k8_relat_1(A_214, B_213)) | ~v1_relat_1(B_213))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.60/4.52  tff(c_2210, plain, (![D_211, E_212]: (r2_hidden(k4_tarski(D_211, E_212), '#skF_7') | ~r2_hidden(k4_tarski(D_211, E_212), '#skF_6') | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_7')) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_163, c_2203])).
% 13.60/4.52  tff(c_2217, plain, (![D_215, E_216]: (r2_hidden(k4_tarski(D_215, E_216), '#skF_7') | ~r2_hidden(k4_tarski(D_215, E_216), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_163, c_2210])).
% 13.60/4.52  tff(c_2223, plain, (![D_215, E_216]: (k1_funct_1('#skF_7', D_215)=E_216 | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(k4_tarski(D_215, E_216), '#skF_6'))), inference(resolution, [status(thm)], [c_2217, c_22])).
% 13.60/4.52  tff(c_2252, plain, (![D_220, E_221]: (k1_funct_1('#skF_7', D_220)=E_221 | ~r2_hidden(k4_tarski(D_220, E_221), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_2223])).
% 13.60/4.52  tff(c_2256, plain, (![A_19]: (k1_funct_1('#skF_7', A_19)=k1_funct_1('#skF_6', A_19) | ~r2_hidden(A_19, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_20, c_2252])).
% 13.60/4.52  tff(c_2260, plain, (![A_222]: (k1_funct_1('#skF_7', A_222)=k1_funct_1('#skF_6', A_222) | ~r2_hidden(A_222, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_2256])).
% 13.60/4.52  tff(c_2263, plain, (k1_funct_1('#skF_7', '#skF_10')=k1_funct_1('#skF_6', '#skF_10')), inference(resolution, [status(thm)], [c_2170, c_2260])).
% 13.60/4.52  tff(c_2274, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2202, c_2263])).
% 13.60/4.52  tff(c_2276, plain, (k1_funct_1('#skF_7', '#skF_10')=k1_funct_1('#skF_6', '#skF_10')), inference(splitRight, [status(thm)], [c_2201])).
% 13.60/4.52  tff(c_42, plain, (~r2_hidden('#skF_8', k1_relat_1('#skF_6')) | r2_hidden('#skF_9', k1_relat_1('#skF_6')) | k1_funct_1('#skF_7', '#skF_10')!=k1_funct_1('#skF_6', '#skF_10') | k8_relat_1('#skF_5', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.60/4.52  tff(c_2320, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_2276, c_1703, c_42])).
% 13.60/4.52  tff(c_2321, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2171, c_2320])).
% 13.60/4.52  tff(c_2323, plain, (k8_relat_1('#skF_5', '#skF_7')!='#skF_6'), inference(splitRight, [status(thm)], [c_112])).
% 13.60/4.52  tff(c_10, plain, (![A_1, B_2, C_12]: (r2_hidden(k4_tarski('#skF_1'(A_1, B_2, C_12), '#skF_2'(A_1, B_2, C_12)), B_2) | r2_hidden(k4_tarski('#skF_3'(A_1, B_2, C_12), '#skF_4'(A_1, B_2, C_12)), C_12) | k8_relat_1(A_1, B_2)=C_12 | ~v1_relat_1(C_12) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.60/4.52  tff(c_2991, plain, (![A_313, B_314, C_315]: (~r2_hidden(k4_tarski('#skF_1'(A_313, B_314, C_315), '#skF_2'(A_313, B_314, C_315)), C_315) | r2_hidden(k4_tarski('#skF_3'(A_313, B_314, C_315), '#skF_4'(A_313, B_314, C_315)), C_315) | k8_relat_1(A_313, B_314)=C_315 | ~v1_relat_1(C_315) | ~v1_relat_1(B_314))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.60/4.52  tff(c_3017, plain, (![A_316, B_317]: (r2_hidden(k4_tarski('#skF_3'(A_316, B_317, B_317), '#skF_4'(A_316, B_317, B_317)), B_317) | k8_relat_1(A_316, B_317)=B_317 | ~v1_relat_1(B_317))), inference(resolution, [status(thm)], [c_10, c_2991])).
% 13.60/4.52  tff(c_3056, plain, (![A_316, B_317]: (r2_hidden('#skF_3'(A_316, B_317, B_317), k1_relat_1(B_317)) | ~v1_funct_1(B_317) | k8_relat_1(A_316, B_317)=B_317 | ~v1_relat_1(B_317))), inference(resolution, [status(thm)], [c_3017, c_24])).
% 13.60/4.52  tff(c_3055, plain, (![B_317, A_316]: (k1_funct_1(B_317, '#skF_3'(A_316, B_317, B_317))='#skF_4'(A_316, B_317, B_317) | ~v1_funct_1(B_317) | k8_relat_1(A_316, B_317)=B_317 | ~v1_relat_1(B_317))), inference(resolution, [status(thm)], [c_3017, c_22])).
% 13.60/4.52  tff(c_3057, plain, (![A_318, B_319]: (r2_hidden('#skF_3'(A_318, B_319, B_319), k1_relat_1(B_319)) | ~v1_funct_1(B_319) | k8_relat_1(A_318, B_319)=B_319 | ~v1_relat_1(B_319))), inference(resolution, [status(thm)], [c_3017, c_24])).
% 13.60/4.52  tff(c_60, plain, (![D_36]: (k8_relat_1('#skF_5', '#skF_7')='#skF_6' | k1_funct_1('#skF_7', D_36)=k1_funct_1('#skF_6', D_36) | ~r2_hidden(D_36, k1_relat_1('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.60/4.52  tff(c_2339, plain, (![D_36]: (k1_funct_1('#skF_7', D_36)=k1_funct_1('#skF_6', D_36) | ~r2_hidden(D_36, k1_relat_1('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_2323, c_60])).
% 13.60/4.52  tff(c_3069, plain, (![A_318]: (k1_funct_1('#skF_7', '#skF_3'(A_318, '#skF_6', '#skF_6'))=k1_funct_1('#skF_6', '#skF_3'(A_318, '#skF_6', '#skF_6')) | ~v1_funct_1('#skF_6') | k8_relat_1(A_318, '#skF_6')='#skF_6' | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_3057, c_2339])).
% 13.60/4.52  tff(c_3075, plain, (![A_320]: (k1_funct_1('#skF_7', '#skF_3'(A_320, '#skF_6', '#skF_6'))=k1_funct_1('#skF_6', '#skF_3'(A_320, '#skF_6', '#skF_6')) | k8_relat_1(A_320, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_3069])).
% 13.60/4.52  tff(c_86, plain, (![D_35]: (k8_relat_1('#skF_5', '#skF_7')='#skF_6' | r2_hidden(k1_funct_1('#skF_7', D_35), '#skF_5') | ~r2_hidden(D_35, k1_relat_1('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.60/4.52  tff(c_2325, plain, (![D_35]: (r2_hidden(k1_funct_1('#skF_7', D_35), '#skF_5') | ~r2_hidden(D_35, k1_relat_1('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_2323, c_86])).
% 13.60/4.52  tff(c_3148, plain, (![A_324]: (r2_hidden(k1_funct_1('#skF_6', '#skF_3'(A_324, '#skF_6', '#skF_6')), '#skF_5') | ~r2_hidden('#skF_3'(A_324, '#skF_6', '#skF_6'), k1_relat_1('#skF_6')) | k8_relat_1(A_324, '#skF_6')='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3075, c_2325])).
% 13.60/4.52  tff(c_3155, plain, (![A_316]: (r2_hidden('#skF_4'(A_316, '#skF_6', '#skF_6'), '#skF_5') | ~r2_hidden('#skF_3'(A_316, '#skF_6', '#skF_6'), k1_relat_1('#skF_6')) | k8_relat_1(A_316, '#skF_6')='#skF_6' | ~v1_funct_1('#skF_6') | k8_relat_1(A_316, '#skF_6')='#skF_6' | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3055, c_3148])).
% 13.60/4.52  tff(c_3165, plain, (![A_325]: (r2_hidden('#skF_4'(A_325, '#skF_6', '#skF_6'), '#skF_5') | ~r2_hidden('#skF_3'(A_325, '#skF_6', '#skF_6'), k1_relat_1('#skF_6')) | k8_relat_1(A_325, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_3155])).
% 13.60/4.52  tff(c_3169, plain, (![A_316]: (r2_hidden('#skF_4'(A_316, '#skF_6', '#skF_6'), '#skF_5') | ~v1_funct_1('#skF_6') | k8_relat_1(A_316, '#skF_6')='#skF_6' | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_3056, c_3165])).
% 13.60/4.52  tff(c_3186, plain, (![A_316]: (r2_hidden('#skF_4'(A_316, '#skF_6', '#skF_6'), '#skF_5') | k8_relat_1(A_316, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_3169])).
% 13.60/4.52  tff(c_12, plain, (![A_1, B_2, C_12]: (r2_hidden('#skF_2'(A_1, B_2, C_12), A_1) | r2_hidden(k4_tarski('#skF_3'(A_1, B_2, C_12), '#skF_4'(A_1, B_2, C_12)), C_12) | k8_relat_1(A_1, B_2)=C_12 | ~v1_relat_1(C_12) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.60/4.52  tff(c_3197, plain, (![A_327, B_328, C_329]: (r2_hidden('#skF_2'(A_327, B_328, C_329), A_327) | ~r2_hidden(k4_tarski('#skF_3'(A_327, B_328, C_329), '#skF_4'(A_327, B_328, C_329)), B_328) | ~r2_hidden('#skF_4'(A_327, B_328, C_329), A_327) | k8_relat_1(A_327, B_328)=C_329 | ~v1_relat_1(C_329) | ~v1_relat_1(B_328))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.60/4.52  tff(c_3229, plain, (![A_330, C_331]: (~r2_hidden('#skF_4'(A_330, C_331, C_331), A_330) | r2_hidden('#skF_2'(A_330, C_331, C_331), A_330) | k8_relat_1(A_330, C_331)=C_331 | ~v1_relat_1(C_331))), inference(resolution, [status(thm)], [c_12, c_3197])).
% 13.60/4.52  tff(c_3233, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_6', '#skF_6'), '#skF_5') | ~v1_relat_1('#skF_6') | k8_relat_1('#skF_5', '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_3186, c_3229])).
% 13.60/4.52  tff(c_3244, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_6', '#skF_6'), '#skF_5') | k8_relat_1('#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_3233])).
% 13.60/4.52  tff(c_3247, plain, (k8_relat_1('#skF_5', '#skF_6')='#skF_6'), inference(splitLeft, [status(thm)], [c_3244])).
% 13.60/4.52  tff(c_2409, plain, (![A_262, B_263, C_264]: (r2_hidden('#skF_2'(A_262, B_263, C_264), A_262) | r2_hidden(k4_tarski('#skF_3'(A_262, B_263, C_264), '#skF_4'(A_262, B_263, C_264)), C_264) | k8_relat_1(A_262, B_263)=C_264 | ~v1_relat_1(C_264) | ~v1_relat_1(B_263))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.60/4.52  tff(c_16, plain, (![D_17, E_18, B_2, A_1]: (r2_hidden(k4_tarski(D_17, E_18), B_2) | ~r2_hidden(k4_tarski(D_17, E_18), k8_relat_1(A_1, B_2)) | ~v1_relat_1(k8_relat_1(A_1, B_2)) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.60/4.52  tff(c_5815, plain, (![A_461, B_462, A_463, B_464]: (r2_hidden(k4_tarski('#skF_3'(A_461, B_462, k8_relat_1(A_463, B_464)), '#skF_4'(A_461, B_462, k8_relat_1(A_463, B_464))), B_464) | ~v1_relat_1(B_464) | r2_hidden('#skF_2'(A_461, B_462, k8_relat_1(A_463, B_464)), A_461) | k8_relat_1(A_463, B_464)=k8_relat_1(A_461, B_462) | ~v1_relat_1(k8_relat_1(A_463, B_464)) | ~v1_relat_1(B_462))), inference(resolution, [status(thm)], [c_2409, c_16])).
% 13.60/4.52  tff(c_5877, plain, (![A_461, B_462]: (r2_hidden(k4_tarski('#skF_3'(A_461, B_462, '#skF_6'), '#skF_4'(A_461, B_462, k8_relat_1('#skF_5', '#skF_6'))), '#skF_6') | ~v1_relat_1('#skF_6') | r2_hidden('#skF_2'(A_461, B_462, k8_relat_1('#skF_5', '#skF_6')), A_461) | k8_relat_1(A_461, B_462)=k8_relat_1('#skF_5', '#skF_6') | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_6')) | ~v1_relat_1(B_462))), inference(superposition, [status(thm), theory('equality')], [c_3247, c_5815])).
% 13.60/4.52  tff(c_6297, plain, (![A_474, B_475]: (r2_hidden(k4_tarski('#skF_3'(A_474, B_475, '#skF_6'), '#skF_4'(A_474, B_475, '#skF_6')), '#skF_6') | r2_hidden('#skF_2'(A_474, B_475, '#skF_6'), A_474) | k8_relat_1(A_474, B_475)='#skF_6' | ~v1_relat_1(B_475))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_3247, c_3247, c_3247, c_32, c_3247, c_5877])).
% 13.60/4.52  tff(c_6323, plain, (![A_474, B_475]: (k1_funct_1('#skF_6', '#skF_3'(A_474, B_475, '#skF_6'))='#skF_4'(A_474, B_475, '#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | r2_hidden('#skF_2'(A_474, B_475, '#skF_6'), A_474) | k8_relat_1(A_474, B_475)='#skF_6' | ~v1_relat_1(B_475))), inference(resolution, [status(thm)], [c_6297, c_22])).
% 13.60/4.52  tff(c_6348, plain, (![A_474, B_475]: (k1_funct_1('#skF_6', '#skF_3'(A_474, B_475, '#skF_6'))='#skF_4'(A_474, B_475, '#skF_6') | r2_hidden('#skF_2'(A_474, B_475, '#skF_6'), A_474) | k8_relat_1(A_474, B_475)='#skF_6' | ~v1_relat_1(B_475))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_6323])).
% 13.60/4.52  tff(c_2663, plain, (![A_292, B_293, C_294]: (r2_hidden(k4_tarski('#skF_1'(A_292, B_293, C_294), '#skF_2'(A_292, B_293, C_294)), B_293) | r2_hidden(k4_tarski('#skF_3'(A_292, B_293, C_294), '#skF_4'(A_292, B_293, C_294)), C_294) | k8_relat_1(A_292, B_293)=C_294 | ~v1_relat_1(C_294) | ~v1_relat_1(B_293))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.60/4.52  tff(c_7019, plain, (![A_513, B_514, A_515, B_516]: (r2_hidden(k4_tarski('#skF_3'(A_513, B_514, k8_relat_1(A_515, B_516)), '#skF_4'(A_513, B_514, k8_relat_1(A_515, B_516))), B_516) | ~v1_relat_1(B_516) | r2_hidden(k4_tarski('#skF_1'(A_513, B_514, k8_relat_1(A_515, B_516)), '#skF_2'(A_513, B_514, k8_relat_1(A_515, B_516))), B_514) | k8_relat_1(A_515, B_516)=k8_relat_1(A_513, B_514) | ~v1_relat_1(k8_relat_1(A_515, B_516)) | ~v1_relat_1(B_514))), inference(resolution, [status(thm)], [c_2663, c_16])).
% 13.60/4.52  tff(c_7134, plain, (![A_513, B_514]: (r2_hidden(k4_tarski('#skF_3'(A_513, B_514, k8_relat_1('#skF_5', '#skF_6')), '#skF_4'(A_513, B_514, k8_relat_1('#skF_5', '#skF_6'))), '#skF_6') | ~v1_relat_1('#skF_6') | r2_hidden(k4_tarski('#skF_1'(A_513, B_514, k8_relat_1('#skF_5', '#skF_6')), '#skF_2'(A_513, B_514, '#skF_6')), B_514) | k8_relat_1(A_513, B_514)=k8_relat_1('#skF_5', '#skF_6') | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_6')) | ~v1_relat_1(B_514))), inference(superposition, [status(thm), theory('equality')], [c_3247, c_7019])).
% 13.60/4.52  tff(c_7625, plain, (![A_534, B_535]: (r2_hidden(k4_tarski('#skF_3'(A_534, B_535, '#skF_6'), '#skF_4'(A_534, B_535, '#skF_6')), '#skF_6') | r2_hidden(k4_tarski('#skF_1'(A_534, B_535, '#skF_6'), '#skF_2'(A_534, B_535, '#skF_6')), B_535) | k8_relat_1(A_534, B_535)='#skF_6' | ~v1_relat_1(B_535))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_3247, c_3247, c_3247, c_32, c_3247, c_3247, c_7134])).
% 13.60/4.52  tff(c_7694, plain, (![A_536, B_537]: (r2_hidden('#skF_1'(A_536, B_537, '#skF_6'), k1_relat_1(B_537)) | ~v1_funct_1(B_537) | r2_hidden(k4_tarski('#skF_3'(A_536, B_537, '#skF_6'), '#skF_4'(A_536, B_537, '#skF_6')), '#skF_6') | k8_relat_1(A_536, B_537)='#skF_6' | ~v1_relat_1(B_537))), inference(resolution, [status(thm)], [c_7625, c_24])).
% 13.60/4.52  tff(c_7720, plain, (![A_536, B_537]: (k1_funct_1('#skF_6', '#skF_3'(A_536, B_537, '#skF_6'))='#skF_4'(A_536, B_537, '#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | r2_hidden('#skF_1'(A_536, B_537, '#skF_6'), k1_relat_1(B_537)) | ~v1_funct_1(B_537) | k8_relat_1(A_536, B_537)='#skF_6' | ~v1_relat_1(B_537))), inference(resolution, [status(thm)], [c_7694, c_22])).
% 13.60/4.52  tff(c_7745, plain, (![A_536, B_537]: (k1_funct_1('#skF_6', '#skF_3'(A_536, B_537, '#skF_6'))='#skF_4'(A_536, B_537, '#skF_6') | r2_hidden('#skF_1'(A_536, B_537, '#skF_6'), k1_relat_1(B_537)) | ~v1_funct_1(B_537) | k8_relat_1(A_536, B_537)='#skF_6' | ~v1_relat_1(B_537))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_7720])).
% 13.60/4.52  tff(c_8146, plain, (![B_554, A_555]: (k1_funct_1(B_554, '#skF_1'(A_555, B_554, '#skF_6'))='#skF_2'(A_555, B_554, '#skF_6') | ~v1_funct_1(B_554) | r2_hidden(k4_tarski('#skF_3'(A_555, B_554, '#skF_6'), '#skF_4'(A_555, B_554, '#skF_6')), '#skF_6') | k8_relat_1(A_555, B_554)='#skF_6' | ~v1_relat_1(B_554))), inference(resolution, [status(thm)], [c_7625, c_22])).
% 13.60/4.52  tff(c_8176, plain, (![A_555, B_554]: (k1_funct_1('#skF_6', '#skF_3'(A_555, B_554, '#skF_6'))='#skF_4'(A_555, B_554, '#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | k1_funct_1(B_554, '#skF_1'(A_555, B_554, '#skF_6'))='#skF_2'(A_555, B_554, '#skF_6') | ~v1_funct_1(B_554) | k8_relat_1(A_555, B_554)='#skF_6' | ~v1_relat_1(B_554))), inference(resolution, [status(thm)], [c_8146, c_22])).
% 13.60/4.52  tff(c_8297, plain, (![A_558, B_559]: (k1_funct_1('#skF_6', '#skF_3'(A_558, B_559, '#skF_6'))='#skF_4'(A_558, B_559, '#skF_6') | k1_funct_1(B_559, '#skF_1'(A_558, B_559, '#skF_6'))='#skF_2'(A_558, B_559, '#skF_6') | ~v1_funct_1(B_559) | k8_relat_1(A_558, B_559)='#skF_6' | ~v1_relat_1(B_559))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_8176])).
% 13.60/4.52  tff(c_138, plain, (![D_35]: (k8_relat_1('#skF_5', '#skF_7')='#skF_6' | r2_hidden(D_35, k1_relat_1('#skF_6')) | ~r2_hidden(k1_funct_1('#skF_7', D_35), '#skF_5') | ~r2_hidden(D_35, k1_relat_1('#skF_7')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.60/4.52  tff(c_2356, plain, (![D_35]: (r2_hidden(D_35, k1_relat_1('#skF_6')) | ~r2_hidden(k1_funct_1('#skF_7', D_35), '#skF_5') | ~r2_hidden(D_35, k1_relat_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_2323, c_138])).
% 13.60/4.52  tff(c_8391, plain, (![A_558]: (r2_hidden('#skF_1'(A_558, '#skF_7', '#skF_6'), k1_relat_1('#skF_6')) | ~r2_hidden('#skF_2'(A_558, '#skF_7', '#skF_6'), '#skF_5') | ~r2_hidden('#skF_1'(A_558, '#skF_7', '#skF_6'), k1_relat_1('#skF_7')) | k1_funct_1('#skF_6', '#skF_3'(A_558, '#skF_7', '#skF_6'))='#skF_4'(A_558, '#skF_7', '#skF_6') | ~v1_funct_1('#skF_7') | k8_relat_1(A_558, '#skF_7')='#skF_6' | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_8297, c_2356])).
% 13.60/4.52  tff(c_11120, plain, (![A_654]: (r2_hidden('#skF_1'(A_654, '#skF_7', '#skF_6'), k1_relat_1('#skF_6')) | ~r2_hidden('#skF_2'(A_654, '#skF_7', '#skF_6'), '#skF_5') | ~r2_hidden('#skF_1'(A_654, '#skF_7', '#skF_6'), k1_relat_1('#skF_7')) | k1_funct_1('#skF_6', '#skF_3'(A_654, '#skF_7', '#skF_6'))='#skF_4'(A_654, '#skF_7', '#skF_6') | k8_relat_1(A_654, '#skF_7')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_8391])).
% 13.60/4.52  tff(c_11124, plain, (![A_536]: (r2_hidden('#skF_1'(A_536, '#skF_7', '#skF_6'), k1_relat_1('#skF_6')) | ~r2_hidden('#skF_2'(A_536, '#skF_7', '#skF_6'), '#skF_5') | k1_funct_1('#skF_6', '#skF_3'(A_536, '#skF_7', '#skF_6'))='#skF_4'(A_536, '#skF_7', '#skF_6') | ~v1_funct_1('#skF_7') | k8_relat_1(A_536, '#skF_7')='#skF_6' | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_7745, c_11120])).
% 13.60/4.52  tff(c_11160, plain, (![A_655]: (r2_hidden('#skF_1'(A_655, '#skF_7', '#skF_6'), k1_relat_1('#skF_6')) | ~r2_hidden('#skF_2'(A_655, '#skF_7', '#skF_6'), '#skF_5') | k1_funct_1('#skF_6', '#skF_3'(A_655, '#skF_7', '#skF_6'))='#skF_4'(A_655, '#skF_7', '#skF_6') | k8_relat_1(A_655, '#skF_7')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_11124])).
% 13.60/4.52  tff(c_11181, plain, (![A_656]: (k1_funct_1('#skF_7', '#skF_1'(A_656, '#skF_7', '#skF_6'))=k1_funct_1('#skF_6', '#skF_1'(A_656, '#skF_7', '#skF_6')) | ~r2_hidden('#skF_2'(A_656, '#skF_7', '#skF_6'), '#skF_5') | k1_funct_1('#skF_6', '#skF_3'(A_656, '#skF_7', '#skF_6'))='#skF_4'(A_656, '#skF_7', '#skF_6') | k8_relat_1(A_656, '#skF_7')='#skF_6')), inference(resolution, [status(thm)], [c_11160, c_2339])).
% 13.60/4.52  tff(c_11185, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_5', '#skF_7', '#skF_6'))=k1_funct_1('#skF_6', '#skF_1'('#skF_5', '#skF_7', '#skF_6')) | k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_7', '#skF_6'))='#skF_4'('#skF_5', '#skF_7', '#skF_6') | k8_relat_1('#skF_5', '#skF_7')='#skF_6' | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_6348, c_11181])).
% 13.60/4.52  tff(c_11202, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_5', '#skF_7', '#skF_6'))=k1_funct_1('#skF_6', '#skF_1'('#skF_5', '#skF_7', '#skF_6')) | k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_7', '#skF_6'))='#skF_4'('#skF_5', '#skF_7', '#skF_6') | k8_relat_1('#skF_5', '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_11185])).
% 13.60/4.52  tff(c_11203, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_5', '#skF_7', '#skF_6'))=k1_funct_1('#skF_6', '#skF_1'('#skF_5', '#skF_7', '#skF_6')) | k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_7', '#skF_6'))='#skF_4'('#skF_5', '#skF_7', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_2323, c_11202])).
% 13.60/4.52  tff(c_11212, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_7', '#skF_6'))='#skF_4'('#skF_5', '#skF_7', '#skF_6')), inference(splitLeft, [status(thm)], [c_11203])).
% 13.60/4.52  tff(c_2362, plain, (![E_243, A_244, D_245, B_246]: (r2_hidden(E_243, A_244) | ~r2_hidden(k4_tarski(D_245, E_243), k8_relat_1(A_244, B_246)) | ~v1_relat_1(k8_relat_1(A_244, B_246)) | ~v1_relat_1(B_246))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.60/4.52  tff(c_2367, plain, (![A_244, B_246, A_19]: (r2_hidden(k1_funct_1(k8_relat_1(A_244, B_246), A_19), A_244) | ~v1_relat_1(B_246) | ~r2_hidden(A_19, k1_relat_1(k8_relat_1(A_244, B_246))) | ~v1_funct_1(k8_relat_1(A_244, B_246)) | ~v1_relat_1(k8_relat_1(A_244, B_246)))), inference(resolution, [status(thm)], [c_20, c_2362])).
% 13.60/4.52  tff(c_3263, plain, (![A_19]: (r2_hidden(k1_funct_1('#skF_6', A_19), '#skF_5') | ~v1_relat_1('#skF_6') | ~r2_hidden(A_19, k1_relat_1(k8_relat_1('#skF_5', '#skF_6'))) | ~v1_funct_1(k8_relat_1('#skF_5', '#skF_6')) | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_3247, c_2367])).
% 13.60/4.52  tff(c_3284, plain, (![A_19]: (r2_hidden(k1_funct_1('#skF_6', A_19), '#skF_5') | ~r2_hidden(A_19, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_3247, c_30, c_3247, c_3247, c_32, c_3263])).
% 13.60/4.52  tff(c_11227, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_7', '#skF_6'), '#skF_5') | ~r2_hidden('#skF_3'('#skF_5', '#skF_7', '#skF_6'), k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_11212, c_3284])).
% 13.60/4.52  tff(c_11584, plain, (~r2_hidden('#skF_3'('#skF_5', '#skF_7', '#skF_6'), k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_11227])).
% 13.60/4.52  tff(c_2435, plain, (![A_262, B_263, C_264]: (r2_hidden('#skF_3'(A_262, B_263, C_264), k1_relat_1(C_264)) | ~v1_funct_1(C_264) | r2_hidden('#skF_2'(A_262, B_263, C_264), A_262) | k8_relat_1(A_262, B_263)=C_264 | ~v1_relat_1(C_264) | ~v1_relat_1(B_263))), inference(resolution, [status(thm)], [c_2409, c_24])).
% 13.60/4.52  tff(c_11597, plain, (~v1_funct_1('#skF_6') | r2_hidden('#skF_2'('#skF_5', '#skF_7', '#skF_6'), '#skF_5') | k8_relat_1('#skF_5', '#skF_7')='#skF_6' | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_2435, c_11584])).
% 13.60/4.52  tff(c_11612, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_7', '#skF_6'), '#skF_5') | k8_relat_1('#skF_5', '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_30, c_11597])).
% 13.60/4.52  tff(c_11613, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_7', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_2323, c_11612])).
% 13.60/4.52  tff(c_7723, plain, (![A_536, B_537]: (r2_hidden('#skF_3'(A_536, B_537, '#skF_6'), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | r2_hidden('#skF_1'(A_536, B_537, '#skF_6'), k1_relat_1(B_537)) | ~v1_funct_1(B_537) | k8_relat_1(A_536, B_537)='#skF_6' | ~v1_relat_1(B_537))), inference(resolution, [status(thm)], [c_7694, c_24])).
% 13.60/4.52  tff(c_7748, plain, (![A_536, B_537]: (r2_hidden('#skF_3'(A_536, B_537, '#skF_6'), k1_relat_1('#skF_6')) | r2_hidden('#skF_1'(A_536, B_537, '#skF_6'), k1_relat_1(B_537)) | ~v1_funct_1(B_537) | k8_relat_1(A_536, B_537)='#skF_6' | ~v1_relat_1(B_537))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_7723])).
% 13.60/4.52  tff(c_2830, plain, (![A_303, B_304, C_305]: (r2_hidden('#skF_3'(A_303, B_304, C_305), k1_relat_1(C_305)) | ~v1_funct_1(C_305) | r2_hidden(k4_tarski('#skF_1'(A_303, B_304, C_305), '#skF_2'(A_303, B_304, C_305)), B_304) | k8_relat_1(A_303, B_304)=C_305 | ~v1_relat_1(C_305) | ~v1_relat_1(B_304))), inference(resolution, [status(thm)], [c_2663, c_24])).
% 13.60/4.52  tff(c_2868, plain, (![B_304, A_303, C_305]: (k1_funct_1(B_304, '#skF_1'(A_303, B_304, C_305))='#skF_2'(A_303, B_304, C_305) | ~v1_funct_1(B_304) | r2_hidden('#skF_3'(A_303, B_304, C_305), k1_relat_1(C_305)) | ~v1_funct_1(C_305) | k8_relat_1(A_303, B_304)=C_305 | ~v1_relat_1(C_305) | ~v1_relat_1(B_304))), inference(resolution, [status(thm)], [c_2830, c_22])).
% 13.60/4.52  tff(c_11593, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_5', '#skF_7', '#skF_6'))='#skF_2'('#skF_5', '#skF_7', '#skF_6') | ~v1_funct_1('#skF_7') | ~v1_funct_1('#skF_6') | k8_relat_1('#skF_5', '#skF_7')='#skF_6' | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_2868, c_11584])).
% 13.60/4.52  tff(c_11608, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_5', '#skF_7', '#skF_6'))='#skF_2'('#skF_5', '#skF_7', '#skF_6') | k8_relat_1('#skF_5', '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_30, c_26, c_11593])).
% 13.60/4.52  tff(c_11609, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_5', '#skF_7', '#skF_6'))='#skF_2'('#skF_5', '#skF_7', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_2323, c_11608])).
% 13.60/4.52  tff(c_11648, plain, (r2_hidden('#skF_1'('#skF_5', '#skF_7', '#skF_6'), k1_relat_1('#skF_6')) | ~r2_hidden('#skF_2'('#skF_5', '#skF_7', '#skF_6'), '#skF_5') | ~r2_hidden('#skF_1'('#skF_5', '#skF_7', '#skF_6'), k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_11609, c_2356])).
% 13.60/4.52  tff(c_11686, plain, (r2_hidden('#skF_1'('#skF_5', '#skF_7', '#skF_6'), k1_relat_1('#skF_6')) | ~r2_hidden('#skF_1'('#skF_5', '#skF_7', '#skF_6'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_11613, c_11648])).
% 13.60/4.52  tff(c_11704, plain, (~r2_hidden('#skF_1'('#skF_5', '#skF_7', '#skF_6'), k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_11686])).
% 13.60/4.52  tff(c_11710, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_7', '#skF_6'), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_7') | k8_relat_1('#skF_5', '#skF_7')='#skF_6' | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_7748, c_11704])).
% 13.60/4.52  tff(c_11729, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_7', '#skF_6'), k1_relat_1('#skF_6')) | k8_relat_1('#skF_5', '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_11710])).
% 13.60/4.52  tff(c_11731, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2323, c_11584, c_11729])).
% 13.60/4.52  tff(c_11732, plain, (r2_hidden('#skF_1'('#skF_5', '#skF_7', '#skF_6'), k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_11686])).
% 13.60/4.52  tff(c_11748, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_5', '#skF_7', '#skF_6'))=k1_funct_1('#skF_6', '#skF_1'('#skF_5', '#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_11732, c_2339])).
% 13.60/4.52  tff(c_11762, plain, (k1_funct_1('#skF_6', '#skF_1'('#skF_5', '#skF_7', '#skF_6'))='#skF_2'('#skF_5', '#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11609, c_11748])).
% 13.60/4.52  tff(c_2369, plain, (![D_247, E_248, B_249, A_250]: (r2_hidden(k4_tarski(D_247, E_248), B_249) | ~r2_hidden(k4_tarski(D_247, E_248), k8_relat_1(A_250, B_249)) | ~v1_relat_1(k8_relat_1(A_250, B_249)) | ~v1_relat_1(B_249))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.60/4.52  tff(c_2374, plain, (![A_19, A_250, B_249]: (r2_hidden(k4_tarski(A_19, k1_funct_1(k8_relat_1(A_250, B_249), A_19)), B_249) | ~v1_relat_1(B_249) | ~r2_hidden(A_19, k1_relat_1(k8_relat_1(A_250, B_249))) | ~v1_funct_1(k8_relat_1(A_250, B_249)) | ~v1_relat_1(k8_relat_1(A_250, B_249)))), inference(resolution, [status(thm)], [c_20, c_2369])).
% 13.60/4.52  tff(c_3260, plain, (![A_19]: (r2_hidden(k4_tarski(A_19, k1_funct_1('#skF_6', A_19)), '#skF_6') | ~v1_relat_1('#skF_6') | ~r2_hidden(A_19, k1_relat_1(k8_relat_1('#skF_5', '#skF_6'))) | ~v1_funct_1(k8_relat_1('#skF_5', '#skF_6')) | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_3247, c_2374])).
% 13.60/4.52  tff(c_3282, plain, (![A_19]: (r2_hidden(k4_tarski(A_19, k1_funct_1('#skF_6', A_19)), '#skF_6') | ~r2_hidden(A_19, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_3247, c_30, c_3247, c_3247, c_32, c_3260])).
% 13.60/4.52  tff(c_11929, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_5', '#skF_7', '#skF_6'), '#skF_2'('#skF_5', '#skF_7', '#skF_6')), '#skF_6') | ~r2_hidden('#skF_1'('#skF_5', '#skF_7', '#skF_6'), k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_11762, c_3282])).
% 13.60/4.52  tff(c_11946, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_5', '#skF_7', '#skF_6'), '#skF_2'('#skF_5', '#skF_7', '#skF_6')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11732, c_11929])).
% 13.60/4.52  tff(c_14, plain, (![D_17, E_18, A_1, B_2]: (r2_hidden(k4_tarski(D_17, E_18), k8_relat_1(A_1, B_2)) | ~r2_hidden(k4_tarski(D_17, E_18), B_2) | ~r2_hidden(E_18, A_1) | ~v1_relat_1(k8_relat_1(A_1, B_2)) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.60/4.52  tff(c_8951, plain, (![A_587, B_588, A_589, B_590]: (r2_hidden(k4_tarski('#skF_3'(A_587, B_588, k8_relat_1(A_589, B_590)), '#skF_4'(A_587, B_588, k8_relat_1(A_589, B_590))), k8_relat_1(A_589, B_590)) | k8_relat_1(A_589, B_590)=k8_relat_1(A_587, B_588) | ~v1_relat_1(B_588) | ~r2_hidden(k4_tarski('#skF_1'(A_587, B_588, k8_relat_1(A_589, B_590)), '#skF_2'(A_587, B_588, k8_relat_1(A_589, B_590))), B_590) | ~r2_hidden('#skF_2'(A_587, B_588, k8_relat_1(A_589, B_590)), A_589) | ~v1_relat_1(k8_relat_1(A_589, B_590)) | ~v1_relat_1(B_590))), inference(resolution, [status(thm)], [c_14, c_2991])).
% 13.60/4.52  tff(c_9012, plain, (![A_587, B_588]: (r2_hidden(k4_tarski('#skF_3'(A_587, B_588, k8_relat_1('#skF_5', '#skF_6')), '#skF_4'(A_587, B_588, k8_relat_1('#skF_5', '#skF_6'))), '#skF_6') | k8_relat_1(A_587, B_588)=k8_relat_1('#skF_5', '#skF_6') | ~v1_relat_1(B_588) | ~r2_hidden(k4_tarski('#skF_1'(A_587, B_588, k8_relat_1('#skF_5', '#skF_6')), '#skF_2'(A_587, B_588, k8_relat_1('#skF_5', '#skF_6'))), '#skF_6') | ~r2_hidden('#skF_2'(A_587, B_588, k8_relat_1('#skF_5', '#skF_6')), '#skF_5') | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_6')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3247, c_8951])).
% 13.60/4.52  tff(c_9031, plain, (![A_587, B_588]: (r2_hidden(k4_tarski('#skF_3'(A_587, B_588, '#skF_6'), '#skF_4'(A_587, B_588, '#skF_6')), '#skF_6') | k8_relat_1(A_587, B_588)='#skF_6' | ~v1_relat_1(B_588) | ~r2_hidden(k4_tarski('#skF_1'(A_587, B_588, '#skF_6'), '#skF_2'(A_587, B_588, '#skF_6')), '#skF_6') | ~r2_hidden('#skF_2'(A_587, B_588, '#skF_6'), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_32, c_3247, c_3247, c_3247, c_3247, c_3247, c_3247, c_3247, c_9012])).
% 13.60/4.52  tff(c_11960, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_5', '#skF_7', '#skF_6'), '#skF_4'('#skF_5', '#skF_7', '#skF_6')), '#skF_6') | k8_relat_1('#skF_5', '#skF_7')='#skF_6' | ~v1_relat_1('#skF_7') | ~r2_hidden('#skF_2'('#skF_5', '#skF_7', '#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_11946, c_9031])).
% 13.60/4.52  tff(c_11983, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_5', '#skF_7', '#skF_6'), '#skF_4'('#skF_5', '#skF_7', '#skF_6')), '#skF_6') | k8_relat_1('#skF_5', '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_11613, c_28, c_11960])).
% 13.60/4.52  tff(c_11984, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_5', '#skF_7', '#skF_6'), '#skF_4'('#skF_5', '#skF_7', '#skF_6')), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_2323, c_11983])).
% 13.60/4.52  tff(c_12023, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_7', '#skF_6'), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_11984, c_24])).
% 13.60/4.52  tff(c_12038, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_7', '#skF_6'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_12023])).
% 13.60/4.52  tff(c_12040, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11584, c_12038])).
% 13.60/4.52  tff(c_12041, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_7', '#skF_6'), '#skF_5')), inference(splitRight, [status(thm)], [c_11227])).
% 13.60/4.52  tff(c_12042, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_7', '#skF_6'), k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_11227])).
% 13.60/4.52  tff(c_2322, plain, (![D_35]: (r2_hidden(D_35, k1_relat_1('#skF_7')) | ~r2_hidden(D_35, k1_relat_1('#skF_6')))), inference(splitRight, [status(thm)], [c_112])).
% 13.60/4.52  tff(c_12055, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_5', '#skF_7', '#skF_6'))=k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_12042, c_2339])).
% 13.60/4.52  tff(c_12059, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_5', '#skF_7', '#skF_6'))='#skF_4'('#skF_5', '#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11212, c_12055])).
% 13.60/4.52  tff(c_12073, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_5', '#skF_7', '#skF_6'), '#skF_4'('#skF_5', '#skF_7', '#skF_6')), '#skF_7') | ~r2_hidden('#skF_3'('#skF_5', '#skF_7', '#skF_6'), k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_12059, c_20])).
% 13.60/4.52  tff(c_12087, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_5', '#skF_7', '#skF_6'), '#skF_4'('#skF_5', '#skF_7', '#skF_6')), '#skF_7') | ~r2_hidden('#skF_3'('#skF_5', '#skF_7', '#skF_6'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_12073])).
% 13.60/4.52  tff(c_12608, plain, (~r2_hidden('#skF_3'('#skF_5', '#skF_7', '#skF_6'), k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_12087])).
% 13.60/4.52  tff(c_12611, plain, (~r2_hidden('#skF_3'('#skF_5', '#skF_7', '#skF_6'), k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_2322, c_12608])).
% 13.60/4.52  tff(c_12615, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12042, c_12611])).
% 13.60/4.52  tff(c_12616, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_5', '#skF_7', '#skF_6'), '#skF_4'('#skF_5', '#skF_7', '#skF_6')), '#skF_7')), inference(splitRight, [status(thm)], [c_12087])).
% 13.60/4.52  tff(c_3521, plain, (![A_345, B_346, C_347]: (r2_hidden(k4_tarski('#skF_1'(A_345, B_346, C_347), '#skF_2'(A_345, B_346, C_347)), B_346) | ~r2_hidden(k4_tarski('#skF_3'(A_345, B_346, C_347), '#skF_4'(A_345, B_346, C_347)), B_346) | ~r2_hidden('#skF_4'(A_345, B_346, C_347), A_345) | k8_relat_1(A_345, B_346)=C_347 | ~v1_relat_1(C_347) | ~v1_relat_1(B_346))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.60/4.52  tff(c_3572, plain, (![A_345, B_346, C_347]: (r2_hidden('#skF_1'(A_345, B_346, C_347), k1_relat_1(B_346)) | ~v1_funct_1(B_346) | ~r2_hidden(k4_tarski('#skF_3'(A_345, B_346, C_347), '#skF_4'(A_345, B_346, C_347)), B_346) | ~r2_hidden('#skF_4'(A_345, B_346, C_347), A_345) | k8_relat_1(A_345, B_346)=C_347 | ~v1_relat_1(C_347) | ~v1_relat_1(B_346))), inference(resolution, [status(thm)], [c_3521, c_24])).
% 13.60/4.52  tff(c_12634, plain, (r2_hidden('#skF_1'('#skF_5', '#skF_7', '#skF_6'), k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~r2_hidden('#skF_4'('#skF_5', '#skF_7', '#skF_6'), '#skF_5') | k8_relat_1('#skF_5', '#skF_7')='#skF_6' | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_12616, c_3572])).
% 13.60/4.52  tff(c_12656, plain, (r2_hidden('#skF_1'('#skF_5', '#skF_7', '#skF_6'), k1_relat_1('#skF_7')) | k8_relat_1('#skF_5', '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_12041, c_26, c_12634])).
% 13.60/4.52  tff(c_12657, plain, (r2_hidden('#skF_1'('#skF_5', '#skF_7', '#skF_6'), k1_relat_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_2323, c_12656])).
% 13.60/4.52  tff(c_6, plain, (![A_1, B_2, C_12]: (r2_hidden('#skF_2'(A_1, B_2, C_12), A_1) | ~r2_hidden(k4_tarski('#skF_3'(A_1, B_2, C_12), '#skF_4'(A_1, B_2, C_12)), B_2) | ~r2_hidden('#skF_4'(A_1, B_2, C_12), A_1) | k8_relat_1(A_1, B_2)=C_12 | ~v1_relat_1(C_12) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.60/4.52  tff(c_12637, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_7', '#skF_6'), '#skF_5') | ~r2_hidden('#skF_4'('#skF_5', '#skF_7', '#skF_6'), '#skF_5') | k8_relat_1('#skF_5', '#skF_7')='#skF_6' | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_12616, c_6])).
% 13.60/4.52  tff(c_12660, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_7', '#skF_6'), '#skF_5') | k8_relat_1('#skF_5', '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_12041, c_12637])).
% 13.60/4.52  tff(c_12661, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_7', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_2323, c_12660])).
% 13.60/4.52  tff(c_3571, plain, (![B_346, A_345, C_347]: (k1_funct_1(B_346, '#skF_1'(A_345, B_346, C_347))='#skF_2'(A_345, B_346, C_347) | ~v1_funct_1(B_346) | ~r2_hidden(k4_tarski('#skF_3'(A_345, B_346, C_347), '#skF_4'(A_345, B_346, C_347)), B_346) | ~r2_hidden('#skF_4'(A_345, B_346, C_347), A_345) | k8_relat_1(A_345, B_346)=C_347 | ~v1_relat_1(C_347) | ~v1_relat_1(B_346))), inference(resolution, [status(thm)], [c_3521, c_22])).
% 13.60/4.52  tff(c_12631, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_5', '#skF_7', '#skF_6'))='#skF_2'('#skF_5', '#skF_7', '#skF_6') | ~v1_funct_1('#skF_7') | ~r2_hidden('#skF_4'('#skF_5', '#skF_7', '#skF_6'), '#skF_5') | k8_relat_1('#skF_5', '#skF_7')='#skF_6' | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_12616, c_3571])).
% 13.60/4.52  tff(c_12652, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_5', '#skF_7', '#skF_6'))='#skF_2'('#skF_5', '#skF_7', '#skF_6') | k8_relat_1('#skF_5', '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_12041, c_26, c_12631])).
% 13.60/4.52  tff(c_12653, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_5', '#skF_7', '#skF_6'))='#skF_2'('#skF_5', '#skF_7', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_2323, c_12652])).
% 13.60/4.52  tff(c_12713, plain, (r2_hidden('#skF_1'('#skF_5', '#skF_7', '#skF_6'), k1_relat_1('#skF_6')) | ~r2_hidden('#skF_2'('#skF_5', '#skF_7', '#skF_6'), '#skF_5') | ~r2_hidden('#skF_1'('#skF_5', '#skF_7', '#skF_6'), k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_12653, c_2356])).
% 13.60/4.52  tff(c_12751, plain, (r2_hidden('#skF_1'('#skF_5', '#skF_7', '#skF_6'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_12657, c_12661, c_12713])).
% 13.60/4.52  tff(c_12850, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_5', '#skF_7', '#skF_6'))=k1_funct_1('#skF_6', '#skF_1'('#skF_5', '#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_12751, c_2339])).
% 13.60/4.52  tff(c_12864, plain, (k1_funct_1('#skF_6', '#skF_1'('#skF_5', '#skF_7', '#skF_6'))='#skF_2'('#skF_5', '#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_12653, c_12850])).
% 13.60/4.52  tff(c_12874, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_5', '#skF_7', '#skF_6'), '#skF_2'('#skF_5', '#skF_7', '#skF_6')), '#skF_6') | ~r2_hidden('#skF_1'('#skF_5', '#skF_7', '#skF_6'), k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_12864, c_3282])).
% 13.60/4.52  tff(c_12891, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_5', '#skF_7', '#skF_6'), '#skF_2'('#skF_5', '#skF_7', '#skF_6')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_12751, c_12874])).
% 13.60/4.52  tff(c_2, plain, (![A_1, B_2, C_12]: (~r2_hidden(k4_tarski('#skF_1'(A_1, B_2, C_12), '#skF_2'(A_1, B_2, C_12)), C_12) | ~r2_hidden(k4_tarski('#skF_3'(A_1, B_2, C_12), '#skF_4'(A_1, B_2, C_12)), B_2) | ~r2_hidden('#skF_4'(A_1, B_2, C_12), A_1) | k8_relat_1(A_1, B_2)=C_12 | ~v1_relat_1(C_12) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.60/4.52  tff(c_12936, plain, (~r2_hidden(k4_tarski('#skF_3'('#skF_5', '#skF_7', '#skF_6'), '#skF_4'('#skF_5', '#skF_7', '#skF_6')), '#skF_7') | ~r2_hidden('#skF_4'('#skF_5', '#skF_7', '#skF_6'), '#skF_5') | k8_relat_1('#skF_5', '#skF_7')='#skF_6' | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_12891, c_2])).
% 13.60/4.52  tff(c_12961, plain, (k8_relat_1('#skF_5', '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_12041, c_12616, c_12936])).
% 13.60/4.52  tff(c_12963, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2323, c_12961])).
% 13.60/4.52  tff(c_12965, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_7', '#skF_6'))!='#skF_4'('#skF_5', '#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_11203])).
% 13.60/4.52  tff(c_11146, plain, (![A_536]: (r2_hidden('#skF_1'(A_536, '#skF_7', '#skF_6'), k1_relat_1('#skF_6')) | ~r2_hidden('#skF_2'(A_536, '#skF_7', '#skF_6'), '#skF_5') | k1_funct_1('#skF_6', '#skF_3'(A_536, '#skF_7', '#skF_6'))='#skF_4'(A_536, '#skF_7', '#skF_6') | k8_relat_1(A_536, '#skF_7')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_11124])).
% 13.60/4.52  tff(c_12964, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_5', '#skF_7', '#skF_6'))=k1_funct_1('#skF_6', '#skF_1'('#skF_5', '#skF_7', '#skF_6'))), inference(splitRight, [status(thm)], [c_11203])).
% 13.60/4.52  tff(c_8204, plain, (![A_555, B_554]: (k1_funct_1('#skF_6', '#skF_3'(A_555, B_554, '#skF_6'))='#skF_4'(A_555, B_554, '#skF_6') | k1_funct_1(B_554, '#skF_1'(A_555, B_554, '#skF_6'))='#skF_2'(A_555, B_554, '#skF_6') | ~v1_funct_1(B_554) | k8_relat_1(A_555, B_554)='#skF_6' | ~v1_relat_1(B_554))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_8176])).
% 13.60/4.52  tff(c_12973, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_7', '#skF_6'))='#skF_4'('#skF_5', '#skF_7', '#skF_6') | k1_funct_1('#skF_6', '#skF_1'('#skF_5', '#skF_7', '#skF_6'))='#skF_2'('#skF_5', '#skF_7', '#skF_6') | ~v1_funct_1('#skF_7') | k8_relat_1('#skF_5', '#skF_7')='#skF_6' | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_12964, c_8204])).
% 13.60/4.52  tff(c_13013, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_7', '#skF_6'))='#skF_4'('#skF_5', '#skF_7', '#skF_6') | k1_funct_1('#skF_6', '#skF_1'('#skF_5', '#skF_7', '#skF_6'))='#skF_2'('#skF_5', '#skF_7', '#skF_6') | k8_relat_1('#skF_5', '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_12973])).
% 13.60/4.52  tff(c_13014, plain, (k1_funct_1('#skF_6', '#skF_1'('#skF_5', '#skF_7', '#skF_6'))='#skF_2'('#skF_5', '#skF_7', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_2323, c_12965, c_13013])).
% 13.60/4.52  tff(c_13037, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_5', '#skF_7', '#skF_6'))='#skF_2'('#skF_5', '#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_13014, c_12964])).
% 13.60/4.52  tff(c_13244, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_7', '#skF_6'), '#skF_5') | ~r2_hidden('#skF_1'('#skF_5', '#skF_7', '#skF_6'), k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_13037, c_2325])).
% 13.60/4.52  tff(c_13291, plain, (~r2_hidden('#skF_1'('#skF_5', '#skF_7', '#skF_6'), k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_13244])).
% 13.60/4.52  tff(c_13294, plain, (~r2_hidden('#skF_2'('#skF_5', '#skF_7', '#skF_6'), '#skF_5') | k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_7', '#skF_6'))='#skF_4'('#skF_5', '#skF_7', '#skF_6') | k8_relat_1('#skF_5', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_11146, c_13291])).
% 13.60/4.52  tff(c_13297, plain, (~r2_hidden('#skF_2'('#skF_5', '#skF_7', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_2323, c_12965, c_13294])).
% 13.60/4.52  tff(c_13300, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_7', '#skF_6'))='#skF_4'('#skF_5', '#skF_7', '#skF_6') | k8_relat_1('#skF_5', '#skF_7')='#skF_6' | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_6348, c_13297])).
% 13.60/4.52  tff(c_13312, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_7', '#skF_6'))='#skF_4'('#skF_5', '#skF_7', '#skF_6') | k8_relat_1('#skF_5', '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_13300])).
% 13.60/4.52  tff(c_13314, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2323, c_12965, c_13312])).
% 13.60/4.52  tff(c_13315, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_7', '#skF_6'), '#skF_5')), inference(splitRight, [status(thm)], [c_13244])).
% 13.60/4.52  tff(c_13316, plain, (r2_hidden('#skF_1'('#skF_5', '#skF_7', '#skF_6'), k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_13244])).
% 13.60/4.52  tff(c_13047, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_5', '#skF_7', '#skF_6'), '#skF_2'('#skF_5', '#skF_7', '#skF_6')), '#skF_6') | ~r2_hidden('#skF_1'('#skF_5', '#skF_7', '#skF_6'), k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_13014, c_3282])).
% 13.60/4.52  tff(c_13461, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_5', '#skF_7', '#skF_6'), '#skF_2'('#skF_5', '#skF_7', '#skF_6')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_13316, c_13047])).
% 13.60/4.52  tff(c_13466, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_5', '#skF_7', '#skF_6'), '#skF_4'('#skF_5', '#skF_7', '#skF_6')), '#skF_6') | k8_relat_1('#skF_5', '#skF_7')='#skF_6' | ~v1_relat_1('#skF_7') | ~r2_hidden('#skF_2'('#skF_5', '#skF_7', '#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_13461, c_9031])).
% 13.60/4.52  tff(c_13488, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_5', '#skF_7', '#skF_6'), '#skF_4'('#skF_5', '#skF_7', '#skF_6')), '#skF_6') | k8_relat_1('#skF_5', '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_13315, c_28, c_13466])).
% 13.60/4.52  tff(c_13489, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_5', '#skF_7', '#skF_6'), '#skF_4'('#skF_5', '#skF_7', '#skF_6')), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_2323, c_13488])).
% 13.60/4.52  tff(c_13523, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_7', '#skF_6'))='#skF_4'('#skF_5', '#skF_7', '#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_13489, c_22])).
% 13.60/4.52  tff(c_13537, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_5', '#skF_7', '#skF_6'))='#skF_4'('#skF_5', '#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_13523])).
% 13.60/4.52  tff(c_13539, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12965, c_13537])).
% 13.60/4.52  tff(c_13541, plain, (k8_relat_1('#skF_5', '#skF_6')!='#skF_6'), inference(splitRight, [status(thm)], [c_3244])).
% 13.60/4.52  tff(c_3013, plain, (![A_1, B_2]: (r2_hidden(k4_tarski('#skF_3'(A_1, B_2, B_2), '#skF_4'(A_1, B_2, B_2)), B_2) | k8_relat_1(A_1, B_2)=B_2 | ~v1_relat_1(B_2))), inference(resolution, [status(thm)], [c_10, c_2991])).
% 13.60/4.52  tff(c_13956, plain, (![A_708, B_709, C_710]: (r2_hidden(k4_tarski('#skF_1'(A_708, B_709, C_710), '#skF_2'(A_708, B_709, C_710)), B_709) | ~r2_hidden(k4_tarski('#skF_3'(A_708, B_709, C_710), '#skF_4'(A_708, B_709, C_710)), B_709) | ~r2_hidden('#skF_4'(A_708, B_709, C_710), A_708) | k8_relat_1(A_708, B_709)=C_710 | ~v1_relat_1(C_710) | ~v1_relat_1(B_709))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.60/4.52  tff(c_14005, plain, (![A_711, B_712]: (~r2_hidden(k4_tarski('#skF_3'(A_711, B_712, B_712), '#skF_4'(A_711, B_712, B_712)), B_712) | ~r2_hidden('#skF_4'(A_711, B_712, B_712), A_711) | k8_relat_1(A_711, B_712)=B_712 | ~v1_relat_1(B_712))), inference(resolution, [status(thm)], [c_13956, c_2])).
% 13.60/4.52  tff(c_14043, plain, (![A_713, B_714]: (~r2_hidden('#skF_4'(A_713, B_714, B_714), A_713) | k8_relat_1(A_713, B_714)=B_714 | ~v1_relat_1(B_714))), inference(resolution, [status(thm)], [c_3013, c_14005])).
% 13.60/4.52  tff(c_14051, plain, (~v1_relat_1('#skF_6') | k8_relat_1('#skF_5', '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_3186, c_14043])).
% 13.60/4.52  tff(c_14063, plain, (k8_relat_1('#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_14051])).
% 13.60/4.52  tff(c_14065, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13541, c_14063])).
% 13.60/4.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.60/4.52  
% 13.60/4.52  Inference rules
% 13.60/4.52  ----------------------
% 13.60/4.52  #Ref     : 0
% 13.60/4.52  #Sup     : 2739
% 13.60/4.52  #Fact    : 0
% 13.60/4.52  #Define  : 0
% 13.60/4.52  #Split   : 52
% 13.60/4.52  #Chain   : 0
% 13.60/4.52  #Close   : 0
% 13.60/4.52  
% 13.60/4.52  Ordering : KBO
% 13.60/4.52  
% 13.60/4.52  Simplification rules
% 13.60/4.52  ----------------------
% 13.60/4.52  #Subsume      : 634
% 13.60/4.52  #Demod        : 2570
% 13.60/4.52  #Tautology    : 596
% 13.60/4.52  #SimpNegUnit  : 119
% 13.60/4.52  #BackRed      : 1
% 13.60/4.52  
% 13.60/4.52  #Partial instantiations: 0
% 13.60/4.52  #Strategies tried      : 1
% 13.60/4.52  
% 13.60/4.52  Timing (in seconds)
% 13.60/4.52  ----------------------
% 13.60/4.53  Preprocessing        : 0.35
% 13.60/4.53  Parsing              : 0.16
% 13.60/4.53  CNF conversion       : 0.03
% 13.60/4.53  Main loop            : 3.25
% 13.60/4.53  Inferencing          : 1.04
% 13.60/4.53  Reduction            : 0.81
% 13.60/4.53  Demodulation         : 0.52
% 13.60/4.53  BG Simplification    : 0.15
% 13.60/4.53  Subsumption          : 1.04
% 13.60/4.53  Abstraction          : 0.20
% 13.60/4.53  MUC search           : 0.00
% 13.60/4.53  Cooper               : 0.00
% 13.60/4.53  Total                : 3.75
% 13.60/4.53  Index Insertion      : 0.00
% 13.60/4.53  Index Deletion       : 0.00
% 13.60/4.53  Index Matching       : 0.00
% 13.60/4.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
