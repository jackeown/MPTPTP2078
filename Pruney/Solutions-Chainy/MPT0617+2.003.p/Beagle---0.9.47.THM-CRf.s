%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:51 EST 2020

% Result     : Theorem 4.58s
% Output     : CNFRefutation 5.02s
% Verified   : 
% Statistics : Number of formulae       :  116 (1186 expanded)
%              Number of leaves         :   20 ( 419 expanded)
%              Depth                    :   31
%              Number of atoms          :  290 (4785 expanded)
%              Number of equality atoms :   85 (1555 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( k1_relat_1(A) = k1_relat_1(B)
                & ! [C] :
                    ( r2_hidden(C,k1_relat_1(A))
                   => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
             => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( A = B
          <=> ! [C,D] :
                ( r2_hidden(k4_tarski(C,D),A)
              <=> r2_hidden(k4_tarski(C,D),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(c_24,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_32,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_36,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_34,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_30,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_94,plain,(
    ! [A_53,B_54] :
      ( r2_hidden(k4_tarski('#skF_1'(A_53,B_54),'#skF_2'(A_53,B_54)),B_54)
      | r2_hidden(k4_tarski('#skF_3'(A_53,B_54),'#skF_4'(A_53,B_54)),A_53)
      | B_54 = A_53
      | ~ v1_relat_1(B_54)
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ! [C_23,A_21,B_22] :
      ( k1_funct_1(C_23,A_21) = B_22
      | ~ r2_hidden(k4_tarski(A_21,B_22),C_23)
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_761,plain,(
    ! [A_90,B_91] :
      ( k1_funct_1(A_90,'#skF_3'(A_90,B_91)) = '#skF_4'(A_90,B_91)
      | ~ v1_funct_1(A_90)
      | r2_hidden(k4_tarski('#skF_1'(A_90,B_91),'#skF_2'(A_90,B_91)),B_91)
      | B_91 = A_90
      | ~ v1_relat_1(B_91)
      | ~ v1_relat_1(A_90) ) ),
    inference(resolution,[status(thm)],[c_94,c_20])).

tff(c_1618,plain,(
    ! [B_112,A_113] :
      ( k1_funct_1(B_112,'#skF_1'(A_113,B_112)) = '#skF_2'(A_113,B_112)
      | ~ v1_funct_1(B_112)
      | k1_funct_1(A_113,'#skF_3'(A_113,B_112)) = '#skF_4'(A_113,B_112)
      | ~ v1_funct_1(A_113)
      | B_112 = A_113
      | ~ v1_relat_1(B_112)
      | ~ v1_relat_1(A_113) ) ),
    inference(resolution,[status(thm)],[c_761,c_20])).

tff(c_28,plain,(
    k1_relat_1('#skF_5') = k1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_16,plain,(
    ! [A_18,C_20,B_19] :
      ( r2_hidden(A_18,k1_relat_1(C_20))
      | ~ r2_hidden(k4_tarski(A_18,B_19),C_20)
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_240,plain,(
    ! [A_71,B_72] :
      ( r2_hidden('#skF_3'(A_71,B_72),k1_relat_1(A_71))
      | r2_hidden(k4_tarski('#skF_1'(A_71,B_72),'#skF_2'(A_71,B_72)),B_72)
      | B_72 = A_71
      | ~ v1_relat_1(B_72)
      | ~ v1_relat_1(A_71) ) ),
    inference(resolution,[status(thm)],[c_94,c_16])).

tff(c_274,plain,(
    ! [A_73,B_74] :
      ( r2_hidden('#skF_1'(A_73,B_74),k1_relat_1(B_74))
      | r2_hidden('#skF_3'(A_73,B_74),k1_relat_1(A_73))
      | B_74 = A_73
      | ~ v1_relat_1(B_74)
      | ~ v1_relat_1(A_73) ) ),
    inference(resolution,[status(thm)],[c_240,c_16])).

tff(c_26,plain,(
    ! [C_28] :
      ( k1_funct_1('#skF_5',C_28) = k1_funct_1('#skF_6',C_28)
      | ~ r2_hidden(C_28,k1_relat_1('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_37,plain,(
    ! [C_28] :
      ( k1_funct_1('#skF_5',C_28) = k1_funct_1('#skF_6',C_28)
      | ~ r2_hidden(C_28,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26])).

tff(c_280,plain,(
    ! [B_74] :
      ( k1_funct_1('#skF_5','#skF_3'('#skF_6',B_74)) = k1_funct_1('#skF_6','#skF_3'('#skF_6',B_74))
      | r2_hidden('#skF_1'('#skF_6',B_74),k1_relat_1(B_74))
      | B_74 = '#skF_6'
      | ~ v1_relat_1(B_74)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_274,c_37])).

tff(c_298,plain,(
    ! [B_76] :
      ( k1_funct_1('#skF_5','#skF_3'('#skF_6',B_76)) = k1_funct_1('#skF_6','#skF_3'('#skF_6',B_76))
      | r2_hidden('#skF_1'('#skF_6',B_76),k1_relat_1(B_76))
      | B_76 = '#skF_6'
      | ~ v1_relat_1(B_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_280])).

tff(c_305,plain,
    ( k1_funct_1('#skF_5','#skF_3'('#skF_6','#skF_5')) = k1_funct_1('#skF_6','#skF_3'('#skF_6','#skF_5'))
    | r2_hidden('#skF_1'('#skF_6','#skF_5'),k1_relat_1('#skF_6'))
    | '#skF_5' = '#skF_6'
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_298])).

tff(c_311,plain,
    ( k1_funct_1('#skF_5','#skF_3'('#skF_6','#skF_5')) = k1_funct_1('#skF_6','#skF_3'('#skF_6','#skF_5'))
    | r2_hidden('#skF_1'('#skF_6','#skF_5'),k1_relat_1('#skF_6'))
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_305])).

tff(c_312,plain,
    ( k1_funct_1('#skF_5','#skF_3'('#skF_6','#skF_5')) = k1_funct_1('#skF_6','#skF_3'('#skF_6','#skF_5'))
    | r2_hidden('#skF_1'('#skF_6','#skF_5'),k1_relat_1('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_311])).

tff(c_337,plain,(
    r2_hidden('#skF_1'('#skF_6','#skF_5'),k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_312])).

tff(c_341,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_5')) = k1_funct_1('#skF_6','#skF_1'('#skF_6','#skF_5')) ),
    inference(resolution,[status(thm)],[c_337,c_37])).

tff(c_1648,plain,
    ( k1_funct_1('#skF_6','#skF_1'('#skF_6','#skF_5')) = '#skF_2'('#skF_6','#skF_5')
    | ~ v1_funct_1('#skF_5')
    | k1_funct_1('#skF_6','#skF_3'('#skF_6','#skF_5')) = '#skF_4'('#skF_6','#skF_5')
    | ~ v1_funct_1('#skF_6')
    | '#skF_5' = '#skF_6'
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1618,c_341])).

tff(c_1752,plain,
    ( k1_funct_1('#skF_6','#skF_1'('#skF_6','#skF_5')) = '#skF_2'('#skF_6','#skF_5')
    | k1_funct_1('#skF_6','#skF_3'('#skF_6','#skF_5')) = '#skF_4'('#skF_6','#skF_5')
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_36,c_30,c_34,c_1648])).

tff(c_1753,plain,
    ( k1_funct_1('#skF_6','#skF_1'('#skF_6','#skF_5')) = '#skF_2'('#skF_6','#skF_5')
    | k1_funct_1('#skF_6','#skF_3'('#skF_6','#skF_5')) = '#skF_4'('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_1752])).

tff(c_1805,plain,(
    k1_funct_1('#skF_6','#skF_3'('#skF_6','#skF_5')) = '#skF_4'('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1753])).

tff(c_46,plain,(
    ! [A_39,C_40] :
      ( r2_hidden(k4_tarski(A_39,k1_funct_1(C_40,A_39)),C_40)
      | ~ r2_hidden(A_39,k1_relat_1(C_40))
      | ~ v1_funct_1(C_40)
      | ~ v1_relat_1(C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14,plain,(
    ! [B_19,C_20,A_18] :
      ( r2_hidden(B_19,k2_relat_1(C_20))
      | ~ r2_hidden(k4_tarski(A_18,B_19),C_20)
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_62,plain,(
    ! [C_40,A_39] :
      ( r2_hidden(k1_funct_1(C_40,A_39),k2_relat_1(C_40))
      | ~ r2_hidden(A_39,k1_relat_1(C_40))
      | ~ v1_funct_1(C_40)
      | ~ v1_relat_1(C_40) ) ),
    inference(resolution,[status(thm)],[c_46,c_14])).

tff(c_1814,plain,
    ( r2_hidden('#skF_4'('#skF_6','#skF_5'),k2_relat_1('#skF_6'))
    | ~ r2_hidden('#skF_3'('#skF_6','#skF_5'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1805,c_62])).

tff(c_1826,plain,
    ( r2_hidden('#skF_4'('#skF_6','#skF_5'),k2_relat_1('#skF_6'))
    | ~ r2_hidden('#skF_3'('#skF_6','#skF_5'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1814])).

tff(c_1830,plain,(
    ~ r2_hidden('#skF_3'('#skF_6','#skF_5'),k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1826])).

tff(c_270,plain,(
    ! [B_72,A_71] :
      ( k1_funct_1(B_72,'#skF_1'(A_71,B_72)) = '#skF_2'(A_71,B_72)
      | ~ v1_funct_1(B_72)
      | r2_hidden('#skF_3'(A_71,B_72),k1_relat_1(A_71))
      | B_72 = A_71
      | ~ v1_relat_1(B_72)
      | ~ v1_relat_1(A_71) ) ),
    inference(resolution,[status(thm)],[c_240,c_20])).

tff(c_1833,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_5')) = '#skF_2'('#skF_6','#skF_5')
    | ~ v1_funct_1('#skF_5')
    | '#skF_5' = '#skF_6'
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_270,c_1830])).

tff(c_1842,plain,
    ( k1_funct_1('#skF_6','#skF_1'('#skF_6','#skF_5')) = '#skF_2'('#skF_6','#skF_5')
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_36,c_34,c_341,c_1833])).

tff(c_1843,plain,(
    k1_funct_1('#skF_6','#skF_1'('#skF_6','#skF_5')) = '#skF_2'('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_1842])).

tff(c_18,plain,(
    ! [A_21,C_23] :
      ( r2_hidden(k4_tarski(A_21,k1_funct_1(C_23,A_21)),C_23)
      | ~ r2_hidden(A_21,k1_relat_1(C_23))
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1862,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_5'),'#skF_2'('#skF_6','#skF_5')),'#skF_6')
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_5'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1843,c_18])).

tff(c_1868,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_5'),'#skF_2'('#skF_6','#skF_5')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_337,c_1862])).

tff(c_67,plain,(
    ! [A_45,B_46] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_45,B_46),'#skF_2'(A_45,B_46)),A_45)
      | r2_hidden(k4_tarski('#skF_3'(A_45,B_46),'#skF_4'(A_45,B_46)),A_45)
      | B_46 = A_45
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_83,plain,(
    ! [A_45,B_46] :
      ( r2_hidden('#skF_3'(A_45,B_46),k1_relat_1(A_45))
      | ~ r2_hidden(k4_tarski('#skF_1'(A_45,B_46),'#skF_2'(A_45,B_46)),A_45)
      | B_46 = A_45
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1(A_45) ) ),
    inference(resolution,[status(thm)],[c_67,c_16])).

tff(c_1940,plain,
    ( r2_hidden('#skF_3'('#skF_6','#skF_5'),k1_relat_1('#skF_6'))
    | '#skF_5' = '#skF_6'
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1868,c_83])).

tff(c_1961,plain,
    ( r2_hidden('#skF_3'('#skF_6','#skF_5'),k1_relat_1('#skF_6'))
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_36,c_1940])).

tff(c_1963,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_1830,c_1961])).

tff(c_1965,plain,(
    r2_hidden('#skF_3'('#skF_6','#skF_5'),k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1826])).

tff(c_1968,plain,(
    k1_funct_1('#skF_5','#skF_3'('#skF_6','#skF_5')) = k1_funct_1('#skF_6','#skF_3'('#skF_6','#skF_5')) ),
    inference(resolution,[status(thm)],[c_1965,c_37])).

tff(c_1970,plain,(
    k1_funct_1('#skF_5','#skF_3'('#skF_6','#skF_5')) = '#skF_4'('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1805,c_1968])).

tff(c_1980,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_6','#skF_5'),'#skF_4'('#skF_6','#skF_5')),'#skF_5')
    | ~ r2_hidden('#skF_3'('#skF_6','#skF_5'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1970,c_18])).

tff(c_1992,plain,(
    r2_hidden(k4_tarski('#skF_3'('#skF_6','#skF_5'),'#skF_4'('#skF_6','#skF_5')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_1965,c_28,c_1980])).

tff(c_4,plain,(
    ! [A_1,B_11] :
      ( r2_hidden(k4_tarski('#skF_1'(A_1,B_11),'#skF_2'(A_1,B_11)),B_11)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_1,B_11),'#skF_4'(A_1,B_11)),B_11)
      | B_11 = A_1
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1999,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_5'),'#skF_2'('#skF_6','#skF_5')),'#skF_5')
    | '#skF_5' = '#skF_6'
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1992,c_4])).

tff(c_2011,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_5'),'#skF_2'('#skF_6','#skF_5')),'#skF_5')
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_36,c_1999])).

tff(c_2012,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_5'),'#skF_2'('#skF_6','#skF_5')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_2011])).

tff(c_2024,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_5')) = '#skF_2'('#skF_6','#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2012,c_20])).

tff(c_2033,plain,(
    k1_funct_1('#skF_6','#skF_1'('#skF_6','#skF_5')) = '#skF_2'('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_341,c_2024])).

tff(c_2051,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_5'),'#skF_2'('#skF_6','#skF_5')),'#skF_6')
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_5'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2033,c_18])).

tff(c_2057,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_5'),'#skF_2'('#skF_6','#skF_5')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_337,c_2051])).

tff(c_2,plain,(
    ! [A_1,B_11] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_1,B_11),'#skF_2'(A_1,B_11)),A_1)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_1,B_11),'#skF_4'(A_1,B_11)),B_11)
      | B_11 = A_1
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2115,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3'('#skF_6','#skF_5'),'#skF_4'('#skF_6','#skF_5')),'#skF_5')
    | '#skF_5' = '#skF_6'
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2057,c_2])).

tff(c_2139,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_36,c_1992,c_2115])).

tff(c_2141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_2139])).

tff(c_2143,plain,(
    k1_funct_1('#skF_6','#skF_3'('#skF_6','#skF_5')) != '#skF_4'('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_1753])).

tff(c_2142,plain,(
    k1_funct_1('#skF_6','#skF_1'('#skF_6','#skF_5')) = '#skF_2'('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_1753])).

tff(c_2153,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_5'),'#skF_2'('#skF_6','#skF_5')),'#skF_6')
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_5'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2142,c_18])).

tff(c_2159,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_5'),'#skF_2'('#skF_6','#skF_5')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_337,c_2153])).

tff(c_81,plain,(
    ! [A_45,B_46] :
      ( k1_funct_1(A_45,'#skF_3'(A_45,B_46)) = '#skF_4'(A_45,B_46)
      | ~ v1_funct_1(A_45)
      | ~ r2_hidden(k4_tarski('#skF_1'(A_45,B_46),'#skF_2'(A_45,B_46)),A_45)
      | B_46 = A_45
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1(A_45) ) ),
    inference(resolution,[status(thm)],[c_67,c_20])).

tff(c_2233,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_6','#skF_5')) = '#skF_4'('#skF_6','#skF_5')
    | ~ v1_funct_1('#skF_6')
    | '#skF_5' = '#skF_6'
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2159,c_81])).

tff(c_2253,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_6','#skF_5')) = '#skF_4'('#skF_6','#skF_5')
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_36,c_30,c_2233])).

tff(c_2255,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_2143,c_2253])).

tff(c_2257,plain,(
    ~ r2_hidden('#skF_1'('#skF_6','#skF_5'),k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_312])).

tff(c_2435,plain,(
    ! [A_120,B_121] :
      ( k1_funct_1(A_120,'#skF_3'(A_120,B_121)) = '#skF_4'(A_120,B_121)
      | ~ v1_funct_1(A_120)
      | r2_hidden(k4_tarski('#skF_1'(A_120,B_121),'#skF_2'(A_120,B_121)),B_121)
      | B_121 = A_120
      | ~ v1_relat_1(B_121)
      | ~ v1_relat_1(A_120) ) ),
    inference(resolution,[status(thm)],[c_94,c_20])).

tff(c_2529,plain,(
    ! [A_126,B_127] :
      ( r2_hidden('#skF_1'(A_126,B_127),k1_relat_1(B_127))
      | k1_funct_1(A_126,'#skF_3'(A_126,B_127)) = '#skF_4'(A_126,B_127)
      | ~ v1_funct_1(A_126)
      | B_127 = A_126
      | ~ v1_relat_1(B_127)
      | ~ v1_relat_1(A_126) ) ),
    inference(resolution,[status(thm)],[c_2435,c_16])).

tff(c_2558,plain,(
    ! [A_126] :
      ( r2_hidden('#skF_1'(A_126,'#skF_5'),k1_relat_1('#skF_6'))
      | k1_funct_1(A_126,'#skF_3'(A_126,'#skF_5')) = '#skF_4'(A_126,'#skF_5')
      | ~ v1_funct_1(A_126)
      | A_126 = '#skF_5'
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1(A_126) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2529])).

tff(c_2568,plain,(
    ! [A_128] :
      ( r2_hidden('#skF_1'(A_128,'#skF_5'),k1_relat_1('#skF_6'))
      | k1_funct_1(A_128,'#skF_3'(A_128,'#skF_5')) = '#skF_4'(A_128,'#skF_5')
      | ~ v1_funct_1(A_128)
      | A_128 = '#skF_5'
      | ~ v1_relat_1(A_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2558])).

tff(c_2571,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_6','#skF_5')) = '#skF_4'('#skF_6','#skF_5')
    | ~ v1_funct_1('#skF_6')
    | '#skF_5' = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2568,c_2257])).

tff(c_2605,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_6','#skF_5')) = '#skF_4'('#skF_6','#skF_5')
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_2571])).

tff(c_2606,plain,(
    k1_funct_1('#skF_6','#skF_3'('#skF_6','#skF_5')) = '#skF_4'('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_2605])).

tff(c_272,plain,(
    ! [A_71,B_72] :
      ( r2_hidden('#skF_1'(A_71,B_72),k1_relat_1(B_72))
      | r2_hidden('#skF_3'(A_71,B_72),k1_relat_1(A_71))
      | B_72 = A_71
      | ~ v1_relat_1(B_72)
      | ~ v1_relat_1(A_71) ) ),
    inference(resolution,[status(thm)],[c_240,c_16])).

tff(c_2256,plain,(
    k1_funct_1('#skF_5','#skF_3'('#skF_6','#skF_5')) = k1_funct_1('#skF_6','#skF_3'('#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_312])).

tff(c_2283,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_3'('#skF_6','#skF_5')),k2_relat_1('#skF_5'))
    | ~ r2_hidden('#skF_3'('#skF_6','#skF_5'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2256,c_62])).

tff(c_2290,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_3'('#skF_6','#skF_5')),k2_relat_1('#skF_5'))
    | ~ r2_hidden('#skF_3'('#skF_6','#skF_5'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_28,c_2283])).

tff(c_2294,plain,(
    ~ r2_hidden('#skF_3'('#skF_6','#skF_5'),k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_2290])).

tff(c_2312,plain,
    ( r2_hidden('#skF_1'('#skF_6','#skF_5'),k1_relat_1('#skF_5'))
    | '#skF_5' = '#skF_6'
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_272,c_2294])).

tff(c_2318,plain,
    ( r2_hidden('#skF_1'('#skF_6','#skF_5'),k1_relat_1('#skF_6'))
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_36,c_28,c_2312])).

tff(c_2320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_2257,c_2318])).

tff(c_2322,plain,(
    r2_hidden('#skF_3'('#skF_6','#skF_5'),k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_2290])).

tff(c_2286,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_6','#skF_5'),k1_funct_1('#skF_6','#skF_3'('#skF_6','#skF_5'))),'#skF_5')
    | ~ r2_hidden('#skF_3'('#skF_6','#skF_5'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2256,c_18])).

tff(c_2292,plain,
    ( r2_hidden(k4_tarski('#skF_3'('#skF_6','#skF_5'),k1_funct_1('#skF_6','#skF_3'('#skF_6','#skF_5'))),'#skF_5')
    | ~ r2_hidden('#skF_3'('#skF_6','#skF_5'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_28,c_2286])).

tff(c_2329,plain,(
    r2_hidden(k4_tarski('#skF_3'('#skF_6','#skF_5'),k1_funct_1('#skF_6','#skF_3'('#skF_6','#skF_5'))),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2322,c_2292])).

tff(c_2622,plain,(
    r2_hidden(k4_tarski('#skF_3'('#skF_6','#skF_5'),'#skF_4'('#skF_6','#skF_5')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2606,c_2329])).

tff(c_2661,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_5'),'#skF_2'('#skF_6','#skF_5')),'#skF_5')
    | '#skF_5' = '#skF_6'
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2622,c_4])).

tff(c_2673,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_5'),'#skF_2'('#skF_6','#skF_5')),'#skF_5')
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_36,c_2661])).

tff(c_2674,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_5'),'#skF_2'('#skF_6','#skF_5')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_2673])).

tff(c_2692,plain,
    ( r2_hidden('#skF_1'('#skF_6','#skF_5'),k1_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2674,c_16])).

tff(c_2701,plain,(
    r2_hidden('#skF_1'('#skF_6','#skF_5'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_28,c_2692])).

tff(c_2703,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2257,c_2701])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n019.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 10:38:37 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.58/1.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.58/1.88  
% 4.58/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.58/1.88  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 4.58/1.88  
% 4.58/1.88  %Foreground sorts:
% 4.58/1.88  
% 4.58/1.88  
% 4.58/1.88  %Background operators:
% 4.58/1.88  
% 4.58/1.88  
% 4.58/1.88  %Foreground operators:
% 4.58/1.88  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.58/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.58/1.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.58/1.88  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.58/1.88  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.58/1.88  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.58/1.88  tff('#skF_5', type, '#skF_5': $i).
% 4.58/1.88  tff('#skF_6', type, '#skF_6': $i).
% 4.58/1.88  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.58/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.58/1.88  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.58/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.58/1.88  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.58/1.88  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.58/1.88  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.58/1.88  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.58/1.89  
% 5.02/1.91  tff(f_74, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 5.02/1.91  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => ((A = B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) <=> r2_hidden(k4_tarski(C, D), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_relat_1)).
% 5.02/1.91  tff(f_55, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 5.02/1.91  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 5.02/1.91  tff(c_24, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.02/1.91  tff(c_32, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.02/1.91  tff(c_36, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.02/1.91  tff(c_34, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.02/1.91  tff(c_30, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.02/1.91  tff(c_94, plain, (![A_53, B_54]: (r2_hidden(k4_tarski('#skF_1'(A_53, B_54), '#skF_2'(A_53, B_54)), B_54) | r2_hidden(k4_tarski('#skF_3'(A_53, B_54), '#skF_4'(A_53, B_54)), A_53) | B_54=A_53 | ~v1_relat_1(B_54) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.02/1.91  tff(c_20, plain, (![C_23, A_21, B_22]: (k1_funct_1(C_23, A_21)=B_22 | ~r2_hidden(k4_tarski(A_21, B_22), C_23) | ~v1_funct_1(C_23) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.02/1.91  tff(c_761, plain, (![A_90, B_91]: (k1_funct_1(A_90, '#skF_3'(A_90, B_91))='#skF_4'(A_90, B_91) | ~v1_funct_1(A_90) | r2_hidden(k4_tarski('#skF_1'(A_90, B_91), '#skF_2'(A_90, B_91)), B_91) | B_91=A_90 | ~v1_relat_1(B_91) | ~v1_relat_1(A_90))), inference(resolution, [status(thm)], [c_94, c_20])).
% 5.02/1.91  tff(c_1618, plain, (![B_112, A_113]: (k1_funct_1(B_112, '#skF_1'(A_113, B_112))='#skF_2'(A_113, B_112) | ~v1_funct_1(B_112) | k1_funct_1(A_113, '#skF_3'(A_113, B_112))='#skF_4'(A_113, B_112) | ~v1_funct_1(A_113) | B_112=A_113 | ~v1_relat_1(B_112) | ~v1_relat_1(A_113))), inference(resolution, [status(thm)], [c_761, c_20])).
% 5.02/1.91  tff(c_28, plain, (k1_relat_1('#skF_5')=k1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.02/1.91  tff(c_16, plain, (![A_18, C_20, B_19]: (r2_hidden(A_18, k1_relat_1(C_20)) | ~r2_hidden(k4_tarski(A_18, B_19), C_20) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.02/1.91  tff(c_240, plain, (![A_71, B_72]: (r2_hidden('#skF_3'(A_71, B_72), k1_relat_1(A_71)) | r2_hidden(k4_tarski('#skF_1'(A_71, B_72), '#skF_2'(A_71, B_72)), B_72) | B_72=A_71 | ~v1_relat_1(B_72) | ~v1_relat_1(A_71))), inference(resolution, [status(thm)], [c_94, c_16])).
% 5.02/1.91  tff(c_274, plain, (![A_73, B_74]: (r2_hidden('#skF_1'(A_73, B_74), k1_relat_1(B_74)) | r2_hidden('#skF_3'(A_73, B_74), k1_relat_1(A_73)) | B_74=A_73 | ~v1_relat_1(B_74) | ~v1_relat_1(A_73))), inference(resolution, [status(thm)], [c_240, c_16])).
% 5.02/1.91  tff(c_26, plain, (![C_28]: (k1_funct_1('#skF_5', C_28)=k1_funct_1('#skF_6', C_28) | ~r2_hidden(C_28, k1_relat_1('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.02/1.91  tff(c_37, plain, (![C_28]: (k1_funct_1('#skF_5', C_28)=k1_funct_1('#skF_6', C_28) | ~r2_hidden(C_28, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26])).
% 5.02/1.91  tff(c_280, plain, (![B_74]: (k1_funct_1('#skF_5', '#skF_3'('#skF_6', B_74))=k1_funct_1('#skF_6', '#skF_3'('#skF_6', B_74)) | r2_hidden('#skF_1'('#skF_6', B_74), k1_relat_1(B_74)) | B_74='#skF_6' | ~v1_relat_1(B_74) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_274, c_37])).
% 5.02/1.91  tff(c_298, plain, (![B_76]: (k1_funct_1('#skF_5', '#skF_3'('#skF_6', B_76))=k1_funct_1('#skF_6', '#skF_3'('#skF_6', B_76)) | r2_hidden('#skF_1'('#skF_6', B_76), k1_relat_1(B_76)) | B_76='#skF_6' | ~v1_relat_1(B_76))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_280])).
% 5.02/1.91  tff(c_305, plain, (k1_funct_1('#skF_5', '#skF_3'('#skF_6', '#skF_5'))=k1_funct_1('#skF_6', '#skF_3'('#skF_6', '#skF_5')) | r2_hidden('#skF_1'('#skF_6', '#skF_5'), k1_relat_1('#skF_6')) | '#skF_5'='#skF_6' | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_28, c_298])).
% 5.02/1.91  tff(c_311, plain, (k1_funct_1('#skF_5', '#skF_3'('#skF_6', '#skF_5'))=k1_funct_1('#skF_6', '#skF_3'('#skF_6', '#skF_5')) | r2_hidden('#skF_1'('#skF_6', '#skF_5'), k1_relat_1('#skF_6')) | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_305])).
% 5.02/1.91  tff(c_312, plain, (k1_funct_1('#skF_5', '#skF_3'('#skF_6', '#skF_5'))=k1_funct_1('#skF_6', '#skF_3'('#skF_6', '#skF_5')) | r2_hidden('#skF_1'('#skF_6', '#skF_5'), k1_relat_1('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_24, c_311])).
% 5.02/1.91  tff(c_337, plain, (r2_hidden('#skF_1'('#skF_6', '#skF_5'), k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_312])).
% 5.02/1.91  tff(c_341, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_5'))=k1_funct_1('#skF_6', '#skF_1'('#skF_6', '#skF_5'))), inference(resolution, [status(thm)], [c_337, c_37])).
% 5.02/1.91  tff(c_1648, plain, (k1_funct_1('#skF_6', '#skF_1'('#skF_6', '#skF_5'))='#skF_2'('#skF_6', '#skF_5') | ~v1_funct_1('#skF_5') | k1_funct_1('#skF_6', '#skF_3'('#skF_6', '#skF_5'))='#skF_4'('#skF_6', '#skF_5') | ~v1_funct_1('#skF_6') | '#skF_5'='#skF_6' | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1618, c_341])).
% 5.02/1.91  tff(c_1752, plain, (k1_funct_1('#skF_6', '#skF_1'('#skF_6', '#skF_5'))='#skF_2'('#skF_6', '#skF_5') | k1_funct_1('#skF_6', '#skF_3'('#skF_6', '#skF_5'))='#skF_4'('#skF_6', '#skF_5') | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_36, c_30, c_34, c_1648])).
% 5.02/1.91  tff(c_1753, plain, (k1_funct_1('#skF_6', '#skF_1'('#skF_6', '#skF_5'))='#skF_2'('#skF_6', '#skF_5') | k1_funct_1('#skF_6', '#skF_3'('#skF_6', '#skF_5'))='#skF_4'('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_24, c_1752])).
% 5.02/1.91  tff(c_1805, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_6', '#skF_5'))='#skF_4'('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_1753])).
% 5.02/1.91  tff(c_46, plain, (![A_39, C_40]: (r2_hidden(k4_tarski(A_39, k1_funct_1(C_40, A_39)), C_40) | ~r2_hidden(A_39, k1_relat_1(C_40)) | ~v1_funct_1(C_40) | ~v1_relat_1(C_40))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.02/1.91  tff(c_14, plain, (![B_19, C_20, A_18]: (r2_hidden(B_19, k2_relat_1(C_20)) | ~r2_hidden(k4_tarski(A_18, B_19), C_20) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.02/1.91  tff(c_62, plain, (![C_40, A_39]: (r2_hidden(k1_funct_1(C_40, A_39), k2_relat_1(C_40)) | ~r2_hidden(A_39, k1_relat_1(C_40)) | ~v1_funct_1(C_40) | ~v1_relat_1(C_40))), inference(resolution, [status(thm)], [c_46, c_14])).
% 5.02/1.91  tff(c_1814, plain, (r2_hidden('#skF_4'('#skF_6', '#skF_5'), k2_relat_1('#skF_6')) | ~r2_hidden('#skF_3'('#skF_6', '#skF_5'), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1805, c_62])).
% 5.02/1.91  tff(c_1826, plain, (r2_hidden('#skF_4'('#skF_6', '#skF_5'), k2_relat_1('#skF_6')) | ~r2_hidden('#skF_3'('#skF_6', '#skF_5'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1814])).
% 5.02/1.91  tff(c_1830, plain, (~r2_hidden('#skF_3'('#skF_6', '#skF_5'), k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_1826])).
% 5.02/1.91  tff(c_270, plain, (![B_72, A_71]: (k1_funct_1(B_72, '#skF_1'(A_71, B_72))='#skF_2'(A_71, B_72) | ~v1_funct_1(B_72) | r2_hidden('#skF_3'(A_71, B_72), k1_relat_1(A_71)) | B_72=A_71 | ~v1_relat_1(B_72) | ~v1_relat_1(A_71))), inference(resolution, [status(thm)], [c_240, c_20])).
% 5.02/1.91  tff(c_1833, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_5'))='#skF_2'('#skF_6', '#skF_5') | ~v1_funct_1('#skF_5') | '#skF_5'='#skF_6' | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_270, c_1830])).
% 5.02/1.91  tff(c_1842, plain, (k1_funct_1('#skF_6', '#skF_1'('#skF_6', '#skF_5'))='#skF_2'('#skF_6', '#skF_5') | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_36, c_34, c_341, c_1833])).
% 5.02/1.91  tff(c_1843, plain, (k1_funct_1('#skF_6', '#skF_1'('#skF_6', '#skF_5'))='#skF_2'('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_24, c_1842])).
% 5.02/1.91  tff(c_18, plain, (![A_21, C_23]: (r2_hidden(k4_tarski(A_21, k1_funct_1(C_23, A_21)), C_23) | ~r2_hidden(A_21, k1_relat_1(C_23)) | ~v1_funct_1(C_23) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.02/1.91  tff(c_1862, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_6', '#skF_5'), '#skF_2'('#skF_6', '#skF_5')), '#skF_6') | ~r2_hidden('#skF_1'('#skF_6', '#skF_5'), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1843, c_18])).
% 5.02/1.91  tff(c_1868, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_6', '#skF_5'), '#skF_2'('#skF_6', '#skF_5')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_337, c_1862])).
% 5.02/1.91  tff(c_67, plain, (![A_45, B_46]: (~r2_hidden(k4_tarski('#skF_1'(A_45, B_46), '#skF_2'(A_45, B_46)), A_45) | r2_hidden(k4_tarski('#skF_3'(A_45, B_46), '#skF_4'(A_45, B_46)), A_45) | B_46=A_45 | ~v1_relat_1(B_46) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.02/1.91  tff(c_83, plain, (![A_45, B_46]: (r2_hidden('#skF_3'(A_45, B_46), k1_relat_1(A_45)) | ~r2_hidden(k4_tarski('#skF_1'(A_45, B_46), '#skF_2'(A_45, B_46)), A_45) | B_46=A_45 | ~v1_relat_1(B_46) | ~v1_relat_1(A_45))), inference(resolution, [status(thm)], [c_67, c_16])).
% 5.02/1.91  tff(c_1940, plain, (r2_hidden('#skF_3'('#skF_6', '#skF_5'), k1_relat_1('#skF_6')) | '#skF_5'='#skF_6' | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1868, c_83])).
% 5.02/1.91  tff(c_1961, plain, (r2_hidden('#skF_3'('#skF_6', '#skF_5'), k1_relat_1('#skF_6')) | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_36, c_1940])).
% 5.02/1.91  tff(c_1963, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_1830, c_1961])).
% 5.02/1.91  tff(c_1965, plain, (r2_hidden('#skF_3'('#skF_6', '#skF_5'), k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_1826])).
% 5.02/1.91  tff(c_1968, plain, (k1_funct_1('#skF_5', '#skF_3'('#skF_6', '#skF_5'))=k1_funct_1('#skF_6', '#skF_3'('#skF_6', '#skF_5'))), inference(resolution, [status(thm)], [c_1965, c_37])).
% 5.02/1.91  tff(c_1970, plain, (k1_funct_1('#skF_5', '#skF_3'('#skF_6', '#skF_5'))='#skF_4'('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1805, c_1968])).
% 5.02/1.91  tff(c_1980, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_6', '#skF_5'), '#skF_4'('#skF_6', '#skF_5')), '#skF_5') | ~r2_hidden('#skF_3'('#skF_6', '#skF_5'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1970, c_18])).
% 5.02/1.91  tff(c_1992, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_6', '#skF_5'), '#skF_4'('#skF_6', '#skF_5')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_1965, c_28, c_1980])).
% 5.02/1.91  tff(c_4, plain, (![A_1, B_11]: (r2_hidden(k4_tarski('#skF_1'(A_1, B_11), '#skF_2'(A_1, B_11)), B_11) | ~r2_hidden(k4_tarski('#skF_3'(A_1, B_11), '#skF_4'(A_1, B_11)), B_11) | B_11=A_1 | ~v1_relat_1(B_11) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.02/1.91  tff(c_1999, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_6', '#skF_5'), '#skF_2'('#skF_6', '#skF_5')), '#skF_5') | '#skF_5'='#skF_6' | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1992, c_4])).
% 5.02/1.91  tff(c_2011, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_6', '#skF_5'), '#skF_2'('#skF_6', '#skF_5')), '#skF_5') | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_36, c_1999])).
% 5.02/1.91  tff(c_2012, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_6', '#skF_5'), '#skF_2'('#skF_6', '#skF_5')), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_24, c_2011])).
% 5.02/1.91  tff(c_2024, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_5'))='#skF_2'('#skF_6', '#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2012, c_20])).
% 5.02/1.91  tff(c_2033, plain, (k1_funct_1('#skF_6', '#skF_1'('#skF_6', '#skF_5'))='#skF_2'('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_341, c_2024])).
% 5.02/1.91  tff(c_2051, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_6', '#skF_5'), '#skF_2'('#skF_6', '#skF_5')), '#skF_6') | ~r2_hidden('#skF_1'('#skF_6', '#skF_5'), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2033, c_18])).
% 5.02/1.91  tff(c_2057, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_6', '#skF_5'), '#skF_2'('#skF_6', '#skF_5')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_337, c_2051])).
% 5.02/1.91  tff(c_2, plain, (![A_1, B_11]: (~r2_hidden(k4_tarski('#skF_1'(A_1, B_11), '#skF_2'(A_1, B_11)), A_1) | ~r2_hidden(k4_tarski('#skF_3'(A_1, B_11), '#skF_4'(A_1, B_11)), B_11) | B_11=A_1 | ~v1_relat_1(B_11) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.02/1.91  tff(c_2115, plain, (~r2_hidden(k4_tarski('#skF_3'('#skF_6', '#skF_5'), '#skF_4'('#skF_6', '#skF_5')), '#skF_5') | '#skF_5'='#skF_6' | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2057, c_2])).
% 5.02/1.91  tff(c_2139, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_36, c_1992, c_2115])).
% 5.02/1.91  tff(c_2141, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_2139])).
% 5.02/1.91  tff(c_2143, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_6', '#skF_5'))!='#skF_4'('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_1753])).
% 5.02/1.91  tff(c_2142, plain, (k1_funct_1('#skF_6', '#skF_1'('#skF_6', '#skF_5'))='#skF_2'('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_1753])).
% 5.02/1.91  tff(c_2153, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_6', '#skF_5'), '#skF_2'('#skF_6', '#skF_5')), '#skF_6') | ~r2_hidden('#skF_1'('#skF_6', '#skF_5'), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2142, c_18])).
% 5.02/1.91  tff(c_2159, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_6', '#skF_5'), '#skF_2'('#skF_6', '#skF_5')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_337, c_2153])).
% 5.02/1.91  tff(c_81, plain, (![A_45, B_46]: (k1_funct_1(A_45, '#skF_3'(A_45, B_46))='#skF_4'(A_45, B_46) | ~v1_funct_1(A_45) | ~r2_hidden(k4_tarski('#skF_1'(A_45, B_46), '#skF_2'(A_45, B_46)), A_45) | B_46=A_45 | ~v1_relat_1(B_46) | ~v1_relat_1(A_45))), inference(resolution, [status(thm)], [c_67, c_20])).
% 5.02/1.91  tff(c_2233, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_6', '#skF_5'))='#skF_4'('#skF_6', '#skF_5') | ~v1_funct_1('#skF_6') | '#skF_5'='#skF_6' | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2159, c_81])).
% 5.02/1.91  tff(c_2253, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_6', '#skF_5'))='#skF_4'('#skF_6', '#skF_5') | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_36, c_30, c_2233])).
% 5.02/1.91  tff(c_2255, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_2143, c_2253])).
% 5.02/1.91  tff(c_2257, plain, (~r2_hidden('#skF_1'('#skF_6', '#skF_5'), k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_312])).
% 5.02/1.91  tff(c_2435, plain, (![A_120, B_121]: (k1_funct_1(A_120, '#skF_3'(A_120, B_121))='#skF_4'(A_120, B_121) | ~v1_funct_1(A_120) | r2_hidden(k4_tarski('#skF_1'(A_120, B_121), '#skF_2'(A_120, B_121)), B_121) | B_121=A_120 | ~v1_relat_1(B_121) | ~v1_relat_1(A_120))), inference(resolution, [status(thm)], [c_94, c_20])).
% 5.02/1.91  tff(c_2529, plain, (![A_126, B_127]: (r2_hidden('#skF_1'(A_126, B_127), k1_relat_1(B_127)) | k1_funct_1(A_126, '#skF_3'(A_126, B_127))='#skF_4'(A_126, B_127) | ~v1_funct_1(A_126) | B_127=A_126 | ~v1_relat_1(B_127) | ~v1_relat_1(A_126))), inference(resolution, [status(thm)], [c_2435, c_16])).
% 5.02/1.91  tff(c_2558, plain, (![A_126]: (r2_hidden('#skF_1'(A_126, '#skF_5'), k1_relat_1('#skF_6')) | k1_funct_1(A_126, '#skF_3'(A_126, '#skF_5'))='#skF_4'(A_126, '#skF_5') | ~v1_funct_1(A_126) | A_126='#skF_5' | ~v1_relat_1('#skF_5') | ~v1_relat_1(A_126))), inference(superposition, [status(thm), theory('equality')], [c_28, c_2529])).
% 5.02/1.91  tff(c_2568, plain, (![A_128]: (r2_hidden('#skF_1'(A_128, '#skF_5'), k1_relat_1('#skF_6')) | k1_funct_1(A_128, '#skF_3'(A_128, '#skF_5'))='#skF_4'(A_128, '#skF_5') | ~v1_funct_1(A_128) | A_128='#skF_5' | ~v1_relat_1(A_128))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2558])).
% 5.02/1.91  tff(c_2571, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_6', '#skF_5'))='#skF_4'('#skF_6', '#skF_5') | ~v1_funct_1('#skF_6') | '#skF_5'='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2568, c_2257])).
% 5.02/1.91  tff(c_2605, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_6', '#skF_5'))='#skF_4'('#skF_6', '#skF_5') | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_2571])).
% 5.02/1.91  tff(c_2606, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_6', '#skF_5'))='#skF_4'('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_24, c_2605])).
% 5.02/1.91  tff(c_272, plain, (![A_71, B_72]: (r2_hidden('#skF_1'(A_71, B_72), k1_relat_1(B_72)) | r2_hidden('#skF_3'(A_71, B_72), k1_relat_1(A_71)) | B_72=A_71 | ~v1_relat_1(B_72) | ~v1_relat_1(A_71))), inference(resolution, [status(thm)], [c_240, c_16])).
% 5.02/1.91  tff(c_2256, plain, (k1_funct_1('#skF_5', '#skF_3'('#skF_6', '#skF_5'))=k1_funct_1('#skF_6', '#skF_3'('#skF_6', '#skF_5'))), inference(splitRight, [status(thm)], [c_312])).
% 5.02/1.91  tff(c_2283, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_3'('#skF_6', '#skF_5')), k2_relat_1('#skF_5')) | ~r2_hidden('#skF_3'('#skF_6', '#skF_5'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2256, c_62])).
% 5.02/1.91  tff(c_2290, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_3'('#skF_6', '#skF_5')), k2_relat_1('#skF_5')) | ~r2_hidden('#skF_3'('#skF_6', '#skF_5'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_28, c_2283])).
% 5.02/1.91  tff(c_2294, plain, (~r2_hidden('#skF_3'('#skF_6', '#skF_5'), k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_2290])).
% 5.02/1.91  tff(c_2312, plain, (r2_hidden('#skF_1'('#skF_6', '#skF_5'), k1_relat_1('#skF_5')) | '#skF_5'='#skF_6' | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_272, c_2294])).
% 5.02/1.91  tff(c_2318, plain, (r2_hidden('#skF_1'('#skF_6', '#skF_5'), k1_relat_1('#skF_6')) | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_36, c_28, c_2312])).
% 5.02/1.91  tff(c_2320, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_2257, c_2318])).
% 5.02/1.91  tff(c_2322, plain, (r2_hidden('#skF_3'('#skF_6', '#skF_5'), k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_2290])).
% 5.02/1.91  tff(c_2286, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_6', '#skF_5'), k1_funct_1('#skF_6', '#skF_3'('#skF_6', '#skF_5'))), '#skF_5') | ~r2_hidden('#skF_3'('#skF_6', '#skF_5'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2256, c_18])).
% 5.02/1.91  tff(c_2292, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_6', '#skF_5'), k1_funct_1('#skF_6', '#skF_3'('#skF_6', '#skF_5'))), '#skF_5') | ~r2_hidden('#skF_3'('#skF_6', '#skF_5'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_28, c_2286])).
% 5.02/1.91  tff(c_2329, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_6', '#skF_5'), k1_funct_1('#skF_6', '#skF_3'('#skF_6', '#skF_5'))), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2322, c_2292])).
% 5.02/1.91  tff(c_2622, plain, (r2_hidden(k4_tarski('#skF_3'('#skF_6', '#skF_5'), '#skF_4'('#skF_6', '#skF_5')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2606, c_2329])).
% 5.02/1.91  tff(c_2661, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_6', '#skF_5'), '#skF_2'('#skF_6', '#skF_5')), '#skF_5') | '#skF_5'='#skF_6' | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2622, c_4])).
% 5.02/1.91  tff(c_2673, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_6', '#skF_5'), '#skF_2'('#skF_6', '#skF_5')), '#skF_5') | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_36, c_2661])).
% 5.02/1.91  tff(c_2674, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_6', '#skF_5'), '#skF_2'('#skF_6', '#skF_5')), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_24, c_2673])).
% 5.02/1.91  tff(c_2692, plain, (r2_hidden('#skF_1'('#skF_6', '#skF_5'), k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2674, c_16])).
% 5.02/1.91  tff(c_2701, plain, (r2_hidden('#skF_1'('#skF_6', '#skF_5'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_28, c_2692])).
% 5.02/1.91  tff(c_2703, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2257, c_2701])).
% 5.02/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.02/1.91  
% 5.02/1.91  Inference rules
% 5.02/1.91  ----------------------
% 5.02/1.91  #Ref     : 0
% 5.02/1.91  #Sup     : 503
% 5.02/1.91  #Fact    : 0
% 5.02/1.91  #Define  : 0
% 5.02/1.91  #Split   : 11
% 5.02/1.91  #Chain   : 0
% 5.02/1.91  #Close   : 0
% 5.02/1.91  
% 5.02/1.91  Ordering : KBO
% 5.02/1.91  
% 5.02/1.91  Simplification rules
% 5.02/1.91  ----------------------
% 5.02/1.91  #Subsume      : 66
% 5.02/1.91  #Demod        : 619
% 5.02/1.91  #Tautology    : 285
% 5.02/1.91  #SimpNegUnit  : 62
% 5.02/1.91  #BackRed      : 18
% 5.02/1.91  
% 5.02/1.91  #Partial instantiations: 0
% 5.02/1.91  #Strategies tried      : 1
% 5.02/1.91  
% 5.02/1.91  Timing (in seconds)
% 5.02/1.91  ----------------------
% 5.02/1.91  Preprocessing        : 0.31
% 5.02/1.91  Parsing              : 0.16
% 5.02/1.91  CNF conversion       : 0.03
% 5.02/1.91  Main loop            : 0.83
% 5.02/1.91  Inferencing          : 0.34
% 5.02/1.91  Reduction            : 0.25
% 5.02/1.91  Demodulation         : 0.17
% 5.02/1.91  BG Simplification    : 0.04
% 5.02/1.91  Subsumption          : 0.16
% 5.02/1.91  Abstraction          : 0.04
% 5.02/1.91  MUC search           : 0.00
% 5.02/1.91  Cooper               : 0.00
% 5.02/1.91  Total                : 1.18
% 5.02/1.91  Index Insertion      : 0.00
% 5.02/1.91  Index Deletion       : 0.00
% 5.02/1.91  Index Matching       : 0.00
% 5.02/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
