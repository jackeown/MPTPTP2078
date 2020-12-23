%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:37 EST 2020

% Result     : Theorem 5.18s
% Output     : CNFRefutation 5.18s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 177 expanded)
%              Number of leaves         :   26 (  72 expanded)
%              Depth                    :   10
%              Number of atoms          :  183 ( 522 expanded)
%              Number of equality atoms :    3 (   9 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k1_funct_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( r1_tarski(C,k1_relat_1(k5_relat_1(A,B)))
              <=> ( r1_tarski(C,k1_relat_1(A))
                  & r1_tarski(k9_relat_1(A,C),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( r2_hidden(D,k1_relat_1(A))
                & r2_hidden(k1_funct_1(A,D),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_60,plain,(
    ! [A_39,B_40] :
      ( ~ r2_hidden('#skF_1'(A_39,B_40),B_40)
      | r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_65,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_60])).

tff(c_46,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_42,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_44,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_10,plain,(
    ! [A_9,B_11] :
      ( k10_relat_1(A_9,k1_relat_1(B_11)) = k1_relat_1(k5_relat_1(A_9,B_11))
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_98,plain,(
    ! [D_55,A_56,B_57] :
      ( r2_hidden(D_55,k1_relat_1(A_56))
      | ~ r2_hidden(D_55,k10_relat_1(A_56,B_57))
      | ~ v1_funct_1(A_56)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_148,plain,(
    ! [A_68,B_69,B_70] :
      ( r2_hidden('#skF_1'(k10_relat_1(A_68,B_69),B_70),k1_relat_1(A_68))
      | ~ v1_funct_1(A_68)
      | ~ v1_relat_1(A_68)
      | r1_tarski(k10_relat_1(A_68,B_69),B_70) ) ),
    inference(resolution,[status(thm)],[c_6,c_98])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_160,plain,(
    ! [A_71,B_72] :
      ( ~ v1_funct_1(A_71)
      | ~ v1_relat_1(A_71)
      | r1_tarski(k10_relat_1(A_71,B_72),k1_relat_1(A_71)) ) ),
    inference(resolution,[status(thm)],[c_148,c_4])).

tff(c_165,plain,(
    ! [A_9,B_11] :
      ( ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9)
      | r1_tarski(k1_relat_1(k5_relat_1(A_9,B_11)),k1_relat_1(A_9))
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_160])).

tff(c_58,plain,
    ( r1_tarski('#skF_6',k1_relat_1('#skF_4'))
    | r1_tarski('#skF_7',k1_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_71,plain,(
    r1_tarski('#skF_7',k1_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_67,plain,(
    ! [C_42,B_43,A_44] :
      ( r2_hidden(C_42,B_43)
      | ~ r2_hidden(C_42,A_44)
      | ~ r1_tarski(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_75,plain,(
    ! [A_47,B_48,B_49] :
      ( r2_hidden('#skF_1'(A_47,B_48),B_49)
      | ~ r1_tarski(A_47,B_49)
      | r1_tarski(A_47,B_48) ) ),
    inference(resolution,[status(thm)],[c_6,c_67])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_122,plain,(
    ! [A_61,B_62,B_63,B_64] :
      ( r2_hidden('#skF_1'(A_61,B_62),B_63)
      | ~ r1_tarski(B_64,B_63)
      | ~ r1_tarski(A_61,B_64)
      | r1_tarski(A_61,B_62) ) ),
    inference(resolution,[status(thm)],[c_75,c_2])).

tff(c_135,plain,(
    ! [A_65,B_66] :
      ( r2_hidden('#skF_1'(A_65,B_66),k1_relat_1(k5_relat_1('#skF_4','#skF_5')))
      | ~ r1_tarski(A_65,'#skF_7')
      | r1_tarski(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_71,c_122])).

tff(c_171,plain,(
    ! [A_75,B_76,B_77] :
      ( r2_hidden('#skF_1'(A_75,B_76),B_77)
      | ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_4','#skF_5')),B_77)
      | ~ r1_tarski(A_75,'#skF_7')
      | r1_tarski(A_75,B_76) ) ),
    inference(resolution,[status(thm)],[c_135,c_2])).

tff(c_174,plain,(
    ! [A_75,B_76] :
      ( r2_hidden('#skF_1'(A_75,B_76),k1_relat_1('#skF_4'))
      | ~ r1_tarski(A_75,'#skF_7')
      | r1_tarski(A_75,B_76)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_165,c_171])).

tff(c_186,plain,(
    ! [A_78,B_79] :
      ( r2_hidden('#skF_1'(A_78,B_79),k1_relat_1('#skF_4'))
      | ~ r1_tarski(A_78,'#skF_7')
      | r1_tarski(A_78,B_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_44,c_174])).

tff(c_195,plain,(
    ! [A_80] :
      ( ~ r1_tarski(A_80,'#skF_7')
      | r1_tarski(A_80,k1_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_186,c_4])).

tff(c_52,plain,
    ( r1_tarski('#skF_6',k1_relat_1('#skF_4'))
    | ~ r1_tarski(k9_relat_1('#skF_4','#skF_7'),k1_relat_1('#skF_5'))
    | ~ r1_tarski('#skF_7',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_121,plain,(
    ~ r1_tarski('#skF_7',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_203,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_195,c_121])).

tff(c_209,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_203])).

tff(c_211,plain,(
    r1_tarski('#skF_7',k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_8,plain,(
    ! [C_8,A_6,B_7] :
      ( r1_tarski(k9_relat_1(C_8,A_6),k9_relat_1(C_8,B_7))
      | ~ r1_tarski(A_6,B_7)
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_30,plain,(
    ! [B_25,A_24] :
      ( r1_tarski(k9_relat_1(B_25,k10_relat_1(B_25,A_24)),A_24)
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_215,plain,(
    ! [A_81,B_82,B_83,B_84] :
      ( r2_hidden('#skF_1'(A_81,B_82),B_83)
      | ~ r1_tarski(B_84,B_83)
      | ~ r1_tarski(A_81,B_84)
      | r1_tarski(A_81,B_82) ) ),
    inference(resolution,[status(thm)],[c_75,c_2])).

tff(c_750,plain,(
    ! [A_158,B_159,A_160,B_161] :
      ( r2_hidden('#skF_1'(A_158,B_159),A_160)
      | ~ r1_tarski(A_158,k9_relat_1(B_161,k10_relat_1(B_161,A_160)))
      | r1_tarski(A_158,B_159)
      | ~ v1_funct_1(B_161)
      | ~ v1_relat_1(B_161) ) ),
    inference(resolution,[status(thm)],[c_30,c_215])).

tff(c_1868,plain,(
    ! [C_259,A_260,B_261,A_262] :
      ( r2_hidden('#skF_1'(k9_relat_1(C_259,A_260),B_261),A_262)
      | r1_tarski(k9_relat_1(C_259,A_260),B_261)
      | ~ v1_funct_1(C_259)
      | ~ r1_tarski(A_260,k10_relat_1(C_259,A_262))
      | ~ v1_relat_1(C_259) ) ),
    inference(resolution,[status(thm)],[c_8,c_750])).

tff(c_1904,plain,(
    ! [C_263,A_264,A_265] :
      ( r1_tarski(k9_relat_1(C_263,A_264),A_265)
      | ~ v1_funct_1(C_263)
      | ~ r1_tarski(A_264,k10_relat_1(C_263,A_265))
      | ~ v1_relat_1(C_263) ) ),
    inference(resolution,[status(thm)],[c_1868,c_4])).

tff(c_210,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_7'),k1_relat_1('#skF_5'))
    | r1_tarski('#skF_6',k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_212,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_7'),k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_210])).

tff(c_1934,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ r1_tarski('#skF_7',k10_relat_1('#skF_4',k1_relat_1('#skF_5')))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1904,c_212])).

tff(c_1948,plain,(
    ~ r1_tarski('#skF_7',k10_relat_1('#skF_4',k1_relat_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_1934])).

tff(c_1951,plain,
    ( ~ r1_tarski('#skF_7',k1_relat_1(k5_relat_1('#skF_4','#skF_5')))
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1948])).

tff(c_1954,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_71,c_1951])).

tff(c_1956,plain,(
    r1_tarski(k9_relat_1('#skF_4','#skF_7'),k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_210])).

tff(c_48,plain,
    ( ~ r1_tarski('#skF_6',k1_relat_1(k5_relat_1('#skF_4','#skF_5')))
    | ~ r1_tarski(k9_relat_1('#skF_4','#skF_7'),k1_relat_1('#skF_5'))
    | ~ r1_tarski('#skF_7',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2020,plain,(
    ~ r1_tarski('#skF_6',k1_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_1956,c_48])).

tff(c_1955,plain,(
    r1_tarski('#skF_6',k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_210])).

tff(c_50,plain,
    ( r1_tarski(k9_relat_1('#skF_4','#skF_6'),k1_relat_1('#skF_5'))
    | ~ r1_tarski(k9_relat_1('#skF_4','#skF_7'),k1_relat_1('#skF_5'))
    | ~ r1_tarski('#skF_7',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1993,plain,(
    r1_tarski(k9_relat_1('#skF_4','#skF_6'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_1956,c_50])).

tff(c_2295,plain,(
    ! [A_311,C_312,B_313] :
      ( r1_tarski(A_311,k10_relat_1(C_312,B_313))
      | ~ r1_tarski(k9_relat_1(C_312,A_311),B_313)
      | ~ r1_tarski(A_311,k1_relat_1(C_312))
      | ~ v1_funct_1(C_312)
      | ~ v1_relat_1(C_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2318,plain,
    ( r1_tarski('#skF_6',k10_relat_1('#skF_4',k1_relat_1('#skF_5')))
    | ~ r1_tarski('#skF_6',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1993,c_2295])).

tff(c_2348,plain,(
    r1_tarski('#skF_6',k10_relat_1('#skF_4',k1_relat_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_1955,c_2318])).

tff(c_2365,plain,
    ( r1_tarski('#skF_6',k1_relat_1(k5_relat_1('#skF_4','#skF_5')))
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2348])).

tff(c_2370,plain,(
    r1_tarski('#skF_6',k1_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_2365])).

tff(c_2372,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2020,c_2370])).

tff(c_2374,plain,(
    ~ r1_tarski('#skF_7',k1_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_54,plain,
    ( ~ r1_tarski('#skF_6',k1_relat_1(k5_relat_1('#skF_4','#skF_5')))
    | r1_tarski('#skF_7',k1_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2398,plain,(
    ~ r1_tarski('#skF_6',k1_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_2374,c_54])).

tff(c_2373,plain,(
    r1_tarski('#skF_6',k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_56,plain,
    ( r1_tarski(k9_relat_1('#skF_4','#skF_6'),k1_relat_1('#skF_5'))
    | r1_tarski('#skF_7',k1_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2375,plain,(
    r1_tarski(k9_relat_1('#skF_4','#skF_6'),k1_relat_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_2374,c_56])).

tff(c_2706,plain,(
    ! [A_379,C_380,B_381] :
      ( r1_tarski(A_379,k10_relat_1(C_380,B_381))
      | ~ r1_tarski(k9_relat_1(C_380,A_379),B_381)
      | ~ r1_tarski(A_379,k1_relat_1(C_380))
      | ~ v1_funct_1(C_380)
      | ~ v1_relat_1(C_380) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2728,plain,
    ( r1_tarski('#skF_6',k10_relat_1('#skF_4',k1_relat_1('#skF_5')))
    | ~ r1_tarski('#skF_6',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2375,c_2706])).

tff(c_2744,plain,(
    r1_tarski('#skF_6',k10_relat_1('#skF_4',k1_relat_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_2373,c_2728])).

tff(c_2756,plain,
    ( r1_tarski('#skF_6',k1_relat_1(k5_relat_1('#skF_4','#skF_5')))
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2744])).

tff(c_2762,plain,(
    r1_tarski('#skF_6',k1_relat_1(k5_relat_1('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_2756])).

tff(c_2764,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2398,c_2762])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:19:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.18/1.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.18/1.97  
% 5.18/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.18/1.97  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k1_funct_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 5.18/1.97  
% 5.18/1.97  %Foreground sorts:
% 5.18/1.97  
% 5.18/1.97  
% 5.18/1.97  %Background operators:
% 5.18/1.97  
% 5.18/1.97  
% 5.18/1.97  %Foreground operators:
% 5.18/1.97  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.18/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.18/1.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.18/1.97  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.18/1.97  tff('#skF_7', type, '#skF_7': $i).
% 5.18/1.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.18/1.97  tff('#skF_5', type, '#skF_5': $i).
% 5.18/1.97  tff('#skF_6', type, '#skF_6': $i).
% 5.18/1.97  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.18/1.97  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.18/1.97  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.18/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.18/1.97  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.18/1.97  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.18/1.97  tff('#skF_4', type, '#skF_4': $i).
% 5.18/1.97  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.18/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.18/1.97  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.18/1.97  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.18/1.97  
% 5.18/1.99  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.18/1.99  tff(f_107, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (r1_tarski(C, k1_relat_1(k5_relat_1(A, B))) <=> (r1_tarski(C, k1_relat_1(A)) & r1_tarski(k9_relat_1(A, C), k1_relat_1(B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_1)).
% 5.18/1.99  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 5.18/1.99  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, k1_relat_1(A)) & r2_hidden(k1_funct_1(A, D), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_funct_1)).
% 5.18/1.99  tff(f_38, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 5.18/1.99  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 5.18/1.99  tff(f_75, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 5.18/1.99  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.18/1.99  tff(c_60, plain, (![A_39, B_40]: (~r2_hidden('#skF_1'(A_39, B_40), B_40) | r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.18/1.99  tff(c_65, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_60])).
% 5.18/1.99  tff(c_46, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.18/1.99  tff(c_42, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.18/1.99  tff(c_44, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.18/1.99  tff(c_10, plain, (![A_9, B_11]: (k10_relat_1(A_9, k1_relat_1(B_11))=k1_relat_1(k5_relat_1(A_9, B_11)) | ~v1_relat_1(B_11) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.18/1.99  tff(c_98, plain, (![D_55, A_56, B_57]: (r2_hidden(D_55, k1_relat_1(A_56)) | ~r2_hidden(D_55, k10_relat_1(A_56, B_57)) | ~v1_funct_1(A_56) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.18/1.99  tff(c_148, plain, (![A_68, B_69, B_70]: (r2_hidden('#skF_1'(k10_relat_1(A_68, B_69), B_70), k1_relat_1(A_68)) | ~v1_funct_1(A_68) | ~v1_relat_1(A_68) | r1_tarski(k10_relat_1(A_68, B_69), B_70))), inference(resolution, [status(thm)], [c_6, c_98])).
% 5.18/1.99  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.18/1.99  tff(c_160, plain, (![A_71, B_72]: (~v1_funct_1(A_71) | ~v1_relat_1(A_71) | r1_tarski(k10_relat_1(A_71, B_72), k1_relat_1(A_71)))), inference(resolution, [status(thm)], [c_148, c_4])).
% 5.18/1.99  tff(c_165, plain, (![A_9, B_11]: (~v1_funct_1(A_9) | ~v1_relat_1(A_9) | r1_tarski(k1_relat_1(k5_relat_1(A_9, B_11)), k1_relat_1(A_9)) | ~v1_relat_1(B_11) | ~v1_relat_1(A_9))), inference(superposition, [status(thm), theory('equality')], [c_10, c_160])).
% 5.18/1.99  tff(c_58, plain, (r1_tarski('#skF_6', k1_relat_1('#skF_4')) | r1_tarski('#skF_7', k1_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.18/1.99  tff(c_71, plain, (r1_tarski('#skF_7', k1_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_58])).
% 5.18/1.99  tff(c_67, plain, (![C_42, B_43, A_44]: (r2_hidden(C_42, B_43) | ~r2_hidden(C_42, A_44) | ~r1_tarski(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.18/1.99  tff(c_75, plain, (![A_47, B_48, B_49]: (r2_hidden('#skF_1'(A_47, B_48), B_49) | ~r1_tarski(A_47, B_49) | r1_tarski(A_47, B_48))), inference(resolution, [status(thm)], [c_6, c_67])).
% 5.18/1.99  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.18/1.99  tff(c_122, plain, (![A_61, B_62, B_63, B_64]: (r2_hidden('#skF_1'(A_61, B_62), B_63) | ~r1_tarski(B_64, B_63) | ~r1_tarski(A_61, B_64) | r1_tarski(A_61, B_62))), inference(resolution, [status(thm)], [c_75, c_2])).
% 5.18/1.99  tff(c_135, plain, (![A_65, B_66]: (r2_hidden('#skF_1'(A_65, B_66), k1_relat_1(k5_relat_1('#skF_4', '#skF_5'))) | ~r1_tarski(A_65, '#skF_7') | r1_tarski(A_65, B_66))), inference(resolution, [status(thm)], [c_71, c_122])).
% 5.18/1.99  tff(c_171, plain, (![A_75, B_76, B_77]: (r2_hidden('#skF_1'(A_75, B_76), B_77) | ~r1_tarski(k1_relat_1(k5_relat_1('#skF_4', '#skF_5')), B_77) | ~r1_tarski(A_75, '#skF_7') | r1_tarski(A_75, B_76))), inference(resolution, [status(thm)], [c_135, c_2])).
% 5.18/1.99  tff(c_174, plain, (![A_75, B_76]: (r2_hidden('#skF_1'(A_75, B_76), k1_relat_1('#skF_4')) | ~r1_tarski(A_75, '#skF_7') | r1_tarski(A_75, B_76) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_165, c_171])).
% 5.18/1.99  tff(c_186, plain, (![A_78, B_79]: (r2_hidden('#skF_1'(A_78, B_79), k1_relat_1('#skF_4')) | ~r1_tarski(A_78, '#skF_7') | r1_tarski(A_78, B_79))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_44, c_174])).
% 5.18/1.99  tff(c_195, plain, (![A_80]: (~r1_tarski(A_80, '#skF_7') | r1_tarski(A_80, k1_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_186, c_4])).
% 5.18/1.99  tff(c_52, plain, (r1_tarski('#skF_6', k1_relat_1('#skF_4')) | ~r1_tarski(k9_relat_1('#skF_4', '#skF_7'), k1_relat_1('#skF_5')) | ~r1_tarski('#skF_7', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.18/1.99  tff(c_121, plain, (~r1_tarski('#skF_7', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_52])).
% 5.18/1.99  tff(c_203, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_195, c_121])).
% 5.18/1.99  tff(c_209, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_203])).
% 5.18/1.99  tff(c_211, plain, (r1_tarski('#skF_7', k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_52])).
% 5.18/1.99  tff(c_8, plain, (![C_8, A_6, B_7]: (r1_tarski(k9_relat_1(C_8, A_6), k9_relat_1(C_8, B_7)) | ~r1_tarski(A_6, B_7) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.18/1.99  tff(c_30, plain, (![B_25, A_24]: (r1_tarski(k9_relat_1(B_25, k10_relat_1(B_25, A_24)), A_24) | ~v1_funct_1(B_25) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.18/1.99  tff(c_215, plain, (![A_81, B_82, B_83, B_84]: (r2_hidden('#skF_1'(A_81, B_82), B_83) | ~r1_tarski(B_84, B_83) | ~r1_tarski(A_81, B_84) | r1_tarski(A_81, B_82))), inference(resolution, [status(thm)], [c_75, c_2])).
% 5.18/1.99  tff(c_750, plain, (![A_158, B_159, A_160, B_161]: (r2_hidden('#skF_1'(A_158, B_159), A_160) | ~r1_tarski(A_158, k9_relat_1(B_161, k10_relat_1(B_161, A_160))) | r1_tarski(A_158, B_159) | ~v1_funct_1(B_161) | ~v1_relat_1(B_161))), inference(resolution, [status(thm)], [c_30, c_215])).
% 5.18/1.99  tff(c_1868, plain, (![C_259, A_260, B_261, A_262]: (r2_hidden('#skF_1'(k9_relat_1(C_259, A_260), B_261), A_262) | r1_tarski(k9_relat_1(C_259, A_260), B_261) | ~v1_funct_1(C_259) | ~r1_tarski(A_260, k10_relat_1(C_259, A_262)) | ~v1_relat_1(C_259))), inference(resolution, [status(thm)], [c_8, c_750])).
% 5.18/1.99  tff(c_1904, plain, (![C_263, A_264, A_265]: (r1_tarski(k9_relat_1(C_263, A_264), A_265) | ~v1_funct_1(C_263) | ~r1_tarski(A_264, k10_relat_1(C_263, A_265)) | ~v1_relat_1(C_263))), inference(resolution, [status(thm)], [c_1868, c_4])).
% 5.18/1.99  tff(c_210, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_7'), k1_relat_1('#skF_5')) | r1_tarski('#skF_6', k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_52])).
% 5.18/1.99  tff(c_212, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_7'), k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_210])).
% 5.18/1.99  tff(c_1934, plain, (~v1_funct_1('#skF_4') | ~r1_tarski('#skF_7', k10_relat_1('#skF_4', k1_relat_1('#skF_5'))) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1904, c_212])).
% 5.18/1.99  tff(c_1948, plain, (~r1_tarski('#skF_7', k10_relat_1('#skF_4', k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_1934])).
% 5.18/1.99  tff(c_1951, plain, (~r1_tarski('#skF_7', k1_relat_1(k5_relat_1('#skF_4', '#skF_5'))) | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10, c_1948])).
% 5.18/1.99  tff(c_1954, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_71, c_1951])).
% 5.18/1.99  tff(c_1956, plain, (r1_tarski(k9_relat_1('#skF_4', '#skF_7'), k1_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_210])).
% 5.18/1.99  tff(c_48, plain, (~r1_tarski('#skF_6', k1_relat_1(k5_relat_1('#skF_4', '#skF_5'))) | ~r1_tarski(k9_relat_1('#skF_4', '#skF_7'), k1_relat_1('#skF_5')) | ~r1_tarski('#skF_7', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.18/1.99  tff(c_2020, plain, (~r1_tarski('#skF_6', k1_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_211, c_1956, c_48])).
% 5.18/1.99  tff(c_1955, plain, (r1_tarski('#skF_6', k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_210])).
% 5.18/1.99  tff(c_50, plain, (r1_tarski(k9_relat_1('#skF_4', '#skF_6'), k1_relat_1('#skF_5')) | ~r1_tarski(k9_relat_1('#skF_4', '#skF_7'), k1_relat_1('#skF_5')) | ~r1_tarski('#skF_7', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.18/1.99  tff(c_1993, plain, (r1_tarski(k9_relat_1('#skF_4', '#skF_6'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_211, c_1956, c_50])).
% 5.18/1.99  tff(c_2295, plain, (![A_311, C_312, B_313]: (r1_tarski(A_311, k10_relat_1(C_312, B_313)) | ~r1_tarski(k9_relat_1(C_312, A_311), B_313) | ~r1_tarski(A_311, k1_relat_1(C_312)) | ~v1_funct_1(C_312) | ~v1_relat_1(C_312))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.18/1.99  tff(c_2318, plain, (r1_tarski('#skF_6', k10_relat_1('#skF_4', k1_relat_1('#skF_5'))) | ~r1_tarski('#skF_6', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1993, c_2295])).
% 5.18/1.99  tff(c_2348, plain, (r1_tarski('#skF_6', k10_relat_1('#skF_4', k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_1955, c_2318])).
% 5.18/1.99  tff(c_2365, plain, (r1_tarski('#skF_6', k1_relat_1(k5_relat_1('#skF_4', '#skF_5'))) | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10, c_2348])).
% 5.18/1.99  tff(c_2370, plain, (r1_tarski('#skF_6', k1_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_2365])).
% 5.18/1.99  tff(c_2372, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2020, c_2370])).
% 5.18/1.99  tff(c_2374, plain, (~r1_tarski('#skF_7', k1_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_58])).
% 5.18/1.99  tff(c_54, plain, (~r1_tarski('#skF_6', k1_relat_1(k5_relat_1('#skF_4', '#skF_5'))) | r1_tarski('#skF_7', k1_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.18/1.99  tff(c_2398, plain, (~r1_tarski('#skF_6', k1_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_2374, c_54])).
% 5.18/1.99  tff(c_2373, plain, (r1_tarski('#skF_6', k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_58])).
% 5.18/1.99  tff(c_56, plain, (r1_tarski(k9_relat_1('#skF_4', '#skF_6'), k1_relat_1('#skF_5')) | r1_tarski('#skF_7', k1_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.18/1.99  tff(c_2375, plain, (r1_tarski(k9_relat_1('#skF_4', '#skF_6'), k1_relat_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_2374, c_56])).
% 5.18/1.99  tff(c_2706, plain, (![A_379, C_380, B_381]: (r1_tarski(A_379, k10_relat_1(C_380, B_381)) | ~r1_tarski(k9_relat_1(C_380, A_379), B_381) | ~r1_tarski(A_379, k1_relat_1(C_380)) | ~v1_funct_1(C_380) | ~v1_relat_1(C_380))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.18/1.99  tff(c_2728, plain, (r1_tarski('#skF_6', k10_relat_1('#skF_4', k1_relat_1('#skF_5'))) | ~r1_tarski('#skF_6', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2375, c_2706])).
% 5.18/1.99  tff(c_2744, plain, (r1_tarski('#skF_6', k10_relat_1('#skF_4', k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_2373, c_2728])).
% 5.18/1.99  tff(c_2756, plain, (r1_tarski('#skF_6', k1_relat_1(k5_relat_1('#skF_4', '#skF_5'))) | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10, c_2744])).
% 5.18/1.99  tff(c_2762, plain, (r1_tarski('#skF_6', k1_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_2756])).
% 5.18/1.99  tff(c_2764, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2398, c_2762])).
% 5.18/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.18/1.99  
% 5.18/1.99  Inference rules
% 5.18/1.99  ----------------------
% 5.18/1.99  #Ref     : 0
% 5.18/1.99  #Sup     : 651
% 5.18/1.99  #Fact    : 0
% 5.18/1.99  #Define  : 0
% 5.18/1.99  #Split   : 13
% 5.18/1.99  #Chain   : 0
% 5.18/1.99  #Close   : 0
% 5.18/1.99  
% 5.18/1.99  Ordering : KBO
% 5.18/1.99  
% 5.18/1.99  Simplification rules
% 5.18/1.99  ----------------------
% 5.18/1.99  #Subsume      : 148
% 5.18/1.99  #Demod        : 120
% 5.18/1.99  #Tautology    : 22
% 5.18/1.99  #SimpNegUnit  : 4
% 5.18/1.99  #BackRed      : 0
% 5.18/1.99  
% 5.18/1.99  #Partial instantiations: 0
% 5.18/1.99  #Strategies tried      : 1
% 5.18/1.99  
% 5.18/1.99  Timing (in seconds)
% 5.18/1.99  ----------------------
% 5.18/1.99  Preprocessing        : 0.33
% 5.18/1.99  Parsing              : 0.17
% 5.18/1.99  CNF conversion       : 0.03
% 5.18/1.99  Main loop            : 0.87
% 5.18/1.99  Inferencing          : 0.28
% 5.18/1.99  Reduction            : 0.22
% 5.18/1.99  Demodulation         : 0.15
% 5.18/1.99  BG Simplification    : 0.04
% 5.18/1.99  Subsumption          : 0.27
% 5.18/1.99  Abstraction          : 0.04
% 5.18/1.99  MUC search           : 0.00
% 5.18/1.99  Cooper               : 0.00
% 5.18/1.99  Total                : 1.24
% 5.18/2.00  Index Insertion      : 0.00
% 5.18/2.00  Index Deletion       : 0.00
% 5.18/2.00  Index Matching       : 0.00
% 5.18/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
