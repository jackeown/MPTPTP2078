%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:57 EST 2020

% Result     : Theorem 9.81s
% Output     : CNFRefutation 9.81s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 584 expanded)
%              Number of leaves         :   26 ( 219 expanded)
%              Depth                    :   28
%              Number of atoms          :  221 (1619 expanded)
%              Number of equality atoms :   76 ( 532 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( k1_relat_1(B) = k1_tarski(A)
         => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(c_38,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_4')) != k2_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_44,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_28,plain,(
    ! [A_18] :
      ( k9_relat_1(A_18,k1_relat_1(A_18)) = k2_relat_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_40,plain,(
    k1_tarski('#skF_4') = k1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_49,plain,(
    r2_hidden('#skF_4',k1_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_4])).

tff(c_30,plain,(
    ! [B_20,A_19] :
      ( r2_hidden(k1_funct_1(B_20,A_19),k2_relat_1(B_20))
      | ~ r2_hidden(A_19,k1_relat_1(B_20))
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_32,plain,(
    ! [A_21,C_23] :
      ( r2_hidden(k4_tarski(A_21,k1_funct_1(C_23,A_21)),C_23)
      | ~ r2_hidden(A_21,k1_relat_1(C_23))
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_430,plain,(
    ! [A_80,C_81,B_82,D_83] :
      ( r2_hidden(A_80,k9_relat_1(C_81,B_82))
      | ~ r2_hidden(D_83,B_82)
      | ~ r2_hidden(k4_tarski(D_83,A_80),C_81)
      | ~ r2_hidden(D_83,k1_relat_1(C_81))
      | ~ v1_relat_1(C_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_487,plain,(
    ! [A_89,C_90,C_91] :
      ( r2_hidden(A_89,k9_relat_1(C_90,k1_tarski(C_91)))
      | ~ r2_hidden(k4_tarski(C_91,A_89),C_90)
      | ~ r2_hidden(C_91,k1_relat_1(C_90))
      | ~ v1_relat_1(C_90) ) ),
    inference(resolution,[status(thm)],[c_4,c_430])).

tff(c_211,plain,(
    ! [A_58,B_59,C_60] :
      ( r2_hidden('#skF_3'(A_58,B_59,C_60),k1_relat_1(C_60))
      | ~ r2_hidden(A_58,k9_relat_1(C_60,B_59))
      | ~ v1_relat_1(C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_62,plain,(
    ! [C_26,A_27] :
      ( C_26 = A_27
      | ~ r2_hidden(C_26,k1_tarski(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_65,plain,(
    ! [C_26] :
      ( C_26 = '#skF_4'
      | ~ r2_hidden(C_26,k1_relat_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_62])).

tff(c_215,plain,(
    ! [A_58,B_59] :
      ( '#skF_3'(A_58,B_59,'#skF_5') = '#skF_4'
      | ~ r2_hidden(A_58,k9_relat_1('#skF_5',B_59))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_211,c_65])).

tff(c_221,plain,(
    ! [A_58,B_59] :
      ( '#skF_3'(A_58,B_59,'#skF_5') = '#skF_4'
      | ~ r2_hidden(A_58,k9_relat_1('#skF_5',B_59)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_215])).

tff(c_501,plain,(
    ! [A_89,C_91] :
      ( '#skF_3'(A_89,k1_tarski(C_91),'#skF_5') = '#skF_4'
      | ~ r2_hidden(k4_tarski(C_91,A_89),'#skF_5')
      | ~ r2_hidden(C_91,k1_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_487,c_221])).

tff(c_527,plain,(
    ! [A_92,C_93] :
      ( '#skF_3'(A_92,k1_tarski(C_93),'#skF_5') = '#skF_4'
      | ~ r2_hidden(k4_tarski(C_93,A_92),'#skF_5')
      | ~ r2_hidden(C_93,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_501])).

tff(c_535,plain,(
    ! [A_21] :
      ( '#skF_3'(k1_funct_1('#skF_5',A_21),k1_tarski(A_21),'#skF_5') = '#skF_4'
      | ~ r2_hidden(A_21,k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_32,c_527])).

tff(c_542,plain,(
    ! [A_94] :
      ( '#skF_3'(k1_funct_1('#skF_5',A_94),k1_tarski(A_94),'#skF_5') = '#skF_4'
      | ~ r2_hidden(A_94,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_535])).

tff(c_560,plain,
    ( '#skF_3'(k1_funct_1('#skF_5','#skF_4'),k1_relat_1('#skF_5'),'#skF_5') = '#skF_4'
    | ~ r2_hidden('#skF_4',k1_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_542])).

tff(c_570,plain,(
    '#skF_3'(k1_funct_1('#skF_5','#skF_4'),k1_relat_1('#skF_5'),'#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_560])).

tff(c_24,plain,(
    ! [A_12,B_13,C_14] :
      ( r2_hidden(k4_tarski('#skF_3'(A_12,B_13,C_14),A_12),C_14)
      | ~ r2_hidden(A_12,k9_relat_1(C_14,B_13))
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_574,plain,
    ( r2_hidden(k4_tarski('#skF_4',k1_funct_1('#skF_5','#skF_4')),'#skF_5')
    | ~ r2_hidden(k1_funct_1('#skF_5','#skF_4'),k9_relat_1('#skF_5',k1_relat_1('#skF_5')))
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_570,c_24])).

tff(c_590,plain,
    ( r2_hidden(k4_tarski('#skF_4',k1_funct_1('#skF_5','#skF_4')),'#skF_5')
    | ~ r2_hidden(k1_funct_1('#skF_5','#skF_4'),k9_relat_1('#skF_5',k1_relat_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_574])).

tff(c_616,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_4'),k9_relat_1('#skF_5',k1_relat_1('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_590])).

tff(c_619,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_4'),k2_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_616])).

tff(c_621,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_4'),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_619])).

tff(c_624,plain,
    ( ~ r2_hidden('#skF_4',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_621])).

tff(c_628,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_49,c_624])).

tff(c_630,plain,(
    r2_hidden(k1_funct_1('#skF_5','#skF_4'),k9_relat_1('#skF_5',k1_relat_1('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_590])).

tff(c_708,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_4'),k2_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_630])).

tff(c_719,plain,(
    r2_hidden(k1_funct_1('#skF_5','#skF_4'),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_708])).

tff(c_12,plain,(
    ! [A_1,B_2] :
      ( '#skF_1'(A_1,B_2) = A_1
      | r2_hidden('#skF_2'(A_1,B_2),B_2)
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26,plain,(
    ! [A_12,B_13,C_14] :
      ( r2_hidden('#skF_3'(A_12,B_13,C_14),k1_relat_1(C_14))
      | ~ r2_hidden(A_12,k9_relat_1(C_14,B_13))
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_189,plain,(
    ! [B_55,A_56] :
      ( r2_hidden(k1_funct_1(B_55,A_56),k2_relat_1(B_55))
      | ~ r2_hidden(A_56,k1_relat_1(B_55))
      | ~ v1_funct_1(B_55)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_134,plain,(
    ! [A_46,B_47,C_48] :
      ( r2_hidden('#skF_3'(A_46,B_47,C_48),B_47)
      | ~ r2_hidden(A_46,k9_relat_1(C_48,B_47))
      | ~ v1_relat_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_151,plain,(
    ! [A_52,C_53] :
      ( '#skF_3'(A_52,k1_relat_1('#skF_5'),C_53) = '#skF_4'
      | ~ r2_hidden(A_52,k9_relat_1(C_53,k1_relat_1('#skF_5')))
      | ~ v1_relat_1(C_53) ) ),
    inference(resolution,[status(thm)],[c_134,c_65])).

tff(c_167,plain,(
    ! [A_52] :
      ( '#skF_3'(A_52,k1_relat_1('#skF_5'),'#skF_5') = '#skF_4'
      | ~ r2_hidden(A_52,k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_151])).

tff(c_172,plain,(
    ! [A_52] :
      ( '#skF_3'(A_52,k1_relat_1('#skF_5'),'#skF_5') = '#skF_4'
      | ~ r2_hidden(A_52,k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44,c_167])).

tff(c_193,plain,(
    ! [A_56] :
      ( '#skF_3'(k1_funct_1('#skF_5',A_56),k1_relat_1('#skF_5'),'#skF_5') = '#skF_4'
      | ~ r2_hidden(A_56,k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_189,c_172])).

tff(c_196,plain,(
    ! [A_56] :
      ( '#skF_3'(k1_funct_1('#skF_5',A_56),k1_relat_1('#skF_5'),'#skF_5') = '#skF_4'
      | ~ r2_hidden(A_56,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_193])).

tff(c_353,plain,(
    ! [A_71,B_72,C_73] :
      ( r2_hidden(k4_tarski('#skF_3'(A_71,B_72,C_73),A_71),C_73)
      | ~ r2_hidden(A_71,k9_relat_1(C_73,B_72))
      | ~ v1_relat_1(C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_34,plain,(
    ! [C_23,A_21,B_22] :
      ( k1_funct_1(C_23,A_21) = B_22
      | ~ r2_hidden(k4_tarski(A_21,B_22),C_23)
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_406,plain,(
    ! [C_76,A_77,B_78] :
      ( k1_funct_1(C_76,'#skF_3'(A_77,B_78,C_76)) = A_77
      | ~ v1_funct_1(C_76)
      | ~ r2_hidden(A_77,k9_relat_1(C_76,B_78))
      | ~ v1_relat_1(C_76) ) ),
    inference(resolution,[status(thm)],[c_353,c_34])).

tff(c_1087,plain,(
    ! [A_123,A_124] :
      ( k1_funct_1(A_123,'#skF_3'(A_124,k1_relat_1(A_123),A_123)) = A_124
      | ~ v1_funct_1(A_123)
      | ~ r2_hidden(A_124,k2_relat_1(A_123))
      | ~ v1_relat_1(A_123)
      | ~ v1_relat_1(A_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_406])).

tff(c_1120,plain,(
    ! [A_56] :
      ( k1_funct_1('#skF_5',A_56) = k1_funct_1('#skF_5','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | ~ r2_hidden(k1_funct_1('#skF_5',A_56),k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ r2_hidden(A_56,k1_relat_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_1087])).

tff(c_1135,plain,(
    ! [A_125] :
      ( k1_funct_1('#skF_5',A_125) = k1_funct_1('#skF_5','#skF_4')
      | ~ r2_hidden(k1_funct_1('#skF_5',A_125),k2_relat_1('#skF_5'))
      | ~ r2_hidden(A_125,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44,c_42,c_1120])).

tff(c_1146,plain,(
    ! [A_19] :
      ( k1_funct_1('#skF_5',A_19) = k1_funct_1('#skF_5','#skF_4')
      | ~ r2_hidden(A_19,k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30,c_1135])).

tff(c_1156,plain,(
    ! [A_126] :
      ( k1_funct_1('#skF_5',A_126) = k1_funct_1('#skF_5','#skF_4')
      | ~ r2_hidden(A_126,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_1146])).

tff(c_1168,plain,(
    ! [A_12,B_13] :
      ( k1_funct_1('#skF_5','#skF_3'(A_12,B_13,'#skF_5')) = k1_funct_1('#skF_5','#skF_4')
      | ~ r2_hidden(A_12,k9_relat_1('#skF_5',B_13))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_26,c_1156])).

tff(c_1194,plain,(
    ! [A_127,B_128] :
      ( k1_funct_1('#skF_5','#skF_3'(A_127,B_128,'#skF_5')) = k1_funct_1('#skF_5','#skF_4')
      | ~ r2_hidden(A_127,k9_relat_1('#skF_5',B_128)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1168])).

tff(c_1229,plain,(
    ! [A_127] :
      ( k1_funct_1('#skF_5','#skF_3'(A_127,k1_relat_1('#skF_5'),'#skF_5')) = k1_funct_1('#skF_5','#skF_4')
      | ~ r2_hidden(A_127,k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1194])).

tff(c_1245,plain,(
    ! [A_129] :
      ( k1_funct_1('#skF_5','#skF_3'(A_129,k1_relat_1('#skF_5'),'#skF_5')) = k1_funct_1('#skF_5','#skF_4')
      | ~ r2_hidden(A_129,k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1229])).

tff(c_423,plain,(
    ! [A_18,A_77] :
      ( k1_funct_1(A_18,'#skF_3'(A_77,k1_relat_1(A_18),A_18)) = A_77
      | ~ v1_funct_1(A_18)
      | ~ r2_hidden(A_77,k2_relat_1(A_18))
      | ~ v1_relat_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_406])).

tff(c_1251,plain,(
    ! [A_129] :
      ( k1_funct_1('#skF_5','#skF_4') = A_129
      | ~ v1_funct_1('#skF_5')
      | ~ r2_hidden(A_129,k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ r2_hidden(A_129,k2_relat_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1245,c_423])).

tff(c_1329,plain,(
    ! [A_134] :
      ( k1_funct_1('#skF_5','#skF_4') = A_134
      | ~ r2_hidden(A_134,k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44,c_42,c_1251])).

tff(c_1555,plain,(
    ! [A_141] :
      ( '#skF_2'(A_141,k2_relat_1('#skF_5')) = k1_funct_1('#skF_5','#skF_4')
      | '#skF_1'(A_141,k2_relat_1('#skF_5')) = A_141
      | k2_relat_1('#skF_5') = k1_tarski(A_141) ) ),
    inference(resolution,[status(thm)],[c_12,c_1329])).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( '#skF_1'(A_1,B_2) = A_1
      | '#skF_2'(A_1,B_2) != A_1
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1571,plain,(
    ! [A_141] :
      ( '#skF_1'(A_141,k2_relat_1('#skF_5')) = A_141
      | k1_funct_1('#skF_5','#skF_4') != A_141
      | k2_relat_1('#skF_5') = k1_tarski(A_141)
      | '#skF_1'(A_141,k2_relat_1('#skF_5')) = A_141
      | k2_relat_1('#skF_5') = k1_tarski(A_141) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1555,c_8])).

tff(c_13203,plain,(
    ! [A_457] :
      ( k1_funct_1('#skF_5','#skF_4') != A_457
      | k2_relat_1('#skF_5') = k1_tarski(A_457)
      | '#skF_1'(A_457,k2_relat_1('#skF_5')) = A_457 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_1571])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | '#skF_2'(A_1,B_2) != A_1
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_13475,plain,(
    ! [A_461] :
      ( ~ r2_hidden(A_461,k2_relat_1('#skF_5'))
      | '#skF_2'(A_461,k2_relat_1('#skF_5')) != A_461
      | k2_relat_1('#skF_5') = k1_tarski(A_461)
      | k1_funct_1('#skF_5','#skF_4') != A_461
      | k2_relat_1('#skF_5') = k1_tarski(A_461) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13203,c_6])).

tff(c_13500,plain,
    ( '#skF_2'(k1_funct_1('#skF_5','#skF_4'),k2_relat_1('#skF_5')) != k1_funct_1('#skF_5','#skF_4')
    | k1_tarski(k1_funct_1('#skF_5','#skF_4')) = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_719,c_13475])).

tff(c_13536,plain,(
    '#skF_2'(k1_funct_1('#skF_5','#skF_4'),k2_relat_1('#skF_5')) != k1_funct_1('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_38,c_13500])).

tff(c_1366,plain,(
    ! [A_1] :
      ( '#skF_2'(A_1,k2_relat_1('#skF_5')) = k1_funct_1('#skF_5','#skF_4')
      | '#skF_1'(A_1,k2_relat_1('#skF_5')) = A_1
      | k2_relat_1('#skF_5') = k1_tarski(A_1) ) ),
    inference(resolution,[status(thm)],[c_12,c_1329])).

tff(c_13553,plain,
    ( '#skF_1'(k1_funct_1('#skF_5','#skF_4'),k2_relat_1('#skF_5')) = k1_funct_1('#skF_5','#skF_4')
    | k1_tarski(k1_funct_1('#skF_5','#skF_4')) = k2_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1366,c_13536])).

tff(c_13559,plain,(
    '#skF_1'(k1_funct_1('#skF_5','#skF_4'),k2_relat_1('#skF_5')) = k1_funct_1('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_13553])).

tff(c_10,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r2_hidden('#skF_2'(A_1,B_2),B_2)
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1365,plain,(
    ! [A_1] :
      ( '#skF_2'(A_1,k2_relat_1('#skF_5')) = k1_funct_1('#skF_5','#skF_4')
      | ~ r2_hidden('#skF_1'(A_1,k2_relat_1('#skF_5')),k2_relat_1('#skF_5'))
      | k2_relat_1('#skF_5') = k1_tarski(A_1) ) ),
    inference(resolution,[status(thm)],[c_10,c_1329])).

tff(c_13575,plain,
    ( '#skF_2'(k1_funct_1('#skF_5','#skF_4'),k2_relat_1('#skF_5')) = k1_funct_1('#skF_5','#skF_4')
    | ~ r2_hidden(k1_funct_1('#skF_5','#skF_4'),k2_relat_1('#skF_5'))
    | k1_tarski(k1_funct_1('#skF_5','#skF_4')) = k2_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_13559,c_1365])).

tff(c_13596,plain,
    ( '#skF_2'(k1_funct_1('#skF_5','#skF_4'),k2_relat_1('#skF_5')) = k1_funct_1('#skF_5','#skF_4')
    | k1_tarski(k1_funct_1('#skF_5','#skF_4')) = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_719,c_13575])).

tff(c_13598,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_13536,c_13596])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:04:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.81/3.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.81/3.36  
% 9.81/3.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.81/3.36  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 9.81/3.36  
% 9.81/3.36  %Foreground sorts:
% 9.81/3.36  
% 9.81/3.36  
% 9.81/3.36  %Background operators:
% 9.81/3.36  
% 9.81/3.36  
% 9.81/3.36  %Foreground operators:
% 9.81/3.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.81/3.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.81/3.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.81/3.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.81/3.36  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.81/3.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.81/3.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.81/3.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.81/3.36  tff('#skF_5', type, '#skF_5': $i).
% 9.81/3.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.81/3.36  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.81/3.36  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.81/3.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.81/3.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.81/3.36  tff('#skF_4', type, '#skF_4': $i).
% 9.81/3.36  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 9.81/3.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.81/3.36  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.81/3.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.81/3.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.81/3.36  
% 9.81/3.38  tff(f_80, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 9.81/3.38  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 9.81/3.38  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 9.81/3.38  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 9.81/3.38  tff(f_71, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 9.81/3.38  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 9.81/3.38  tff(c_38, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_4'))!=k2_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.81/3.38  tff(c_44, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.81/3.38  tff(c_28, plain, (![A_18]: (k9_relat_1(A_18, k1_relat_1(A_18))=k2_relat_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.81/3.38  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.81/3.38  tff(c_40, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.81/3.38  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.81/3.38  tff(c_49, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_4])).
% 9.81/3.38  tff(c_30, plain, (![B_20, A_19]: (r2_hidden(k1_funct_1(B_20, A_19), k2_relat_1(B_20)) | ~r2_hidden(A_19, k1_relat_1(B_20)) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.81/3.38  tff(c_32, plain, (![A_21, C_23]: (r2_hidden(k4_tarski(A_21, k1_funct_1(C_23, A_21)), C_23) | ~r2_hidden(A_21, k1_relat_1(C_23)) | ~v1_funct_1(C_23) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.81/3.38  tff(c_430, plain, (![A_80, C_81, B_82, D_83]: (r2_hidden(A_80, k9_relat_1(C_81, B_82)) | ~r2_hidden(D_83, B_82) | ~r2_hidden(k4_tarski(D_83, A_80), C_81) | ~r2_hidden(D_83, k1_relat_1(C_81)) | ~v1_relat_1(C_81))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.81/3.38  tff(c_487, plain, (![A_89, C_90, C_91]: (r2_hidden(A_89, k9_relat_1(C_90, k1_tarski(C_91))) | ~r2_hidden(k4_tarski(C_91, A_89), C_90) | ~r2_hidden(C_91, k1_relat_1(C_90)) | ~v1_relat_1(C_90))), inference(resolution, [status(thm)], [c_4, c_430])).
% 9.81/3.38  tff(c_211, plain, (![A_58, B_59, C_60]: (r2_hidden('#skF_3'(A_58, B_59, C_60), k1_relat_1(C_60)) | ~r2_hidden(A_58, k9_relat_1(C_60, B_59)) | ~v1_relat_1(C_60))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.81/3.38  tff(c_62, plain, (![C_26, A_27]: (C_26=A_27 | ~r2_hidden(C_26, k1_tarski(A_27)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.81/3.38  tff(c_65, plain, (![C_26]: (C_26='#skF_4' | ~r2_hidden(C_26, k1_relat_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_40, c_62])).
% 9.81/3.38  tff(c_215, plain, (![A_58, B_59]: ('#skF_3'(A_58, B_59, '#skF_5')='#skF_4' | ~r2_hidden(A_58, k9_relat_1('#skF_5', B_59)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_211, c_65])).
% 9.81/3.38  tff(c_221, plain, (![A_58, B_59]: ('#skF_3'(A_58, B_59, '#skF_5')='#skF_4' | ~r2_hidden(A_58, k9_relat_1('#skF_5', B_59)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_215])).
% 9.81/3.38  tff(c_501, plain, (![A_89, C_91]: ('#skF_3'(A_89, k1_tarski(C_91), '#skF_5')='#skF_4' | ~r2_hidden(k4_tarski(C_91, A_89), '#skF_5') | ~r2_hidden(C_91, k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_487, c_221])).
% 9.81/3.38  tff(c_527, plain, (![A_92, C_93]: ('#skF_3'(A_92, k1_tarski(C_93), '#skF_5')='#skF_4' | ~r2_hidden(k4_tarski(C_93, A_92), '#skF_5') | ~r2_hidden(C_93, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_501])).
% 9.81/3.38  tff(c_535, plain, (![A_21]: ('#skF_3'(k1_funct_1('#skF_5', A_21), k1_tarski(A_21), '#skF_5')='#skF_4' | ~r2_hidden(A_21, k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_32, c_527])).
% 9.81/3.38  tff(c_542, plain, (![A_94]: ('#skF_3'(k1_funct_1('#skF_5', A_94), k1_tarski(A_94), '#skF_5')='#skF_4' | ~r2_hidden(A_94, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_535])).
% 9.81/3.38  tff(c_560, plain, ('#skF_3'(k1_funct_1('#skF_5', '#skF_4'), k1_relat_1('#skF_5'), '#skF_5')='#skF_4' | ~r2_hidden('#skF_4', k1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_542])).
% 9.81/3.38  tff(c_570, plain, ('#skF_3'(k1_funct_1('#skF_5', '#skF_4'), k1_relat_1('#skF_5'), '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_49, c_560])).
% 9.81/3.38  tff(c_24, plain, (![A_12, B_13, C_14]: (r2_hidden(k4_tarski('#skF_3'(A_12, B_13, C_14), A_12), C_14) | ~r2_hidden(A_12, k9_relat_1(C_14, B_13)) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.81/3.38  tff(c_574, plain, (r2_hidden(k4_tarski('#skF_4', k1_funct_1('#skF_5', '#skF_4')), '#skF_5') | ~r2_hidden(k1_funct_1('#skF_5', '#skF_4'), k9_relat_1('#skF_5', k1_relat_1('#skF_5'))) | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_570, c_24])).
% 9.81/3.38  tff(c_590, plain, (r2_hidden(k4_tarski('#skF_4', k1_funct_1('#skF_5', '#skF_4')), '#skF_5') | ~r2_hidden(k1_funct_1('#skF_5', '#skF_4'), k9_relat_1('#skF_5', k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_574])).
% 9.81/3.38  tff(c_616, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_4'), k9_relat_1('#skF_5', k1_relat_1('#skF_5')))), inference(splitLeft, [status(thm)], [c_590])).
% 9.81/3.38  tff(c_619, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_4'), k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_28, c_616])).
% 9.81/3.38  tff(c_621, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_4'), k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_619])).
% 9.81/3.38  tff(c_624, plain, (~r2_hidden('#skF_4', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_621])).
% 9.81/3.38  tff(c_628, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_49, c_624])).
% 9.81/3.38  tff(c_630, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_4'), k9_relat_1('#skF_5', k1_relat_1('#skF_5')))), inference(splitRight, [status(thm)], [c_590])).
% 9.81/3.38  tff(c_708, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_4'), k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_28, c_630])).
% 9.81/3.38  tff(c_719, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_4'), k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_708])).
% 9.81/3.38  tff(c_12, plain, (![A_1, B_2]: ('#skF_1'(A_1, B_2)=A_1 | r2_hidden('#skF_2'(A_1, B_2), B_2) | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.81/3.38  tff(c_26, plain, (![A_12, B_13, C_14]: (r2_hidden('#skF_3'(A_12, B_13, C_14), k1_relat_1(C_14)) | ~r2_hidden(A_12, k9_relat_1(C_14, B_13)) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.81/3.38  tff(c_189, plain, (![B_55, A_56]: (r2_hidden(k1_funct_1(B_55, A_56), k2_relat_1(B_55)) | ~r2_hidden(A_56, k1_relat_1(B_55)) | ~v1_funct_1(B_55) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.81/3.38  tff(c_134, plain, (![A_46, B_47, C_48]: (r2_hidden('#skF_3'(A_46, B_47, C_48), B_47) | ~r2_hidden(A_46, k9_relat_1(C_48, B_47)) | ~v1_relat_1(C_48))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.81/3.38  tff(c_151, plain, (![A_52, C_53]: ('#skF_3'(A_52, k1_relat_1('#skF_5'), C_53)='#skF_4' | ~r2_hidden(A_52, k9_relat_1(C_53, k1_relat_1('#skF_5'))) | ~v1_relat_1(C_53))), inference(resolution, [status(thm)], [c_134, c_65])).
% 9.81/3.38  tff(c_167, plain, (![A_52]: ('#skF_3'(A_52, k1_relat_1('#skF_5'), '#skF_5')='#skF_4' | ~r2_hidden(A_52, k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_151])).
% 9.81/3.38  tff(c_172, plain, (![A_52]: ('#skF_3'(A_52, k1_relat_1('#skF_5'), '#skF_5')='#skF_4' | ~r2_hidden(A_52, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44, c_167])).
% 9.81/3.38  tff(c_193, plain, (![A_56]: ('#skF_3'(k1_funct_1('#skF_5', A_56), k1_relat_1('#skF_5'), '#skF_5')='#skF_4' | ~r2_hidden(A_56, k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_189, c_172])).
% 9.81/3.38  tff(c_196, plain, (![A_56]: ('#skF_3'(k1_funct_1('#skF_5', A_56), k1_relat_1('#skF_5'), '#skF_5')='#skF_4' | ~r2_hidden(A_56, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_193])).
% 9.81/3.38  tff(c_353, plain, (![A_71, B_72, C_73]: (r2_hidden(k4_tarski('#skF_3'(A_71, B_72, C_73), A_71), C_73) | ~r2_hidden(A_71, k9_relat_1(C_73, B_72)) | ~v1_relat_1(C_73))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.81/3.38  tff(c_34, plain, (![C_23, A_21, B_22]: (k1_funct_1(C_23, A_21)=B_22 | ~r2_hidden(k4_tarski(A_21, B_22), C_23) | ~v1_funct_1(C_23) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.81/3.38  tff(c_406, plain, (![C_76, A_77, B_78]: (k1_funct_1(C_76, '#skF_3'(A_77, B_78, C_76))=A_77 | ~v1_funct_1(C_76) | ~r2_hidden(A_77, k9_relat_1(C_76, B_78)) | ~v1_relat_1(C_76))), inference(resolution, [status(thm)], [c_353, c_34])).
% 9.81/3.38  tff(c_1087, plain, (![A_123, A_124]: (k1_funct_1(A_123, '#skF_3'(A_124, k1_relat_1(A_123), A_123))=A_124 | ~v1_funct_1(A_123) | ~r2_hidden(A_124, k2_relat_1(A_123)) | ~v1_relat_1(A_123) | ~v1_relat_1(A_123))), inference(superposition, [status(thm), theory('equality')], [c_28, c_406])).
% 9.81/3.38  tff(c_1120, plain, (![A_56]: (k1_funct_1('#skF_5', A_56)=k1_funct_1('#skF_5', '#skF_4') | ~v1_funct_1('#skF_5') | ~r2_hidden(k1_funct_1('#skF_5', A_56), k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r2_hidden(A_56, k1_relat_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_196, c_1087])).
% 9.81/3.38  tff(c_1135, plain, (![A_125]: (k1_funct_1('#skF_5', A_125)=k1_funct_1('#skF_5', '#skF_4') | ~r2_hidden(k1_funct_1('#skF_5', A_125), k2_relat_1('#skF_5')) | ~r2_hidden(A_125, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44, c_42, c_1120])).
% 9.81/3.38  tff(c_1146, plain, (![A_19]: (k1_funct_1('#skF_5', A_19)=k1_funct_1('#skF_5', '#skF_4') | ~r2_hidden(A_19, k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_30, c_1135])).
% 9.81/3.38  tff(c_1156, plain, (![A_126]: (k1_funct_1('#skF_5', A_126)=k1_funct_1('#skF_5', '#skF_4') | ~r2_hidden(A_126, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_1146])).
% 9.81/3.38  tff(c_1168, plain, (![A_12, B_13]: (k1_funct_1('#skF_5', '#skF_3'(A_12, B_13, '#skF_5'))=k1_funct_1('#skF_5', '#skF_4') | ~r2_hidden(A_12, k9_relat_1('#skF_5', B_13)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_26, c_1156])).
% 9.81/3.38  tff(c_1194, plain, (![A_127, B_128]: (k1_funct_1('#skF_5', '#skF_3'(A_127, B_128, '#skF_5'))=k1_funct_1('#skF_5', '#skF_4') | ~r2_hidden(A_127, k9_relat_1('#skF_5', B_128)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1168])).
% 9.81/3.38  tff(c_1229, plain, (![A_127]: (k1_funct_1('#skF_5', '#skF_3'(A_127, k1_relat_1('#skF_5'), '#skF_5'))=k1_funct_1('#skF_5', '#skF_4') | ~r2_hidden(A_127, k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1194])).
% 9.81/3.38  tff(c_1245, plain, (![A_129]: (k1_funct_1('#skF_5', '#skF_3'(A_129, k1_relat_1('#skF_5'), '#skF_5'))=k1_funct_1('#skF_5', '#skF_4') | ~r2_hidden(A_129, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1229])).
% 9.81/3.38  tff(c_423, plain, (![A_18, A_77]: (k1_funct_1(A_18, '#skF_3'(A_77, k1_relat_1(A_18), A_18))=A_77 | ~v1_funct_1(A_18) | ~r2_hidden(A_77, k2_relat_1(A_18)) | ~v1_relat_1(A_18) | ~v1_relat_1(A_18))), inference(superposition, [status(thm), theory('equality')], [c_28, c_406])).
% 9.81/3.38  tff(c_1251, plain, (![A_129]: (k1_funct_1('#skF_5', '#skF_4')=A_129 | ~v1_funct_1('#skF_5') | ~r2_hidden(A_129, k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r2_hidden(A_129, k2_relat_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1245, c_423])).
% 9.81/3.38  tff(c_1329, plain, (![A_134]: (k1_funct_1('#skF_5', '#skF_4')=A_134 | ~r2_hidden(A_134, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44, c_42, c_1251])).
% 9.81/3.38  tff(c_1555, plain, (![A_141]: ('#skF_2'(A_141, k2_relat_1('#skF_5'))=k1_funct_1('#skF_5', '#skF_4') | '#skF_1'(A_141, k2_relat_1('#skF_5'))=A_141 | k2_relat_1('#skF_5')=k1_tarski(A_141))), inference(resolution, [status(thm)], [c_12, c_1329])).
% 9.81/3.38  tff(c_8, plain, (![A_1, B_2]: ('#skF_1'(A_1, B_2)=A_1 | '#skF_2'(A_1, B_2)!=A_1 | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.81/3.38  tff(c_1571, plain, (![A_141]: ('#skF_1'(A_141, k2_relat_1('#skF_5'))=A_141 | k1_funct_1('#skF_5', '#skF_4')!=A_141 | k2_relat_1('#skF_5')=k1_tarski(A_141) | '#skF_1'(A_141, k2_relat_1('#skF_5'))=A_141 | k2_relat_1('#skF_5')=k1_tarski(A_141))), inference(superposition, [status(thm), theory('equality')], [c_1555, c_8])).
% 9.81/3.38  tff(c_13203, plain, (![A_457]: (k1_funct_1('#skF_5', '#skF_4')!=A_457 | k2_relat_1('#skF_5')=k1_tarski(A_457) | '#skF_1'(A_457, k2_relat_1('#skF_5'))=A_457)), inference(factorization, [status(thm), theory('equality')], [c_1571])).
% 9.81/3.38  tff(c_6, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | '#skF_2'(A_1, B_2)!=A_1 | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.81/3.38  tff(c_13475, plain, (![A_461]: (~r2_hidden(A_461, k2_relat_1('#skF_5')) | '#skF_2'(A_461, k2_relat_1('#skF_5'))!=A_461 | k2_relat_1('#skF_5')=k1_tarski(A_461) | k1_funct_1('#skF_5', '#skF_4')!=A_461 | k2_relat_1('#skF_5')=k1_tarski(A_461))), inference(superposition, [status(thm), theory('equality')], [c_13203, c_6])).
% 9.81/3.38  tff(c_13500, plain, ('#skF_2'(k1_funct_1('#skF_5', '#skF_4'), k2_relat_1('#skF_5'))!=k1_funct_1('#skF_5', '#skF_4') | k1_tarski(k1_funct_1('#skF_5', '#skF_4'))=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_719, c_13475])).
% 9.81/3.38  tff(c_13536, plain, ('#skF_2'(k1_funct_1('#skF_5', '#skF_4'), k2_relat_1('#skF_5'))!=k1_funct_1('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_38, c_38, c_13500])).
% 9.81/3.38  tff(c_1366, plain, (![A_1]: ('#skF_2'(A_1, k2_relat_1('#skF_5'))=k1_funct_1('#skF_5', '#skF_4') | '#skF_1'(A_1, k2_relat_1('#skF_5'))=A_1 | k2_relat_1('#skF_5')=k1_tarski(A_1))), inference(resolution, [status(thm)], [c_12, c_1329])).
% 9.81/3.38  tff(c_13553, plain, ('#skF_1'(k1_funct_1('#skF_5', '#skF_4'), k2_relat_1('#skF_5'))=k1_funct_1('#skF_5', '#skF_4') | k1_tarski(k1_funct_1('#skF_5', '#skF_4'))=k2_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1366, c_13536])).
% 9.81/3.38  tff(c_13559, plain, ('#skF_1'(k1_funct_1('#skF_5', '#skF_4'), k2_relat_1('#skF_5'))=k1_funct_1('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_38, c_13553])).
% 9.81/3.38  tff(c_10, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r2_hidden('#skF_2'(A_1, B_2), B_2) | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.81/3.38  tff(c_1365, plain, (![A_1]: ('#skF_2'(A_1, k2_relat_1('#skF_5'))=k1_funct_1('#skF_5', '#skF_4') | ~r2_hidden('#skF_1'(A_1, k2_relat_1('#skF_5')), k2_relat_1('#skF_5')) | k2_relat_1('#skF_5')=k1_tarski(A_1))), inference(resolution, [status(thm)], [c_10, c_1329])).
% 9.81/3.38  tff(c_13575, plain, ('#skF_2'(k1_funct_1('#skF_5', '#skF_4'), k2_relat_1('#skF_5'))=k1_funct_1('#skF_5', '#skF_4') | ~r2_hidden(k1_funct_1('#skF_5', '#skF_4'), k2_relat_1('#skF_5')) | k1_tarski(k1_funct_1('#skF_5', '#skF_4'))=k2_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_13559, c_1365])).
% 9.81/3.38  tff(c_13596, plain, ('#skF_2'(k1_funct_1('#skF_5', '#skF_4'), k2_relat_1('#skF_5'))=k1_funct_1('#skF_5', '#skF_4') | k1_tarski(k1_funct_1('#skF_5', '#skF_4'))=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_719, c_13575])).
% 9.81/3.38  tff(c_13598, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_13536, c_13596])).
% 9.81/3.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.81/3.38  
% 9.81/3.38  Inference rules
% 9.81/3.38  ----------------------
% 9.81/3.38  #Ref     : 0
% 9.81/3.38  #Sup     : 2900
% 9.81/3.38  #Fact    : 4
% 9.81/3.38  #Define  : 0
% 9.81/3.38  #Split   : 8
% 9.81/3.38  #Chain   : 0
% 9.81/3.38  #Close   : 0
% 9.81/3.38  
% 9.81/3.38  Ordering : KBO
% 9.81/3.38  
% 9.81/3.38  Simplification rules
% 9.81/3.38  ----------------------
% 9.81/3.38  #Subsume      : 788
% 9.81/3.38  #Demod        : 2792
% 9.81/3.38  #Tautology    : 718
% 9.81/3.38  #SimpNegUnit  : 19
% 9.81/3.38  #BackRed      : 0
% 9.81/3.38  
% 9.81/3.38  #Partial instantiations: 0
% 9.81/3.38  #Strategies tried      : 1
% 9.81/3.38  
% 9.81/3.38  Timing (in seconds)
% 9.81/3.38  ----------------------
% 9.81/3.38  Preprocessing        : 0.30
% 9.81/3.38  Parsing              : 0.15
% 9.81/3.38  CNF conversion       : 0.02
% 9.81/3.38  Main loop            : 2.26
% 9.81/3.38  Inferencing          : 0.70
% 9.81/3.38  Reduction            : 0.70
% 9.81/3.38  Demodulation         : 0.48
% 9.81/3.38  BG Simplification    : 0.09
% 9.81/3.38  Subsumption          : 0.63
% 9.81/3.38  Abstraction          : 0.13
% 9.81/3.38  MUC search           : 0.00
% 9.81/3.38  Cooper               : 0.00
% 9.81/3.38  Total                : 2.60
% 9.81/3.38  Index Insertion      : 0.00
% 9.81/3.38  Index Deletion       : 0.00
% 9.81/3.38  Index Matching       : 0.00
% 9.81/3.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
