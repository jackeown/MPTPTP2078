%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:38 EST 2020

% Result     : Theorem 7.37s
% Output     : CNFRefutation 7.54s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 434 expanded)
%              Number of leaves         :   29 ( 150 expanded)
%              Depth                    :   13
%              Number of atoms          :  275 (1231 expanded)
%              Number of equality atoms :   41 ( 128 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_117,negated_conjecture,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_42,axiom,(
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

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_100,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
           => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k5_relat_1(A_6,B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_34,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_24,plain,(
    ! [A_26,B_27] :
      ( v1_funct_1(k7_relat_1(A_26,B_27))
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_30,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(k7_relat_1(A_8,B_9))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,(
    ! [A_41,B_42] :
      ( ~ r2_hidden('#skF_1'(A_41,B_42),B_42)
      | r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_57,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_52])).

tff(c_16,plain,(
    ! [A_16,B_18] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_16,B_18)),k1_relat_1(A_16))
      | ~ v1_relat_1(B_18)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_48,plain,
    ( r1_tarski('#skF_4',k1_relat_1('#skF_2'))
    | r1_tarski('#skF_5',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_59,plain,(
    r1_tarski('#skF_5',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_71,plain,(
    ! [C_50,B_51,A_52] :
      ( r2_hidden(C_50,B_51)
      | ~ r2_hidden(C_50,A_52)
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_122,plain,(
    ! [A_58,B_59,B_60] :
      ( r2_hidden('#skF_1'(A_58,B_59),B_60)
      | ~ r1_tarski(A_58,B_60)
      | r1_tarski(A_58,B_59) ) ),
    inference(resolution,[status(thm)],[c_6,c_71])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_332,plain,(
    ! [A_71,B_72,B_73,B_74] :
      ( r2_hidden('#skF_1'(A_71,B_72),B_73)
      | ~ r1_tarski(B_74,B_73)
      | ~ r1_tarski(A_71,B_74)
      | r1_tarski(A_71,B_72) ) ),
    inference(resolution,[status(thm)],[c_122,c_2])).

tff(c_348,plain,(
    ! [A_75,B_76] :
      ( r2_hidden('#skF_1'(A_75,B_76),k1_relat_1(k5_relat_1('#skF_2','#skF_3')))
      | ~ r1_tarski(A_75,'#skF_5')
      | r1_tarski(A_75,B_76) ) ),
    inference(resolution,[status(thm)],[c_59,c_332])).

tff(c_661,plain,(
    ! [A_87,B_88,B_89] :
      ( r2_hidden('#skF_1'(A_87,B_88),B_89)
      | ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_2','#skF_3')),B_89)
      | ~ r1_tarski(A_87,'#skF_5')
      | r1_tarski(A_87,B_88) ) ),
    inference(resolution,[status(thm)],[c_348,c_2])).

tff(c_673,plain,(
    ! [A_87,B_88] :
      ( r2_hidden('#skF_1'(A_87,B_88),k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_87,'#skF_5')
      | r1_tarski(A_87,B_88)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_661])).

tff(c_684,plain,(
    ! [A_90,B_91] :
      ( r2_hidden('#skF_1'(A_90,B_91),k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_90,'#skF_5')
      | r1_tarski(A_90,B_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_673])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_693,plain,(
    ! [A_92] :
      ( ~ r1_tarski(A_92,'#skF_5')
      | r1_tarski(A_92,k1_relat_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_684,c_4])).

tff(c_42,plain,
    ( r1_tarski('#skF_4',k1_relat_1('#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_2','#skF_5'),k1_relat_1('#skF_3'))
    | ~ r1_tarski('#skF_5',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_165,plain,(
    ~ r1_tarski('#skF_5',k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_705,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_693,c_165])).

tff(c_717,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_705])).

tff(c_719,plain,(
    r1_tarski('#skF_5',k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_22,plain,(
    ! [B_25,A_24] :
      ( k1_relat_1(k7_relat_1(B_25,A_24)) = A_24
      | ~ r1_tarski(A_24,k1_relat_1(B_25))
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_722,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_5')) = '#skF_5'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_719,c_22])).

tff(c_725,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_722])).

tff(c_75,plain,(
    ! [B_53,A_54] :
      ( k1_relat_1(k7_relat_1(B_53,A_54)) = A_54
      | ~ r1_tarski(A_54,k1_relat_1(B_53))
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_88,plain,(
    ! [B_53] :
      ( k1_relat_1(k7_relat_1(B_53,k1_relat_1(B_53))) = k1_relat_1(B_53)
      | ~ v1_relat_1(B_53) ) ),
    inference(resolution,[status(thm)],[c_57,c_75])).

tff(c_732,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_5'),'#skF_5')) = k1_relat_1(k7_relat_1('#skF_2','#skF_5'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_725,c_88])).

tff(c_744,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_5'),'#skF_5')) = '#skF_5'
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_725,c_732])).

tff(c_749,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_744])).

tff(c_752,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_749])).

tff(c_756,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_752])).

tff(c_758,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_744])).

tff(c_852,plain,(
    ! [B_96,C_97,A_98] :
      ( k7_relat_1(k5_relat_1(B_96,C_97),A_98) = k5_relat_1(k7_relat_1(B_96,A_98),C_97)
      | ~ v1_relat_1(C_97)
      | ~ v1_relat_1(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_87,plain,
    ( k1_relat_1(k7_relat_1(k5_relat_1('#skF_2','#skF_3'),'#skF_5')) = '#skF_5'
    | ~ v1_relat_1(k5_relat_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_59,c_75])).

tff(c_132,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_135,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_132])).

tff(c_139,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_135])).

tff(c_140,plain,(
    k1_relat_1(k7_relat_1(k5_relat_1('#skF_2','#skF_3'),'#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_865,plain,
    ( k1_relat_1(k5_relat_1(k7_relat_1('#skF_2','#skF_5'),'#skF_3')) = '#skF_5'
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_852,c_140])).

tff(c_887,plain,(
    k1_relat_1(k5_relat_1(k7_relat_1('#skF_2','#skF_5'),'#skF_3')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_865])).

tff(c_14,plain,(
    ! [B_15,A_14] :
      ( k2_relat_1(k7_relat_1(B_15,A_14)) = k9_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1153,plain,(
    ! [B_115,A_116] :
      ( r1_tarski(k2_relat_1(B_115),k1_relat_1(A_116))
      | k1_relat_1(k5_relat_1(B_115,A_116)) != k1_relat_1(B_115)
      | ~ v1_funct_1(B_115)
      | ~ v1_relat_1(B_115)
      | ~ v1_funct_1(A_116)
      | ~ v1_relat_1(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_3831,plain,(
    ! [B_198,A_199,A_200] :
      ( r1_tarski(k9_relat_1(B_198,A_199),k1_relat_1(A_200))
      | k1_relat_1(k5_relat_1(k7_relat_1(B_198,A_199),A_200)) != k1_relat_1(k7_relat_1(B_198,A_199))
      | ~ v1_funct_1(k7_relat_1(B_198,A_199))
      | ~ v1_relat_1(k7_relat_1(B_198,A_199))
      | ~ v1_funct_1(A_200)
      | ~ v1_relat_1(A_200)
      | ~ v1_relat_1(B_198) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1153])).

tff(c_718,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_2','#skF_5'),k1_relat_1('#skF_3'))
    | r1_tarski('#skF_4',k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_748,plain,(
    ~ r1_tarski(k9_relat_1('#skF_2','#skF_5'),k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_718])).

tff(c_3851,plain,
    ( k1_relat_1(k5_relat_1(k7_relat_1('#skF_2','#skF_5'),'#skF_3')) != k1_relat_1(k7_relat_1('#skF_2','#skF_5'))
    | ~ v1_funct_1(k7_relat_1('#skF_2','#skF_5'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_5'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_3831,c_748])).

tff(c_3933,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_2','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_30,c_758,c_725,c_887,c_3851])).

tff(c_3945,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_3933])).

tff(c_3949,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_3945])).

tff(c_3951,plain,(
    r1_tarski(k9_relat_1('#skF_2','#skF_5'),k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_718])).

tff(c_38,plain,
    ( ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3')))
    | ~ r1_tarski(k9_relat_1('#skF_2','#skF_5'),k1_relat_1('#skF_3'))
    | ~ r1_tarski('#skF_5',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_3981,plain,
    ( ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3')))
    | ~ r1_tarski(k9_relat_1('#skF_2','#skF_5'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_719,c_38])).

tff(c_3982,plain,(
    ~ r1_tarski(k9_relat_1('#skF_2','#skF_5'),k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3981])).

tff(c_3990,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3951,c_3982])).

tff(c_3991,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_3981])).

tff(c_141,plain,(
    v1_relat_1(k5_relat_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_3950,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_718])).

tff(c_3954,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_3950,c_22])).

tff(c_3957,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3954])).

tff(c_3964,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_4'),'#skF_4')) = k1_relat_1(k7_relat_1('#skF_2','#skF_4'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3957,c_88])).

tff(c_3976,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_4'),'#skF_4')) = '#skF_4'
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3957,c_3964])).

tff(c_4114,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3976])).

tff(c_4117,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_4114])).

tff(c_4121,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4117])).

tff(c_4123,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3976])).

tff(c_40,plain,
    ( r1_tarski(k9_relat_1('#skF_2','#skF_4'),k1_relat_1('#skF_3'))
    | ~ r1_tarski(k9_relat_1('#skF_2','#skF_5'),k1_relat_1('#skF_3'))
    | ~ r1_tarski('#skF_5',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_4189,plain,(
    r1_tarski(k9_relat_1('#skF_2','#skF_4'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_719,c_3951,c_40])).

tff(c_4124,plain,(
    ! [A_204,B_205] :
      ( k1_relat_1(k5_relat_1(A_204,B_205)) = k1_relat_1(A_204)
      | ~ r1_tarski(k2_relat_1(A_204),k1_relat_1(B_205))
      | ~ v1_relat_1(B_205)
      | ~ v1_relat_1(A_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6258,plain,(
    ! [B_293,A_294,B_295] :
      ( k1_relat_1(k5_relat_1(k7_relat_1(B_293,A_294),B_295)) = k1_relat_1(k7_relat_1(B_293,A_294))
      | ~ r1_tarski(k9_relat_1(B_293,A_294),k1_relat_1(B_295))
      | ~ v1_relat_1(B_295)
      | ~ v1_relat_1(k7_relat_1(B_293,A_294))
      | ~ v1_relat_1(B_293) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_4124])).

tff(c_6331,plain,
    ( k1_relat_1(k5_relat_1(k7_relat_1('#skF_2','#skF_4'),'#skF_3')) = k1_relat_1(k7_relat_1('#skF_2','#skF_4'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_4'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4189,c_6258])).

tff(c_6371,plain,(
    k1_relat_1(k5_relat_1(k7_relat_1('#skF_2','#skF_4'),'#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4123,c_32,c_3957,c_6331])).

tff(c_4000,plain,(
    ! [B_201,C_202,A_203] :
      ( k7_relat_1(k5_relat_1(B_201,C_202),A_203) = k5_relat_1(k7_relat_1(B_201,A_203),C_202)
      | ~ v1_relat_1(C_202)
      | ~ v1_relat_1(B_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    ! [B_23,A_22] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_23,A_22)),k1_relat_1(B_23))
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4013,plain,(
    ! [B_201,A_203,C_202] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(B_201,A_203),C_202)),k1_relat_1(k5_relat_1(B_201,C_202)))
      | ~ v1_relat_1(k5_relat_1(B_201,C_202))
      | ~ v1_relat_1(C_202)
      | ~ v1_relat_1(B_201) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4000,c_20])).

tff(c_6393,plain,
    ( r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3')))
    | ~ v1_relat_1(k5_relat_1('#skF_2','#skF_3'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6371,c_4013])).

tff(c_6433,plain,(
    r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_141,c_6393])).

tff(c_6435,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3991,c_6433])).

tff(c_6437,plain,(
    ~ r1_tarski('#skF_5',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_44,plain,
    ( ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3')))
    | r1_tarski('#skF_5',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_6553,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_6437,c_44])).

tff(c_6436,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_6455,plain,(
    ! [B_307,A_308] :
      ( k1_relat_1(k7_relat_1(B_307,A_308)) = A_308
      | ~ r1_tarski(A_308,k1_relat_1(B_307))
      | ~ v1_relat_1(B_307) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_6467,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_6436,c_6455])).

tff(c_6479,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6467])).

tff(c_6517,plain,(
    ! [B_309] :
      ( k1_relat_1(k7_relat_1(B_309,k1_relat_1(B_309))) = k1_relat_1(B_309)
      | ~ v1_relat_1(B_309) ) ),
    inference(resolution,[status(thm)],[c_57,c_6455])).

tff(c_6547,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_4'),'#skF_4')) = k1_relat_1(k7_relat_1('#skF_2','#skF_4'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6479,c_6517])).

tff(c_6552,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_4'),'#skF_4')) = '#skF_4'
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6479,c_6547])).

tff(c_6563,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_6552])).

tff(c_6566,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_6563])).

tff(c_6570,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6566])).

tff(c_6572,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_6552])).

tff(c_46,plain,
    ( r1_tarski(k9_relat_1('#skF_2','#skF_4'),k1_relat_1('#skF_3'))
    | r1_tarski('#skF_5',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_6438,plain,(
    r1_tarski(k9_relat_1('#skF_2','#skF_4'),k1_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_6437,c_46])).

tff(c_6809,plain,(
    ! [A_330,B_331] :
      ( k1_relat_1(k5_relat_1(A_330,B_331)) = k1_relat_1(A_330)
      | ~ r1_tarski(k2_relat_1(A_330),k1_relat_1(B_331))
      | ~ v1_relat_1(B_331)
      | ~ v1_relat_1(A_330) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_8277,plain,(
    ! [B_406,A_407,B_408] :
      ( k1_relat_1(k5_relat_1(k7_relat_1(B_406,A_407),B_408)) = k1_relat_1(k7_relat_1(B_406,A_407))
      | ~ r1_tarski(k9_relat_1(B_406,A_407),k1_relat_1(B_408))
      | ~ v1_relat_1(B_408)
      | ~ v1_relat_1(k7_relat_1(B_406,A_407))
      | ~ v1_relat_1(B_406) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_6809])).

tff(c_8320,plain,
    ( k1_relat_1(k5_relat_1(k7_relat_1('#skF_2','#skF_4'),'#skF_3')) = k1_relat_1(k7_relat_1('#skF_2','#skF_4'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_4'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_6438,c_8277])).

tff(c_8332,plain,(
    k1_relat_1(k5_relat_1(k7_relat_1('#skF_2','#skF_4'),'#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6572,c_32,c_6479,c_8320])).

tff(c_6665,plain,(
    ! [B_316,C_317,A_318] :
      ( k7_relat_1(k5_relat_1(B_316,C_317),A_318) = k5_relat_1(k7_relat_1(B_316,A_318),C_317)
      | ~ v1_relat_1(C_317)
      | ~ v1_relat_1(B_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6685,plain,(
    ! [B_316,A_318,C_317] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(B_316,A_318),C_317)),k1_relat_1(k5_relat_1(B_316,C_317)))
      | ~ v1_relat_1(k5_relat_1(B_316,C_317))
      | ~ v1_relat_1(C_317)
      | ~ v1_relat_1(B_316) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6665,c_20])).

tff(c_8342,plain,
    ( r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3')))
    | ~ v1_relat_1(k5_relat_1('#skF_2','#skF_3'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8332,c_6685])).

tff(c_8385,plain,
    ( r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3')))
    | ~ v1_relat_1(k5_relat_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_8342])).

tff(c_8386,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_6553,c_8385])).

tff(c_8401,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_8386])).

tff(c_8405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_8401])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:23:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.37/2.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.54/2.60  
% 7.54/2.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.54/2.60  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 7.54/2.60  
% 7.54/2.60  %Foreground sorts:
% 7.54/2.60  
% 7.54/2.60  
% 7.54/2.60  %Background operators:
% 7.54/2.60  
% 7.54/2.60  
% 7.54/2.60  %Foreground operators:
% 7.54/2.60  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.54/2.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.54/2.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.54/2.60  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.54/2.60  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.54/2.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.54/2.60  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.54/2.60  tff('#skF_5', type, '#skF_5': $i).
% 7.54/2.60  tff('#skF_2', type, '#skF_2': $i).
% 7.54/2.60  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.54/2.60  tff('#skF_3', type, '#skF_3': $i).
% 7.54/2.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.54/2.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.54/2.60  tff('#skF_4', type, '#skF_4': $i).
% 7.54/2.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.54/2.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.54/2.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.54/2.60  
% 7.54/2.64  tff(f_117, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (r1_tarski(C, k1_relat_1(k5_relat_1(A, B))) <=> (r1_tarski(C, k1_relat_1(A)) & r1_tarski(k9_relat_1(A, C), k1_relat_1(B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_1)).
% 7.54/2.64  tff(f_38, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 7.54/2.64  tff(f_87, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 7.54/2.64  tff(f_42, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 7.54/2.64  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.54/2.64  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 7.54/2.64  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 7.54/2.64  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_relat_1)).
% 7.54/2.64  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 7.54/2.64  tff(f_100, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(k5_relat_1(B, A)) = k1_relat_1(B)) => r1_tarski(k2_relat_1(B), k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_funct_1)).
% 7.54/2.64  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 7.54/2.64  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_relat_1)).
% 7.54/2.64  tff(c_36, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.54/2.64  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.54/2.64  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k5_relat_1(A_6, B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.54/2.64  tff(c_34, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.54/2.64  tff(c_24, plain, (![A_26, B_27]: (v1_funct_1(k7_relat_1(A_26, B_27)) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.54/2.64  tff(c_30, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.54/2.64  tff(c_10, plain, (![A_8, B_9]: (v1_relat_1(k7_relat_1(A_8, B_9)) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.54/2.64  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.54/2.64  tff(c_52, plain, (![A_41, B_42]: (~r2_hidden('#skF_1'(A_41, B_42), B_42) | r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.54/2.64  tff(c_57, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_52])).
% 7.54/2.64  tff(c_16, plain, (![A_16, B_18]: (r1_tarski(k1_relat_1(k5_relat_1(A_16, B_18)), k1_relat_1(A_16)) | ~v1_relat_1(B_18) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.54/2.64  tff(c_48, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_2')) | r1_tarski('#skF_5', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.54/2.64  tff(c_59, plain, (r1_tarski('#skF_5', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_48])).
% 7.54/2.64  tff(c_71, plain, (![C_50, B_51, A_52]: (r2_hidden(C_50, B_51) | ~r2_hidden(C_50, A_52) | ~r1_tarski(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.54/2.64  tff(c_122, plain, (![A_58, B_59, B_60]: (r2_hidden('#skF_1'(A_58, B_59), B_60) | ~r1_tarski(A_58, B_60) | r1_tarski(A_58, B_59))), inference(resolution, [status(thm)], [c_6, c_71])).
% 7.54/2.64  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.54/2.64  tff(c_332, plain, (![A_71, B_72, B_73, B_74]: (r2_hidden('#skF_1'(A_71, B_72), B_73) | ~r1_tarski(B_74, B_73) | ~r1_tarski(A_71, B_74) | r1_tarski(A_71, B_72))), inference(resolution, [status(thm)], [c_122, c_2])).
% 7.54/2.64  tff(c_348, plain, (![A_75, B_76]: (r2_hidden('#skF_1'(A_75, B_76), k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))) | ~r1_tarski(A_75, '#skF_5') | r1_tarski(A_75, B_76))), inference(resolution, [status(thm)], [c_59, c_332])).
% 7.54/2.64  tff(c_661, plain, (![A_87, B_88, B_89]: (r2_hidden('#skF_1'(A_87, B_88), B_89) | ~r1_tarski(k1_relat_1(k5_relat_1('#skF_2', '#skF_3')), B_89) | ~r1_tarski(A_87, '#skF_5') | r1_tarski(A_87, B_88))), inference(resolution, [status(thm)], [c_348, c_2])).
% 7.54/2.64  tff(c_673, plain, (![A_87, B_88]: (r2_hidden('#skF_1'(A_87, B_88), k1_relat_1('#skF_2')) | ~r1_tarski(A_87, '#skF_5') | r1_tarski(A_87, B_88) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_661])).
% 7.54/2.64  tff(c_684, plain, (![A_90, B_91]: (r2_hidden('#skF_1'(A_90, B_91), k1_relat_1('#skF_2')) | ~r1_tarski(A_90, '#skF_5') | r1_tarski(A_90, B_91))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_673])).
% 7.54/2.64  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.54/2.64  tff(c_693, plain, (![A_92]: (~r1_tarski(A_92, '#skF_5') | r1_tarski(A_92, k1_relat_1('#skF_2')))), inference(resolution, [status(thm)], [c_684, c_4])).
% 7.54/2.64  tff(c_42, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_2')) | ~r1_tarski(k9_relat_1('#skF_2', '#skF_5'), k1_relat_1('#skF_3')) | ~r1_tarski('#skF_5', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.54/2.64  tff(c_165, plain, (~r1_tarski('#skF_5', k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_42])).
% 7.54/2.64  tff(c_705, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_693, c_165])).
% 7.54/2.64  tff(c_717, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_57, c_705])).
% 7.54/2.64  tff(c_719, plain, (r1_tarski('#skF_5', k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_42])).
% 7.54/2.64  tff(c_22, plain, (![B_25, A_24]: (k1_relat_1(k7_relat_1(B_25, A_24))=A_24 | ~r1_tarski(A_24, k1_relat_1(B_25)) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.54/2.64  tff(c_722, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_5'))='#skF_5' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_719, c_22])).
% 7.54/2.64  tff(c_725, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_722])).
% 7.54/2.64  tff(c_75, plain, (![B_53, A_54]: (k1_relat_1(k7_relat_1(B_53, A_54))=A_54 | ~r1_tarski(A_54, k1_relat_1(B_53)) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.54/2.64  tff(c_88, plain, (![B_53]: (k1_relat_1(k7_relat_1(B_53, k1_relat_1(B_53)))=k1_relat_1(B_53) | ~v1_relat_1(B_53))), inference(resolution, [status(thm)], [c_57, c_75])).
% 7.54/2.64  tff(c_732, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_5'), '#skF_5'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_5')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_725, c_88])).
% 7.54/2.64  tff(c_744, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_5'), '#skF_5'))='#skF_5' | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_725, c_732])).
% 7.54/2.64  tff(c_749, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_5'))), inference(splitLeft, [status(thm)], [c_744])).
% 7.54/2.64  tff(c_752, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10, c_749])).
% 7.54/2.64  tff(c_756, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_752])).
% 7.54/2.64  tff(c_758, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_5'))), inference(splitRight, [status(thm)], [c_744])).
% 7.54/2.64  tff(c_852, plain, (![B_96, C_97, A_98]: (k7_relat_1(k5_relat_1(B_96, C_97), A_98)=k5_relat_1(k7_relat_1(B_96, A_98), C_97) | ~v1_relat_1(C_97) | ~v1_relat_1(B_96))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.54/2.64  tff(c_87, plain, (k1_relat_1(k7_relat_1(k5_relat_1('#skF_2', '#skF_3'), '#skF_5'))='#skF_5' | ~v1_relat_1(k5_relat_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_59, c_75])).
% 7.54/2.64  tff(c_132, plain, (~v1_relat_1(k5_relat_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_87])).
% 7.54/2.64  tff(c_135, plain, (~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_132])).
% 7.54/2.64  tff(c_139, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_135])).
% 7.54/2.64  tff(c_140, plain, (k1_relat_1(k7_relat_1(k5_relat_1('#skF_2', '#skF_3'), '#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_87])).
% 7.54/2.64  tff(c_865, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_2', '#skF_5'), '#skF_3'))='#skF_5' | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_852, c_140])).
% 7.54/2.64  tff(c_887, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_2', '#skF_5'), '#skF_3'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_865])).
% 7.54/2.64  tff(c_14, plain, (![B_15, A_14]: (k2_relat_1(k7_relat_1(B_15, A_14))=k9_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.54/2.64  tff(c_1153, plain, (![B_115, A_116]: (r1_tarski(k2_relat_1(B_115), k1_relat_1(A_116)) | k1_relat_1(k5_relat_1(B_115, A_116))!=k1_relat_1(B_115) | ~v1_funct_1(B_115) | ~v1_relat_1(B_115) | ~v1_funct_1(A_116) | ~v1_relat_1(A_116))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.54/2.64  tff(c_3831, plain, (![B_198, A_199, A_200]: (r1_tarski(k9_relat_1(B_198, A_199), k1_relat_1(A_200)) | k1_relat_1(k5_relat_1(k7_relat_1(B_198, A_199), A_200))!=k1_relat_1(k7_relat_1(B_198, A_199)) | ~v1_funct_1(k7_relat_1(B_198, A_199)) | ~v1_relat_1(k7_relat_1(B_198, A_199)) | ~v1_funct_1(A_200) | ~v1_relat_1(A_200) | ~v1_relat_1(B_198))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1153])).
% 7.54/2.64  tff(c_718, plain, (~r1_tarski(k9_relat_1('#skF_2', '#skF_5'), k1_relat_1('#skF_3')) | r1_tarski('#skF_4', k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_42])).
% 7.54/2.64  tff(c_748, plain, (~r1_tarski(k9_relat_1('#skF_2', '#skF_5'), k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_718])).
% 7.54/2.64  tff(c_3851, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_2', '#skF_5'), '#skF_3'))!=k1_relat_1(k7_relat_1('#skF_2', '#skF_5')) | ~v1_funct_1(k7_relat_1('#skF_2', '#skF_5')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_5')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_3831, c_748])).
% 7.54/2.64  tff(c_3933, plain, (~v1_funct_1(k7_relat_1('#skF_2', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_30, c_758, c_725, c_887, c_3851])).
% 7.54/2.64  tff(c_3945, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_3933])).
% 7.54/2.64  tff(c_3949, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_3945])).
% 7.54/2.64  tff(c_3951, plain, (r1_tarski(k9_relat_1('#skF_2', '#skF_5'), k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_718])).
% 7.54/2.64  tff(c_38, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))) | ~r1_tarski(k9_relat_1('#skF_2', '#skF_5'), k1_relat_1('#skF_3')) | ~r1_tarski('#skF_5', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.54/2.64  tff(c_3981, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))) | ~r1_tarski(k9_relat_1('#skF_2', '#skF_5'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_719, c_38])).
% 7.54/2.64  tff(c_3982, plain, (~r1_tarski(k9_relat_1('#skF_2', '#skF_5'), k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_3981])).
% 7.54/2.64  tff(c_3990, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3951, c_3982])).
% 7.54/2.64  tff(c_3991, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_3981])).
% 7.54/2.64  tff(c_141, plain, (v1_relat_1(k5_relat_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_87])).
% 7.54/2.64  tff(c_3950, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_718])).
% 7.54/2.64  tff(c_3954, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_4'))='#skF_4' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_3950, c_22])).
% 7.54/2.64  tff(c_3957, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_3954])).
% 7.54/2.64  tff(c_3964, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_4'), '#skF_4'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3957, c_88])).
% 7.54/2.64  tff(c_3976, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_4'), '#skF_4'))='#skF_4' | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3957, c_3964])).
% 7.54/2.64  tff(c_4114, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_3976])).
% 7.54/2.64  tff(c_4117, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10, c_4114])).
% 7.54/2.64  tff(c_4121, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_4117])).
% 7.54/2.64  tff(c_4123, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_3976])).
% 7.54/2.64  tff(c_40, plain, (r1_tarski(k9_relat_1('#skF_2', '#skF_4'), k1_relat_1('#skF_3')) | ~r1_tarski(k9_relat_1('#skF_2', '#skF_5'), k1_relat_1('#skF_3')) | ~r1_tarski('#skF_5', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.54/2.64  tff(c_4189, plain, (r1_tarski(k9_relat_1('#skF_2', '#skF_4'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_719, c_3951, c_40])).
% 7.54/2.64  tff(c_4124, plain, (![A_204, B_205]: (k1_relat_1(k5_relat_1(A_204, B_205))=k1_relat_1(A_204) | ~r1_tarski(k2_relat_1(A_204), k1_relat_1(B_205)) | ~v1_relat_1(B_205) | ~v1_relat_1(A_204))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.54/2.64  tff(c_6258, plain, (![B_293, A_294, B_295]: (k1_relat_1(k5_relat_1(k7_relat_1(B_293, A_294), B_295))=k1_relat_1(k7_relat_1(B_293, A_294)) | ~r1_tarski(k9_relat_1(B_293, A_294), k1_relat_1(B_295)) | ~v1_relat_1(B_295) | ~v1_relat_1(k7_relat_1(B_293, A_294)) | ~v1_relat_1(B_293))), inference(superposition, [status(thm), theory('equality')], [c_14, c_4124])).
% 7.54/2.64  tff(c_6331, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_2', '#skF_4'), '#skF_3'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_4')) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_4')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_4189, c_6258])).
% 7.54/2.64  tff(c_6371, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_2', '#skF_4'), '#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_4123, c_32, c_3957, c_6331])).
% 7.54/2.64  tff(c_4000, plain, (![B_201, C_202, A_203]: (k7_relat_1(k5_relat_1(B_201, C_202), A_203)=k5_relat_1(k7_relat_1(B_201, A_203), C_202) | ~v1_relat_1(C_202) | ~v1_relat_1(B_201))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.54/2.64  tff(c_20, plain, (![B_23, A_22]: (r1_tarski(k1_relat_1(k7_relat_1(B_23, A_22)), k1_relat_1(B_23)) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.54/2.64  tff(c_4013, plain, (![B_201, A_203, C_202]: (r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(B_201, A_203), C_202)), k1_relat_1(k5_relat_1(B_201, C_202))) | ~v1_relat_1(k5_relat_1(B_201, C_202)) | ~v1_relat_1(C_202) | ~v1_relat_1(B_201))), inference(superposition, [status(thm), theory('equality')], [c_4000, c_20])).
% 7.54/2.64  tff(c_6393, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))) | ~v1_relat_1(k5_relat_1('#skF_2', '#skF_3')) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6371, c_4013])).
% 7.54/2.64  tff(c_6433, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_141, c_6393])).
% 7.54/2.64  tff(c_6435, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3991, c_6433])).
% 7.54/2.64  tff(c_6437, plain, (~r1_tarski('#skF_5', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_48])).
% 7.54/2.64  tff(c_44, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))) | r1_tarski('#skF_5', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.54/2.64  tff(c_6553, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_6437, c_44])).
% 7.54/2.64  tff(c_6436, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_48])).
% 7.54/2.64  tff(c_6455, plain, (![B_307, A_308]: (k1_relat_1(k7_relat_1(B_307, A_308))=A_308 | ~r1_tarski(A_308, k1_relat_1(B_307)) | ~v1_relat_1(B_307))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.54/2.64  tff(c_6467, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_4'))='#skF_4' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_6436, c_6455])).
% 7.54/2.64  tff(c_6479, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_6467])).
% 7.54/2.64  tff(c_6517, plain, (![B_309]: (k1_relat_1(k7_relat_1(B_309, k1_relat_1(B_309)))=k1_relat_1(B_309) | ~v1_relat_1(B_309))), inference(resolution, [status(thm)], [c_57, c_6455])).
% 7.54/2.64  tff(c_6547, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_4'), '#skF_4'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6479, c_6517])).
% 7.54/2.64  tff(c_6552, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_4'), '#skF_4'))='#skF_4' | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6479, c_6547])).
% 7.54/2.64  tff(c_6563, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_6552])).
% 7.54/2.64  tff(c_6566, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10, c_6563])).
% 7.54/2.64  tff(c_6570, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_6566])).
% 7.54/2.64  tff(c_6572, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_6552])).
% 7.54/2.64  tff(c_46, plain, (r1_tarski(k9_relat_1('#skF_2', '#skF_4'), k1_relat_1('#skF_3')) | r1_tarski('#skF_5', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.54/2.64  tff(c_6438, plain, (r1_tarski(k9_relat_1('#skF_2', '#skF_4'), k1_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_6437, c_46])).
% 7.54/2.64  tff(c_6809, plain, (![A_330, B_331]: (k1_relat_1(k5_relat_1(A_330, B_331))=k1_relat_1(A_330) | ~r1_tarski(k2_relat_1(A_330), k1_relat_1(B_331)) | ~v1_relat_1(B_331) | ~v1_relat_1(A_330))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.54/2.64  tff(c_8277, plain, (![B_406, A_407, B_408]: (k1_relat_1(k5_relat_1(k7_relat_1(B_406, A_407), B_408))=k1_relat_1(k7_relat_1(B_406, A_407)) | ~r1_tarski(k9_relat_1(B_406, A_407), k1_relat_1(B_408)) | ~v1_relat_1(B_408) | ~v1_relat_1(k7_relat_1(B_406, A_407)) | ~v1_relat_1(B_406))), inference(superposition, [status(thm), theory('equality')], [c_14, c_6809])).
% 7.54/2.64  tff(c_8320, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_2', '#skF_4'), '#skF_3'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_4')) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_4')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_6438, c_8277])).
% 7.54/2.64  tff(c_8332, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_2', '#skF_4'), '#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_6572, c_32, c_6479, c_8320])).
% 7.54/2.64  tff(c_6665, plain, (![B_316, C_317, A_318]: (k7_relat_1(k5_relat_1(B_316, C_317), A_318)=k5_relat_1(k7_relat_1(B_316, A_318), C_317) | ~v1_relat_1(C_317) | ~v1_relat_1(B_316))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.54/2.64  tff(c_6685, plain, (![B_316, A_318, C_317]: (r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(B_316, A_318), C_317)), k1_relat_1(k5_relat_1(B_316, C_317))) | ~v1_relat_1(k5_relat_1(B_316, C_317)) | ~v1_relat_1(C_317) | ~v1_relat_1(B_316))), inference(superposition, [status(thm), theory('equality')], [c_6665, c_20])).
% 7.54/2.64  tff(c_8342, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))) | ~v1_relat_1(k5_relat_1('#skF_2', '#skF_3')) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_8332, c_6685])).
% 7.54/2.64  tff(c_8385, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))) | ~v1_relat_1(k5_relat_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_8342])).
% 7.54/2.64  tff(c_8386, plain, (~v1_relat_1(k5_relat_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_6553, c_8385])).
% 7.54/2.64  tff(c_8401, plain, (~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_8386])).
% 7.54/2.64  tff(c_8405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_8401])).
% 7.54/2.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.54/2.64  
% 7.54/2.64  Inference rules
% 7.54/2.64  ----------------------
% 7.54/2.64  #Ref     : 0
% 7.54/2.64  #Sup     : 1994
% 7.54/2.64  #Fact    : 0
% 7.54/2.64  #Define  : 0
% 7.54/2.64  #Split   : 29
% 7.54/2.64  #Chain   : 0
% 7.54/2.64  #Close   : 0
% 7.54/2.64  
% 7.54/2.64  Ordering : KBO
% 7.54/2.64  
% 7.54/2.64  Simplification rules
% 7.54/2.64  ----------------------
% 7.54/2.64  #Subsume      : 229
% 7.54/2.64  #Demod        : 1241
% 7.54/2.64  #Tautology    : 534
% 7.54/2.64  #SimpNegUnit  : 4
% 7.54/2.64  #BackRed      : 0
% 7.54/2.64  
% 7.54/2.64  #Partial instantiations: 0
% 7.54/2.64  #Strategies tried      : 1
% 7.54/2.64  
% 7.54/2.64  Timing (in seconds)
% 7.54/2.64  ----------------------
% 7.54/2.64  Preprocessing        : 0.31
% 7.54/2.64  Parsing              : 0.17
% 7.54/2.64  CNF conversion       : 0.02
% 7.54/2.64  Main loop            : 1.52
% 7.54/2.64  Inferencing          : 0.48
% 7.54/2.64  Reduction            : 0.49
% 7.54/2.64  Demodulation         : 0.35
% 7.54/2.64  BG Simplification    : 0.06
% 7.54/2.65  Subsumption          : 0.40
% 7.54/2.65  Abstraction          : 0.07
% 7.54/2.65  MUC search           : 0.00
% 7.54/2.65  Cooper               : 0.00
% 7.54/2.65  Total                : 1.91
% 7.54/2.65  Index Insertion      : 0.00
% 7.54/2.65  Index Deletion       : 0.00
% 7.54/2.65  Index Matching       : 0.00
% 7.54/2.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
