%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:43 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 581 expanded)
%              Number of leaves         :   27 ( 218 expanded)
%              Depth                    :   13
%              Number of atoms          :  191 (1760 expanded)
%              Number of equality atoms :   23 ( 432 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k4_relat_1 > k2_funct_1 > k1_relat_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_108,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( v2_funct_1(B)
            & r2_hidden(A,k1_relat_1(B)) )
         => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
            & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_49,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( B = k4_relat_1(A)
          <=> ! [C,D] :
                ( r2_hidden(k4_tarski(C,D),B)
              <=> r2_hidden(k4_tarski(D,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
          <=> ( r2_hidden(A,k1_relat_1(C))
              & r2_hidden(k1_funct_1(C,A),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

tff(c_38,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_44,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_42,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_30,plain,(
    ! [A_29,C_31] :
      ( r2_hidden(k4_tarski(A_29,k1_funct_1(C_31,A_29)),C_31)
      | ~ r2_hidden(A_29,k1_relat_1(C_31))
      | ~ v1_funct_1(C_31)
      | ~ v1_relat_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_18,plain,(
    ! [A_20] :
      ( v1_funct_1(k2_funct_1(A_20))
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_40,plain,(
    v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_48,plain,(
    ! [A_35] :
      ( k4_relat_1(A_35) = k2_funct_1(A_35)
      | ~ v2_funct_1(A_35)
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_51,plain,
    ( k4_relat_1('#skF_6') = k2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_48])).

tff(c_54,plain,(
    k4_relat_1('#skF_6') = k2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_51])).

tff(c_14,plain,(
    ! [A_18] :
      ( v1_relat_1(k4_relat_1(A_18))
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_58,plain,
    ( v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_14])).

tff(c_62,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_58])).

tff(c_77,plain,(
    ! [C_44,D_45,A_46] :
      ( r2_hidden(k4_tarski(C_44,D_45),k4_relat_1(A_46))
      | ~ r2_hidden(k4_tarski(D_45,C_44),A_46)
      | ~ v1_relat_1(k4_relat_1(A_46))
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_86,plain,(
    ! [C_44,D_45] :
      ( r2_hidden(k4_tarski(C_44,D_45),k2_funct_1('#skF_6'))
      | ~ r2_hidden(k4_tarski(D_45,C_44),'#skF_6')
      | ~ v1_relat_1(k4_relat_1('#skF_6'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_77])).

tff(c_91,plain,(
    ! [C_47,D_48] :
      ( r2_hidden(k4_tarski(C_47,D_48),k2_funct_1('#skF_6'))
      | ~ r2_hidden(k4_tarski(D_48,C_47),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_62,c_54,c_86])).

tff(c_34,plain,(
    ! [A_29,C_31,B_30] :
      ( r2_hidden(A_29,k1_relat_1(C_31))
      | ~ r2_hidden(k4_tarski(A_29,B_30),C_31)
      | ~ v1_funct_1(C_31)
      | ~ v1_relat_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_94,plain,(
    ! [C_47,D_48] :
      ( r2_hidden(C_47,k1_relat_1(k2_funct_1('#skF_6')))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6'))
      | ~ r2_hidden(k4_tarski(D_48,C_47),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_91,c_34])).

tff(c_100,plain,(
    ! [C_47,D_48] :
      ( r2_hidden(C_47,k1_relat_1(k2_funct_1('#skF_6')))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ r2_hidden(k4_tarski(D_48,C_47),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_94])).

tff(c_104,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_107,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_18,c_104])).

tff(c_111,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_107])).

tff(c_113,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_32,plain,(
    ! [C_31,A_29,B_30] :
      ( k1_funct_1(C_31,A_29) = B_30
      | ~ r2_hidden(k4_tarski(A_29,B_30),C_31)
      | ~ v1_funct_1(C_31)
      | ~ v1_relat_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_97,plain,(
    ! [C_47,D_48] :
      ( k1_funct_1(k2_funct_1('#skF_6'),C_47) = D_48
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6'))
      | ~ r2_hidden(k4_tarski(D_48,C_47),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_91,c_32])).

tff(c_103,plain,(
    ! [C_47,D_48] :
      ( k1_funct_1(k2_funct_1('#skF_6'),C_47) = D_48
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ r2_hidden(k4_tarski(D_48,C_47),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_97])).

tff(c_114,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_116,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_114])).

tff(c_120,plain,(
    ! [C_49,D_50] :
      ( k1_funct_1(k2_funct_1('#skF_6'),C_49) = D_50
      | ~ r2_hidden(k4_tarski(D_50,C_49),'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_124,plain,(
    ! [A_29] :
      ( k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6',A_29)) = A_29
      | ~ r2_hidden(A_29,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_30,c_120])).

tff(c_162,plain,(
    ! [A_58] :
      ( k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6',A_58)) = A_58
      | ~ r2_hidden(A_58,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_124])).

tff(c_36,plain,
    ( k1_funct_1(k5_relat_1('#skF_6',k2_funct_1('#skF_6')),'#skF_5') != '#skF_5'
    | k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_64,plain,(
    k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_171,plain,(
    ~ r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_64])).

tff(c_181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_171])).

tff(c_182,plain,(
    k1_funct_1(k5_relat_1('#skF_6',k2_funct_1('#skF_6')),'#skF_5') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_183,plain,(
    k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_190,plain,(
    ! [A_65,C_66] :
      ( r2_hidden(k4_tarski(A_65,k1_funct_1(C_66,A_65)),C_66)
      | ~ r2_hidden(A_65,k1_relat_1(C_66))
      | ~ v1_funct_1(C_66)
      | ~ v1_relat_1(C_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_199,plain,
    ( r2_hidden(k4_tarski(k1_funct_1('#skF_6','#skF_5'),'#skF_5'),k2_funct_1('#skF_6'))
    | ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_relat_1(k2_funct_1('#skF_6')))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_190])).

tff(c_204,plain,
    ( r2_hidden(k4_tarski(k1_funct_1('#skF_6','#skF_5'),'#skF_5'),k2_funct_1('#skF_6'))
    | ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_relat_1(k2_funct_1('#skF_6')))
    | ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_199])).

tff(c_259,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_204])).

tff(c_262,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_18,c_259])).

tff(c_266,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_262])).

tff(c_268,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_224,plain,(
    ! [C_72,D_73,A_74] :
      ( r2_hidden(k4_tarski(C_72,D_73),k4_relat_1(A_74))
      | ~ r2_hidden(k4_tarski(D_73,C_72),A_74)
      | ~ v1_relat_1(k4_relat_1(A_74))
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_236,plain,(
    ! [C_72,D_73] :
      ( r2_hidden(k4_tarski(C_72,D_73),k2_funct_1('#skF_6'))
      | ~ r2_hidden(k4_tarski(D_73,C_72),'#skF_6')
      | ~ v1_relat_1(k4_relat_1('#skF_6'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_224])).

tff(c_242,plain,(
    ! [C_75,D_76] :
      ( r2_hidden(k4_tarski(C_75,D_76),k2_funct_1('#skF_6'))
      | ~ r2_hidden(k4_tarski(D_76,C_75),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_62,c_54,c_236])).

tff(c_248,plain,(
    ! [C_75,D_76] :
      ( r2_hidden(C_75,k1_relat_1(k2_funct_1('#skF_6')))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6'))
      | ~ r2_hidden(k4_tarski(D_76,C_75),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_242,c_34])).

tff(c_255,plain,(
    ! [C_75,D_76] :
      ( r2_hidden(C_75,k1_relat_1(k2_funct_1('#skF_6')))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ r2_hidden(k4_tarski(D_76,C_75),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_248])).

tff(c_271,plain,(
    ! [C_77,D_78] :
      ( r2_hidden(C_77,k1_relat_1(k2_funct_1('#skF_6')))
      | ~ r2_hidden(k4_tarski(D_78,C_77),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_255])).

tff(c_274,plain,(
    ! [A_29] :
      ( r2_hidden(k1_funct_1('#skF_6',A_29),k1_relat_1(k2_funct_1('#skF_6')))
      | ~ r2_hidden(A_29,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_30,c_271])).

tff(c_277,plain,(
    ! [A_29] :
      ( r2_hidden(k1_funct_1('#skF_6',A_29),k1_relat_1(k2_funct_1('#skF_6')))
      | ~ r2_hidden(A_29,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_274])).

tff(c_267,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_relat_1(k2_funct_1('#skF_6')))
    | r2_hidden(k4_tarski(k1_funct_1('#skF_6','#skF_5'),'#skF_5'),k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_321,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_relat_1(k2_funct_1('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_267])).

tff(c_324,plain,(
    ~ r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_277,c_321])).

tff(c_328,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_324])).

tff(c_330,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_relat_1(k2_funct_1('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_267])).

tff(c_537,plain,(
    ! [A_98,C_99,B_100] :
      ( r2_hidden(A_98,k1_relat_1(k5_relat_1(C_99,B_100)))
      | ~ r2_hidden(k1_funct_1(C_99,A_98),k1_relat_1(B_100))
      | ~ r2_hidden(A_98,k1_relat_1(C_99))
      | ~ v1_funct_1(C_99)
      | ~ v1_relat_1(C_99)
      | ~ v1_funct_1(B_100)
      | ~ v1_relat_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_549,plain,
    ( r2_hidden('#skF_5',k1_relat_1(k5_relat_1('#skF_6',k2_funct_1('#skF_6'))))
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_330,c_537])).

tff(c_567,plain,(
    r2_hidden('#skF_5',k1_relat_1(k5_relat_1('#skF_6',k2_funct_1('#skF_6')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_268,c_44,c_42,c_38,c_549])).

tff(c_754,plain,(
    ! [C_109,B_110,A_111] :
      ( k1_funct_1(k5_relat_1(C_109,B_110),A_111) = k1_funct_1(B_110,k1_funct_1(C_109,A_111))
      | ~ r2_hidden(A_111,k1_relat_1(k5_relat_1(C_109,B_110)))
      | ~ v1_funct_1(C_109)
      | ~ v1_relat_1(C_109)
      | ~ v1_funct_1(B_110)
      | ~ v1_relat_1(B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_766,plain,
    ( k1_funct_1(k5_relat_1('#skF_6',k2_funct_1('#skF_6')),'#skF_5') = k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_567,c_754])).

tff(c_786,plain,(
    k1_funct_1(k5_relat_1('#skF_6',k2_funct_1('#skF_6')),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_268,c_44,c_42,c_183,c_766])).

tff(c_788,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_786])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:00:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.99/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.47  
% 2.99/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.47  %$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k4_relat_1 > k2_funct_1 > k1_relat_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 2.99/1.47  
% 2.99/1.47  %Foreground sorts:
% 2.99/1.47  
% 2.99/1.47  
% 2.99/1.47  %Background operators:
% 2.99/1.47  
% 2.99/1.47  
% 2.99/1.47  %Foreground operators:
% 2.99/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.99/1.47  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.99/1.47  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.99/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.99/1.47  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.99/1.47  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.99/1.47  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.99/1.47  tff('#skF_5', type, '#skF_5': $i).
% 2.99/1.47  tff('#skF_6', type, '#skF_6': $i).
% 2.99/1.47  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.99/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.99/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.99/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.99/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.99/1.47  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.99/1.47  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.99/1.47  
% 3.12/1.49  tff(f_108, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_funct_1)).
% 3.12/1.49  tff(f_95, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 3.12/1.49  tff(f_57, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.12/1.49  tff(f_49, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 3.12/1.49  tff(f_41, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 3.12/1.49  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => ((B = k4_relat_1(A)) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), B) <=> r2_hidden(k4_tarski(D, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_relat_1)).
% 3.12/1.49  tff(f_72, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), k1_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_funct_1)).
% 3.12/1.49  tff(f_85, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) => (k1_funct_1(k5_relat_1(C, B), A) = k1_funct_1(B, k1_funct_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_funct_1)).
% 3.12/1.49  tff(c_38, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.12/1.49  tff(c_44, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.12/1.49  tff(c_42, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.12/1.49  tff(c_30, plain, (![A_29, C_31]: (r2_hidden(k4_tarski(A_29, k1_funct_1(C_31, A_29)), C_31) | ~r2_hidden(A_29, k1_relat_1(C_31)) | ~v1_funct_1(C_31) | ~v1_relat_1(C_31))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.12/1.49  tff(c_18, plain, (![A_20]: (v1_funct_1(k2_funct_1(A_20)) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.12/1.49  tff(c_40, plain, (v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.12/1.49  tff(c_48, plain, (![A_35]: (k4_relat_1(A_35)=k2_funct_1(A_35) | ~v2_funct_1(A_35) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.12/1.49  tff(c_51, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_40, c_48])).
% 3.12/1.49  tff(c_54, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_51])).
% 3.12/1.49  tff(c_14, plain, (![A_18]: (v1_relat_1(k4_relat_1(A_18)) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.12/1.49  tff(c_58, plain, (v1_relat_1(k2_funct_1('#skF_6')) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_54, c_14])).
% 3.12/1.49  tff(c_62, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_58])).
% 3.12/1.49  tff(c_77, plain, (![C_44, D_45, A_46]: (r2_hidden(k4_tarski(C_44, D_45), k4_relat_1(A_46)) | ~r2_hidden(k4_tarski(D_45, C_44), A_46) | ~v1_relat_1(k4_relat_1(A_46)) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.12/1.49  tff(c_86, plain, (![C_44, D_45]: (r2_hidden(k4_tarski(C_44, D_45), k2_funct_1('#skF_6')) | ~r2_hidden(k4_tarski(D_45, C_44), '#skF_6') | ~v1_relat_1(k4_relat_1('#skF_6')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_54, c_77])).
% 3.12/1.49  tff(c_91, plain, (![C_47, D_48]: (r2_hidden(k4_tarski(C_47, D_48), k2_funct_1('#skF_6')) | ~r2_hidden(k4_tarski(D_48, C_47), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_62, c_54, c_86])).
% 3.12/1.49  tff(c_34, plain, (![A_29, C_31, B_30]: (r2_hidden(A_29, k1_relat_1(C_31)) | ~r2_hidden(k4_tarski(A_29, B_30), C_31) | ~v1_funct_1(C_31) | ~v1_relat_1(C_31))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.12/1.49  tff(c_94, plain, (![C_47, D_48]: (r2_hidden(C_47, k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~r2_hidden(k4_tarski(D_48, C_47), '#skF_6'))), inference(resolution, [status(thm)], [c_91, c_34])).
% 3.12/1.49  tff(c_100, plain, (![C_47, D_48]: (r2_hidden(C_47, k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~r2_hidden(k4_tarski(D_48, C_47), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_94])).
% 3.12/1.49  tff(c_104, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_100])).
% 3.12/1.49  tff(c_107, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_18, c_104])).
% 3.12/1.49  tff(c_111, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_107])).
% 3.12/1.49  tff(c_113, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_100])).
% 3.12/1.49  tff(c_32, plain, (![C_31, A_29, B_30]: (k1_funct_1(C_31, A_29)=B_30 | ~r2_hidden(k4_tarski(A_29, B_30), C_31) | ~v1_funct_1(C_31) | ~v1_relat_1(C_31))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.12/1.49  tff(c_97, plain, (![C_47, D_48]: (k1_funct_1(k2_funct_1('#skF_6'), C_47)=D_48 | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~r2_hidden(k4_tarski(D_48, C_47), '#skF_6'))), inference(resolution, [status(thm)], [c_91, c_32])).
% 3.12/1.49  tff(c_103, plain, (![C_47, D_48]: (k1_funct_1(k2_funct_1('#skF_6'), C_47)=D_48 | ~v1_funct_1(k2_funct_1('#skF_6')) | ~r2_hidden(k4_tarski(D_48, C_47), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_97])).
% 3.12/1.49  tff(c_114, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_103])).
% 3.12/1.49  tff(c_116, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_113, c_114])).
% 3.12/1.49  tff(c_120, plain, (![C_49, D_50]: (k1_funct_1(k2_funct_1('#skF_6'), C_49)=D_50 | ~r2_hidden(k4_tarski(D_50, C_49), '#skF_6'))), inference(splitRight, [status(thm)], [c_103])).
% 3.12/1.49  tff(c_124, plain, (![A_29]: (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', A_29))=A_29 | ~r2_hidden(A_29, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_30, c_120])).
% 3.12/1.49  tff(c_162, plain, (![A_58]: (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', A_58))=A_58 | ~r2_hidden(A_58, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_124])).
% 3.12/1.49  tff(c_36, plain, (k1_funct_1(k5_relat_1('#skF_6', k2_funct_1('#skF_6')), '#skF_5')!='#skF_5' | k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.12/1.49  tff(c_64, plain, (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_36])).
% 3.12/1.49  tff(c_171, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_162, c_64])).
% 3.12/1.49  tff(c_181, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_171])).
% 3.12/1.49  tff(c_182, plain, (k1_funct_1(k5_relat_1('#skF_6', k2_funct_1('#skF_6')), '#skF_5')!='#skF_5'), inference(splitRight, [status(thm)], [c_36])).
% 3.12/1.49  tff(c_183, plain, (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_36])).
% 3.12/1.49  tff(c_190, plain, (![A_65, C_66]: (r2_hidden(k4_tarski(A_65, k1_funct_1(C_66, A_65)), C_66) | ~r2_hidden(A_65, k1_relat_1(C_66)) | ~v1_funct_1(C_66) | ~v1_relat_1(C_66))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.12/1.49  tff(c_199, plain, (r2_hidden(k4_tarski(k1_funct_1('#skF_6', '#skF_5'), '#skF_5'), k2_funct_1('#skF_6')) | ~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_183, c_190])).
% 3.12/1.49  tff(c_204, plain, (r2_hidden(k4_tarski(k1_funct_1('#skF_6', '#skF_5'), '#skF_5'), k2_funct_1('#skF_6')) | ~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_199])).
% 3.12/1.49  tff(c_259, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_204])).
% 3.12/1.49  tff(c_262, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_18, c_259])).
% 3.12/1.49  tff(c_266, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_262])).
% 3.12/1.49  tff(c_268, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_204])).
% 3.12/1.49  tff(c_224, plain, (![C_72, D_73, A_74]: (r2_hidden(k4_tarski(C_72, D_73), k4_relat_1(A_74)) | ~r2_hidden(k4_tarski(D_73, C_72), A_74) | ~v1_relat_1(k4_relat_1(A_74)) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.12/1.49  tff(c_236, plain, (![C_72, D_73]: (r2_hidden(k4_tarski(C_72, D_73), k2_funct_1('#skF_6')) | ~r2_hidden(k4_tarski(D_73, C_72), '#skF_6') | ~v1_relat_1(k4_relat_1('#skF_6')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_54, c_224])).
% 3.12/1.49  tff(c_242, plain, (![C_75, D_76]: (r2_hidden(k4_tarski(C_75, D_76), k2_funct_1('#skF_6')) | ~r2_hidden(k4_tarski(D_76, C_75), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_62, c_54, c_236])).
% 3.12/1.49  tff(c_248, plain, (![C_75, D_76]: (r2_hidden(C_75, k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~r2_hidden(k4_tarski(D_76, C_75), '#skF_6'))), inference(resolution, [status(thm)], [c_242, c_34])).
% 3.12/1.49  tff(c_255, plain, (![C_75, D_76]: (r2_hidden(C_75, k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~r2_hidden(k4_tarski(D_76, C_75), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_248])).
% 3.12/1.49  tff(c_271, plain, (![C_77, D_78]: (r2_hidden(C_77, k1_relat_1(k2_funct_1('#skF_6'))) | ~r2_hidden(k4_tarski(D_78, C_77), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_268, c_255])).
% 3.12/1.49  tff(c_274, plain, (![A_29]: (r2_hidden(k1_funct_1('#skF_6', A_29), k1_relat_1(k2_funct_1('#skF_6'))) | ~r2_hidden(A_29, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_30, c_271])).
% 3.12/1.49  tff(c_277, plain, (![A_29]: (r2_hidden(k1_funct_1('#skF_6', A_29), k1_relat_1(k2_funct_1('#skF_6'))) | ~r2_hidden(A_29, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_274])).
% 3.12/1.49  tff(c_267, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_relat_1(k2_funct_1('#skF_6'))) | r2_hidden(k4_tarski(k1_funct_1('#skF_6', '#skF_5'), '#skF_5'), k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_204])).
% 3.12/1.49  tff(c_321, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_relat_1(k2_funct_1('#skF_6')))), inference(splitLeft, [status(thm)], [c_267])).
% 3.12/1.49  tff(c_324, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_277, c_321])).
% 3.12/1.49  tff(c_328, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_324])).
% 3.12/1.49  tff(c_330, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_relat_1(k2_funct_1('#skF_6')))), inference(splitRight, [status(thm)], [c_267])).
% 3.12/1.49  tff(c_537, plain, (![A_98, C_99, B_100]: (r2_hidden(A_98, k1_relat_1(k5_relat_1(C_99, B_100))) | ~r2_hidden(k1_funct_1(C_99, A_98), k1_relat_1(B_100)) | ~r2_hidden(A_98, k1_relat_1(C_99)) | ~v1_funct_1(C_99) | ~v1_relat_1(C_99) | ~v1_funct_1(B_100) | ~v1_relat_1(B_100))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.12/1.49  tff(c_549, plain, (r2_hidden('#skF_5', k1_relat_1(k5_relat_1('#skF_6', k2_funct_1('#skF_6')))) | ~r2_hidden('#skF_5', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_330, c_537])).
% 3.12/1.49  tff(c_567, plain, (r2_hidden('#skF_5', k1_relat_1(k5_relat_1('#skF_6', k2_funct_1('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_268, c_44, c_42, c_38, c_549])).
% 3.12/1.49  tff(c_754, plain, (![C_109, B_110, A_111]: (k1_funct_1(k5_relat_1(C_109, B_110), A_111)=k1_funct_1(B_110, k1_funct_1(C_109, A_111)) | ~r2_hidden(A_111, k1_relat_1(k5_relat_1(C_109, B_110))) | ~v1_funct_1(C_109) | ~v1_relat_1(C_109) | ~v1_funct_1(B_110) | ~v1_relat_1(B_110))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.12/1.49  tff(c_766, plain, (k1_funct_1(k5_relat_1('#skF_6', k2_funct_1('#skF_6')), '#skF_5')=k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_5')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_567, c_754])).
% 3.12/1.49  tff(c_786, plain, (k1_funct_1(k5_relat_1('#skF_6', k2_funct_1('#skF_6')), '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_268, c_44, c_42, c_183, c_766])).
% 3.12/1.49  tff(c_788, plain, $false, inference(negUnitSimplification, [status(thm)], [c_182, c_786])).
% 3.12/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.49  
% 3.12/1.49  Inference rules
% 3.12/1.49  ----------------------
% 3.12/1.49  #Ref     : 0
% 3.12/1.49  #Sup     : 135
% 3.12/1.49  #Fact    : 0
% 3.12/1.49  #Define  : 0
% 3.12/1.49  #Split   : 7
% 3.12/1.49  #Chain   : 0
% 3.12/1.49  #Close   : 0
% 3.12/1.49  
% 3.12/1.49  Ordering : KBO
% 3.12/1.49  
% 3.12/1.49  Simplification rules
% 3.12/1.49  ----------------------
% 3.12/1.49  #Subsume      : 10
% 3.12/1.49  #Demod        : 198
% 3.12/1.49  #Tautology    : 51
% 3.12/1.49  #SimpNegUnit  : 1
% 3.12/1.49  #BackRed      : 0
% 3.12/1.49  
% 3.12/1.49  #Partial instantiations: 0
% 3.12/1.49  #Strategies tried      : 1
% 3.12/1.49  
% 3.12/1.49  Timing (in seconds)
% 3.12/1.49  ----------------------
% 3.12/1.49  Preprocessing        : 0.35
% 3.12/1.49  Parsing              : 0.18
% 3.12/1.49  CNF conversion       : 0.03
% 3.12/1.49  Main loop            : 0.35
% 3.12/1.49  Inferencing          : 0.13
% 3.12/1.49  Reduction            : 0.11
% 3.12/1.49  Demodulation         : 0.08
% 3.12/1.49  BG Simplification    : 0.02
% 3.12/1.49  Subsumption          : 0.07
% 3.12/1.49  Abstraction          : 0.02
% 3.12/1.49  MUC search           : 0.00
% 3.12/1.49  Cooper               : 0.00
% 3.12/1.49  Total                : 0.74
% 3.12/1.49  Index Insertion      : 0.00
% 3.12/1.49  Index Deletion       : 0.00
% 3.12/1.49  Index Matching       : 0.00
% 3.12/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
