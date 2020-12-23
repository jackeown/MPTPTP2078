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
% DateTime   : Thu Dec  3 10:05:39 EST 2020

% Result     : Theorem 3.90s
% Output     : CNFRefutation 4.11s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 383 expanded)
%              Number of leaves         :   30 ( 141 expanded)
%              Depth                    :   13
%              Number of atoms          :  195 (1090 expanded)
%              Number of equality atoms :   22 (  79 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_122,negated_conjecture,(
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

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_105,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
           => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_74,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_50,B_51)),k1_relat_1(A_50))
      | ~ v1_relat_1(B_51)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_46,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_52,plain,(
    r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_56,plain,(
    k2_xboole_0('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) = k1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_69,plain,(
    ! [C_3] :
      ( r1_tarski('#skF_4',C_3)
      | ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_1','#skF_2')),C_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_2])).

tff(c_78,plain,
    ( r1_tarski('#skF_4',k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_69])).

tff(c_84,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_78])).

tff(c_32,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_20,plain,(
    ! [A_24,B_25] :
      ( v1_funct_1(k7_relat_1(A_24,B_25))
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_28,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(k7_relat_1(A_8,B_9))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [B_23,A_22] :
      ( k1_relat_1(k7_relat_1(B_23,A_22)) = A_22
      | ~ r1_tarski(A_22,k1_relat_1(B_23))
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_97,plain,
    ( k1_relat_1(k7_relat_1('#skF_1','#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_18])).

tff(c_103,plain,(
    k1_relat_1(k7_relat_1('#skF_1','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_97])).

tff(c_180,plain,(
    ! [B_59,C_60,A_61] :
      ( k7_relat_1(k5_relat_1(B_59,C_60),A_61) = k5_relat_1(k7_relat_1(B_59,A_61),C_60)
      | ~ v1_relat_1(C_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k5_relat_1(A_6,B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_86,plain,(
    ! [B_52,A_53] :
      ( k1_relat_1(k7_relat_1(B_52,A_53)) = A_53
      | ~ r1_tarski(A_53,k1_relat_1(B_52))
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_94,plain,
    ( k1_relat_1(k7_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_4')) = '#skF_4'
    | ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_86])).

tff(c_124,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_127,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_124])).

tff(c_131,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_127])).

tff(c_132,plain,(
    k1_relat_1(k7_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_186,plain,
    ( k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_4'),'#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_132])).

tff(c_201,plain,(
    k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_4'),'#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_186])).

tff(c_16,plain,(
    ! [A_19,B_21] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_19,B_21)),k1_relat_1(A_19))
      | ~ v1_relat_1(B_21)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_221,plain,
    ( r1_tarski('#skF_4',k1_relat_1(k7_relat_1('#skF_1','#skF_4')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_16])).

tff(c_231,plain,
    ( r1_tarski('#skF_4','#skF_4')
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_103,c_221])).

tff(c_233,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_231])).

tff(c_236,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_233])).

tff(c_240,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_236])).

tff(c_242,plain,(
    v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_231])).

tff(c_12,plain,(
    ! [B_15,A_14] :
      ( k2_relat_1(k7_relat_1(B_15,A_14)) = k9_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_529,plain,(
    ! [B_81,A_82] :
      ( r1_tarski(k2_relat_1(B_81),k1_relat_1(A_82))
      | k1_relat_1(k5_relat_1(B_81,A_82)) != k1_relat_1(B_81)
      | ~ v1_funct_1(B_81)
      | ~ v1_relat_1(B_81)
      | ~ v1_funct_1(A_82)
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1459,plain,(
    ! [B_116,A_117,A_118] :
      ( r1_tarski(k9_relat_1(B_116,A_117),k1_relat_1(A_118))
      | k1_relat_1(k5_relat_1(k7_relat_1(B_116,A_117),A_118)) != k1_relat_1(k7_relat_1(B_116,A_117))
      | ~ v1_funct_1(k7_relat_1(B_116,A_117))
      | ~ v1_relat_1(k7_relat_1(B_116,A_117))
      | ~ v1_funct_1(A_118)
      | ~ v1_relat_1(A_118)
      | ~ v1_relat_1(B_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_529])).

tff(c_40,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_204,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_40])).

tff(c_205,plain,(
    ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_204])).

tff(c_1465,plain,
    ( k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_4'),'#skF_2')) != k1_relat_1(k7_relat_1('#skF_1','#skF_4'))
    | ~ v1_funct_1(k7_relat_1('#skF_1','#skF_4'))
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1459,c_205])).

tff(c_1511,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_28,c_242,c_103,c_201,c_1465])).

tff(c_1522,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_1511])).

tff(c_1526,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1522])).

tff(c_1528,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_36,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1595,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1528,c_36])).

tff(c_14,plain,(
    ! [A_16,B_18] :
      ( k10_relat_1(A_16,k1_relat_1(B_18)) = k1_relat_1(k5_relat_1(A_16,B_18))
      | ~ v1_relat_1(B_18)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1527,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_38,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1557,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_38])).

tff(c_1558,plain,(
    ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1557])).

tff(c_1570,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1528,c_1558])).

tff(c_1571,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1557])).

tff(c_1659,plain,(
    ! [A_120,C_121,B_122] :
      ( r1_tarski(A_120,k10_relat_1(C_121,B_122))
      | ~ r1_tarski(k9_relat_1(C_121,A_120),B_122)
      | ~ r1_tarski(A_120,k1_relat_1(C_121))
      | ~ v1_funct_1(C_121)
      | ~ v1_relat_1(C_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1662,plain,
    ( r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2')))
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1571,c_1659])).

tff(c_1668,plain,(
    r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1527,c_1662])).

tff(c_1677,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1668])).

tff(c_1680,plain,(
    r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_1677])).

tff(c_1682,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1595,c_1680])).

tff(c_1684,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_42,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1756,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1684,c_42])).

tff(c_1683,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_44,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1689,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_1684,c_44])).

tff(c_1891,plain,(
    ! [A_147,C_148,B_149] :
      ( r1_tarski(A_147,k10_relat_1(C_148,B_149))
      | ~ r1_tarski(k9_relat_1(C_148,A_147),B_149)
      | ~ r1_tarski(A_147,k1_relat_1(C_148))
      | ~ v1_funct_1(C_148)
      | ~ v1_relat_1(C_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1897,plain,
    ( r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2')))
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1689,c_1891])).

tff(c_1903,plain,(
    r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1683,c_1897])).

tff(c_1909,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1903])).

tff(c_1912,plain,(
    r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_1909])).

tff(c_1914,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1756,c_1912])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 12:57:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.90/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.90/1.67  
% 3.90/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.90/1.67  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.90/1.67  
% 3.90/1.67  %Foreground sorts:
% 3.90/1.67  
% 3.90/1.67  
% 3.90/1.67  %Background operators:
% 3.90/1.67  
% 3.90/1.67  
% 3.90/1.67  %Foreground operators:
% 3.90/1.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.90/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.90/1.67  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.90/1.67  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.90/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.90/1.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.90/1.67  tff('#skF_2', type, '#skF_2': $i).
% 3.90/1.67  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.90/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.90/1.67  tff('#skF_1', type, '#skF_1': $i).
% 3.90/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.90/1.67  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.90/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.90/1.67  tff('#skF_4', type, '#skF_4': $i).
% 3.90/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.90/1.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.90/1.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.90/1.67  
% 4.11/1.69  tff(f_122, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (r1_tarski(C, k1_relat_1(k5_relat_1(A, B))) <=> (r1_tarski(C, k1_relat_1(A)) & r1_tarski(k9_relat_1(A, C), k1_relat_1(B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_1)).
% 4.11/1.69  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 4.11/1.69  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.11/1.69  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 4.11/1.69  tff(f_82, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 4.11/1.69  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 4.11/1.69  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 4.11/1.69  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_relat_1)).
% 4.11/1.69  tff(f_39, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 4.11/1.69  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 4.11/1.69  tff(f_105, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(k5_relat_1(B, A)) = k1_relat_1(B)) => r1_tarski(k2_relat_1(B), k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_funct_1)).
% 4.11/1.69  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 4.11/1.69  tff(f_92, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 4.11/1.69  tff(c_34, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.11/1.69  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.11/1.69  tff(c_74, plain, (![A_50, B_51]: (r1_tarski(k1_relat_1(k5_relat_1(A_50, B_51)), k1_relat_1(A_50)) | ~v1_relat_1(B_51) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.11/1.69  tff(c_46, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.11/1.69  tff(c_52, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_46])).
% 4.11/1.69  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.11/1.69  tff(c_56, plain, (k2_xboole_0('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))=k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_4])).
% 4.11/1.69  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.11/1.69  tff(c_69, plain, (![C_3]: (r1_tarski('#skF_4', C_3) | ~r1_tarski(k1_relat_1(k5_relat_1('#skF_1', '#skF_2')), C_3))), inference(superposition, [status(thm), theory('equality')], [c_56, c_2])).
% 4.11/1.69  tff(c_78, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_74, c_69])).
% 4.11/1.69  tff(c_84, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_78])).
% 4.11/1.69  tff(c_32, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.11/1.69  tff(c_20, plain, (![A_24, B_25]: (v1_funct_1(k7_relat_1(A_24, B_25)) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.11/1.69  tff(c_28, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.11/1.69  tff(c_8, plain, (![A_8, B_9]: (v1_relat_1(k7_relat_1(A_8, B_9)) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.11/1.69  tff(c_18, plain, (![B_23, A_22]: (k1_relat_1(k7_relat_1(B_23, A_22))=A_22 | ~r1_tarski(A_22, k1_relat_1(B_23)) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.11/1.69  tff(c_97, plain, (k1_relat_1(k7_relat_1('#skF_1', '#skF_4'))='#skF_4' | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_84, c_18])).
% 4.11/1.69  tff(c_103, plain, (k1_relat_1(k7_relat_1('#skF_1', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_97])).
% 4.11/1.69  tff(c_180, plain, (![B_59, C_60, A_61]: (k7_relat_1(k5_relat_1(B_59, C_60), A_61)=k5_relat_1(k7_relat_1(B_59, A_61), C_60) | ~v1_relat_1(C_60) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.11/1.69  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k5_relat_1(A_6, B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.11/1.69  tff(c_86, plain, (![B_52, A_53]: (k1_relat_1(k7_relat_1(B_52, A_53))=A_53 | ~r1_tarski(A_53, k1_relat_1(B_52)) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.11/1.69  tff(c_94, plain, (k1_relat_1(k7_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_4'))='#skF_4' | ~v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_86])).
% 4.11/1.69  tff(c_124, plain, (~v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_94])).
% 4.11/1.69  tff(c_127, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6, c_124])).
% 4.11/1.69  tff(c_131, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_127])).
% 4.11/1.69  tff(c_132, plain, (k1_relat_1(k7_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_94])).
% 4.11/1.69  tff(c_186, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_4'), '#skF_2'))='#skF_4' | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_180, c_132])).
% 4.11/1.69  tff(c_201, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_4'), '#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_186])).
% 4.11/1.69  tff(c_16, plain, (![A_19, B_21]: (r1_tarski(k1_relat_1(k5_relat_1(A_19, B_21)), k1_relat_1(A_19)) | ~v1_relat_1(B_21) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.11/1.69  tff(c_221, plain, (r1_tarski('#skF_4', k1_relat_1(k7_relat_1('#skF_1', '#skF_4'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_201, c_16])).
% 4.11/1.69  tff(c_231, plain, (r1_tarski('#skF_4', '#skF_4') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_103, c_221])).
% 4.11/1.69  tff(c_233, plain, (~v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(splitLeft, [status(thm)], [c_231])).
% 4.11/1.69  tff(c_236, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_8, c_233])).
% 4.11/1.69  tff(c_240, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_236])).
% 4.11/1.69  tff(c_242, plain, (v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(splitRight, [status(thm)], [c_231])).
% 4.11/1.69  tff(c_12, plain, (![B_15, A_14]: (k2_relat_1(k7_relat_1(B_15, A_14))=k9_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.11/1.69  tff(c_529, plain, (![B_81, A_82]: (r1_tarski(k2_relat_1(B_81), k1_relat_1(A_82)) | k1_relat_1(k5_relat_1(B_81, A_82))!=k1_relat_1(B_81) | ~v1_funct_1(B_81) | ~v1_relat_1(B_81) | ~v1_funct_1(A_82) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.11/1.69  tff(c_1459, plain, (![B_116, A_117, A_118]: (r1_tarski(k9_relat_1(B_116, A_117), k1_relat_1(A_118)) | k1_relat_1(k5_relat_1(k7_relat_1(B_116, A_117), A_118))!=k1_relat_1(k7_relat_1(B_116, A_117)) | ~v1_funct_1(k7_relat_1(B_116, A_117)) | ~v1_relat_1(k7_relat_1(B_116, A_117)) | ~v1_funct_1(A_118) | ~v1_relat_1(A_118) | ~v1_relat_1(B_116))), inference(superposition, [status(thm), theory('equality')], [c_12, c_529])).
% 4.11/1.69  tff(c_40, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.11/1.69  tff(c_204, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_40])).
% 4.11/1.69  tff(c_205, plain, (~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_204])).
% 4.11/1.69  tff(c_1465, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_4'), '#skF_2'))!=k1_relat_1(k7_relat_1('#skF_1', '#skF_4')) | ~v1_funct_1(k7_relat_1('#skF_1', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_4')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1459, c_205])).
% 4.11/1.69  tff(c_1511, plain, (~v1_funct_1(k7_relat_1('#skF_1', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_28, c_242, c_103, c_201, c_1465])).
% 4.11/1.69  tff(c_1522, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_20, c_1511])).
% 4.11/1.69  tff(c_1526, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1522])).
% 4.11/1.69  tff(c_1528, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_204])).
% 4.11/1.69  tff(c_36, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.11/1.69  tff(c_1595, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_1528, c_36])).
% 4.11/1.69  tff(c_14, plain, (![A_16, B_18]: (k10_relat_1(A_16, k1_relat_1(B_18))=k1_relat_1(k5_relat_1(A_16, B_18)) | ~v1_relat_1(B_18) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.11/1.69  tff(c_1527, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_204])).
% 4.11/1.69  tff(c_38, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.11/1.69  tff(c_1557, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_38])).
% 4.11/1.69  tff(c_1558, plain, (~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_1557])).
% 4.11/1.69  tff(c_1570, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1528, c_1558])).
% 4.11/1.69  tff(c_1571, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_1557])).
% 4.11/1.69  tff(c_1659, plain, (![A_120, C_121, B_122]: (r1_tarski(A_120, k10_relat_1(C_121, B_122)) | ~r1_tarski(k9_relat_1(C_121, A_120), B_122) | ~r1_tarski(A_120, k1_relat_1(C_121)) | ~v1_funct_1(C_121) | ~v1_relat_1(C_121))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.11/1.69  tff(c_1662, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2'))) | ~r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1571, c_1659])).
% 4.11/1.69  tff(c_1668, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1527, c_1662])).
% 4.11/1.69  tff(c_1677, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14, c_1668])).
% 4.11/1.69  tff(c_1680, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_1677])).
% 4.11/1.69  tff(c_1682, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1595, c_1680])).
% 4.11/1.69  tff(c_1684, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_46])).
% 4.11/1.69  tff(c_42, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.11/1.69  tff(c_1756, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_1684, c_42])).
% 4.11/1.69  tff(c_1683, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_46])).
% 4.11/1.69  tff(c_44, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.11/1.69  tff(c_1689, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_1684, c_44])).
% 4.11/1.69  tff(c_1891, plain, (![A_147, C_148, B_149]: (r1_tarski(A_147, k10_relat_1(C_148, B_149)) | ~r1_tarski(k9_relat_1(C_148, A_147), B_149) | ~r1_tarski(A_147, k1_relat_1(C_148)) | ~v1_funct_1(C_148) | ~v1_relat_1(C_148))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.11/1.69  tff(c_1897, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2'))) | ~r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1689, c_1891])).
% 4.11/1.69  tff(c_1903, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1683, c_1897])).
% 4.11/1.69  tff(c_1909, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14, c_1903])).
% 4.11/1.69  tff(c_1912, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_1909])).
% 4.11/1.69  tff(c_1914, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1756, c_1912])).
% 4.11/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.11/1.69  
% 4.11/1.69  Inference rules
% 4.11/1.69  ----------------------
% 4.11/1.69  #Ref     : 0
% 4.11/1.69  #Sup     : 433
% 4.11/1.69  #Fact    : 0
% 4.11/1.69  #Define  : 0
% 4.11/1.69  #Split   : 9
% 4.11/1.69  #Chain   : 0
% 4.11/1.69  #Close   : 0
% 4.11/1.69  
% 4.11/1.69  Ordering : KBO
% 4.11/1.69  
% 4.11/1.69  Simplification rules
% 4.11/1.69  ----------------------
% 4.11/1.69  #Subsume      : 24
% 4.11/1.69  #Demod        : 262
% 4.11/1.69  #Tautology    : 149
% 4.11/1.69  #SimpNegUnit  : 4
% 4.11/1.69  #BackRed      : 0
% 4.11/1.69  
% 4.11/1.69  #Partial instantiations: 0
% 4.11/1.69  #Strategies tried      : 1
% 4.11/1.69  
% 4.11/1.69  Timing (in seconds)
% 4.11/1.69  ----------------------
% 4.11/1.69  Preprocessing        : 0.33
% 4.11/1.69  Parsing              : 0.18
% 4.11/1.69  CNF conversion       : 0.02
% 4.11/1.69  Main loop            : 0.57
% 4.11/1.69  Inferencing          : 0.21
% 4.11/1.69  Reduction            : 0.17
% 4.11/1.69  Demodulation         : 0.13
% 4.11/1.69  BG Simplification    : 0.03
% 4.11/1.69  Subsumption          : 0.11
% 4.11/1.69  Abstraction          : 0.03
% 4.11/1.69  MUC search           : 0.00
% 4.11/1.69  Cooper               : 0.00
% 4.11/1.69  Total                : 0.93
% 4.11/1.69  Index Insertion      : 0.00
% 4.11/1.69  Index Deletion       : 0.00
% 4.11/1.69  Index Matching       : 0.00
% 4.11/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
