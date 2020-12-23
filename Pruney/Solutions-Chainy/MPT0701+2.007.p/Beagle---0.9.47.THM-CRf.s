%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:02 EST 2020

% Result     : Theorem 5.89s
% Output     : CNFRefutation 5.89s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 199 expanded)
%              Number of leaves         :   25 (  87 expanded)
%              Depth                    :   23
%              Number of atoms          :  196 ( 892 expanded)
%              Number of equality atoms :   49 ( 324 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_5

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ! [D] :
                ( ( v1_relat_1(D)
                  & v1_funct_1(D) )
               => ( ( A = k2_relat_1(B)
                    & k1_relat_1(C) = A
                    & k1_relat_1(D) = A
                    & k5_relat_1(B,C) = k5_relat_1(B,D) )
                 => C = D ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_funct_1)).

tff(f_74,axiom,(
    ! [A] :
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

tff(f_33,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_26,plain,(
    '#skF_9' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_38,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_36,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_30,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_42,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_40,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_32,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_272,plain,(
    ! [A_79,B_80] :
      ( r2_hidden('#skF_5'(A_79,B_80),k1_relat_1(A_79))
      | B_80 = A_79
      | k1_relat_1(B_80) != k1_relat_1(A_79)
      | ~ v1_funct_1(B_80)
      | ~ v1_relat_1(B_80)
      | ~ v1_funct_1(A_79)
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_278,plain,(
    ! [B_80] :
      ( r2_hidden('#skF_5'('#skF_8',B_80),'#skF_6')
      | B_80 = '#skF_8'
      | k1_relat_1(B_80) != k1_relat_1('#skF_8')
      | ~ v1_funct_1(B_80)
      | ~ v1_relat_1(B_80)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_272])).

tff(c_282,plain,(
    ! [B_80] :
      ( r2_hidden('#skF_5'('#skF_8',B_80),'#skF_6')
      | B_80 = '#skF_8'
      | k1_relat_1(B_80) != '#skF_6'
      | ~ v1_funct_1(B_80)
      | ~ v1_relat_1(B_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_32,c_278])).

tff(c_46,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_44,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_34,plain,(
    k2_relat_1('#skF_7') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_64,plain,(
    ! [A_40,C_41] :
      ( r2_hidden(k4_tarski('#skF_4'(A_40,k2_relat_1(A_40),C_41),C_41),A_40)
      | ~ r2_hidden(C_41,k2_relat_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_70,plain,(
    ! [C_41] :
      ( r2_hidden(k4_tarski('#skF_4'('#skF_7','#skF_6',C_41),C_41),'#skF_7')
      | ~ r2_hidden(C_41,k2_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_64])).

tff(c_72,plain,(
    ! [C_41] :
      ( r2_hidden(k4_tarski('#skF_4'('#skF_7','#skF_6',C_41),C_41),'#skF_7')
      | ~ r2_hidden(C_41,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_70])).

tff(c_100,plain,(
    ! [A_49,C_50,B_51] :
      ( r2_hidden(A_49,k1_relat_1(C_50))
      | ~ r2_hidden(k4_tarski(A_49,B_51),C_50)
      | ~ v1_funct_1(C_50)
      | ~ v1_relat_1(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_103,plain,(
    ! [C_41] :
      ( r2_hidden('#skF_4'('#skF_7','#skF_6',C_41),k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(C_41,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_72,c_100])).

tff(c_109,plain,(
    ! [C_41] :
      ( r2_hidden('#skF_4'('#skF_7','#skF_6',C_41),k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_41,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_103])).

tff(c_113,plain,(
    ! [A_56,C_57] :
      ( r2_hidden(k4_tarski(A_56,k1_funct_1(C_57,A_56)),C_57)
      | ~ r2_hidden(A_56,k1_relat_1(C_57))
      | ~ v1_funct_1(C_57)
      | ~ v1_relat_1(C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [C_16,A_1,D_19] :
      ( r2_hidden(C_16,k2_relat_1(A_1))
      | ~ r2_hidden(k4_tarski(D_19,C_16),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_132,plain,(
    ! [C_58,A_59] :
      ( r2_hidden(k1_funct_1(C_58,A_59),k2_relat_1(C_58))
      | ~ r2_hidden(A_59,k1_relat_1(C_58))
      | ~ v1_funct_1(C_58)
      | ~ v1_relat_1(C_58) ) ),
    inference(resolution,[status(thm)],[c_113,c_4])).

tff(c_138,plain,(
    ! [A_59] :
      ( r2_hidden(k1_funct_1('#skF_7',A_59),'#skF_6')
      | ~ r2_hidden(A_59,k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_132])).

tff(c_142,plain,(
    ! [A_59] :
      ( r2_hidden(k1_funct_1('#skF_7',A_59),'#skF_6')
      | ~ r2_hidden(A_59,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_138])).

tff(c_80,plain,(
    ! [C_45,A_46,B_47] :
      ( k1_funct_1(C_45,A_46) = B_47
      | ~ r2_hidden(k4_tarski(A_46,B_47),C_45)
      | ~ v1_funct_1(C_45)
      | ~ v1_relat_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_83,plain,(
    ! [C_41] :
      ( k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_6',C_41)) = C_41
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(C_41,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_72,c_80])).

tff(c_89,plain,(
    ! [C_41] :
      ( k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_6',C_41)) = C_41
      | ~ r2_hidden(C_41,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_83])).

tff(c_28,plain,(
    k5_relat_1('#skF_7','#skF_9') = k5_relat_1('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_298,plain,(
    ! [B_85,C_86,A_87] :
      ( k1_funct_1(k5_relat_1(B_85,C_86),A_87) = k1_funct_1(C_86,k1_funct_1(B_85,A_87))
      | ~ r2_hidden(A_87,k1_relat_1(B_85))
      | ~ v1_funct_1(C_86)
      | ~ v1_relat_1(C_86)
      | ~ v1_funct_1(B_85)
      | ~ v1_relat_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_321,plain,(
    ! [C_86,C_41] :
      ( k1_funct_1(k5_relat_1('#skF_7',C_86),'#skF_4'('#skF_7','#skF_6',C_41)) = k1_funct_1(C_86,k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_6',C_41)))
      | ~ v1_funct_1(C_86)
      | ~ v1_relat_1(C_86)
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(C_41,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_109,c_298])).

tff(c_674,plain,(
    ! [C_108,C_109] :
      ( k1_funct_1(k5_relat_1('#skF_7',C_108),'#skF_4'('#skF_7','#skF_6',C_109)) = k1_funct_1(C_108,k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_6',C_109)))
      | ~ v1_funct_1(C_108)
      | ~ v1_relat_1(C_108)
      | ~ r2_hidden(C_109,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_321])).

tff(c_689,plain,(
    ! [C_109] :
      ( k1_funct_1(k5_relat_1('#skF_7','#skF_8'),'#skF_4'('#skF_7','#skF_6',C_109)) = k1_funct_1('#skF_9',k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_6',C_109)))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(C_109,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_674])).

tff(c_694,plain,(
    ! [C_110] :
      ( k1_funct_1(k5_relat_1('#skF_7','#skF_8'),'#skF_4'('#skF_7','#skF_6',C_110)) = k1_funct_1('#skF_9',k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_6',C_110)))
      | ~ r2_hidden(C_110,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_689])).

tff(c_344,plain,(
    ! [C_86,C_41] :
      ( k1_funct_1(k5_relat_1('#skF_7',C_86),'#skF_4'('#skF_7','#skF_6',C_41)) = k1_funct_1(C_86,k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_6',C_41)))
      | ~ v1_funct_1(C_86)
      | ~ v1_relat_1(C_86)
      | ~ r2_hidden(C_41,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_321])).

tff(c_700,plain,(
    ! [C_110] :
      ( k1_funct_1('#skF_9',k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_6',C_110))) = k1_funct_1('#skF_8',k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_6',C_110)))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(C_110,'#skF_6')
      | ~ r2_hidden(C_110,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_694,c_344])).

tff(c_720,plain,(
    ! [C_111] :
      ( k1_funct_1('#skF_9',k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_6',C_111))) = k1_funct_1('#skF_8',k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_6',C_111)))
      | ~ r2_hidden(C_111,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_700])).

tff(c_745,plain,(
    ! [C_112] :
      ( k1_funct_1('#skF_8',k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_6',C_112))) = k1_funct_1('#skF_9',C_112)
      | ~ r2_hidden(C_112,'#skF_6')
      | ~ r2_hidden(C_112,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_720])).

tff(c_16,plain,(
    ! [A_24,C_26] :
      ( r2_hidden(k4_tarski(A_24,k1_funct_1(C_26,A_24)),C_26)
      | ~ r2_hidden(A_24,k1_relat_1(C_26))
      | ~ v1_funct_1(C_26)
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_754,plain,(
    ! [C_112] :
      ( r2_hidden(k4_tarski(k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_6',C_112)),k1_funct_1('#skF_9',C_112)),'#skF_8')
      | ~ r2_hidden(k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_6',C_112)),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(C_112,'#skF_6')
      | ~ r2_hidden(C_112,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_745,c_16])).

tff(c_3681,plain,(
    ! [C_221] :
      ( r2_hidden(k4_tarski(k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_6',C_221)),k1_funct_1('#skF_9',C_221)),'#skF_8')
      | ~ r2_hidden(k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_6',C_221)),'#skF_6')
      | ~ r2_hidden(C_221,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_32,c_754])).

tff(c_3815,plain,(
    ! [C_225] :
      ( r2_hidden(k4_tarski(C_225,k1_funct_1('#skF_9',C_225)),'#skF_8')
      | ~ r2_hidden(k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_6',C_225)),'#skF_6')
      | ~ r2_hidden(C_225,'#skF_6')
      | ~ r2_hidden(C_225,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_3681])).

tff(c_18,plain,(
    ! [C_26,A_24,B_25] :
      ( k1_funct_1(C_26,A_24) = B_25
      | ~ r2_hidden(k4_tarski(A_24,B_25),C_26)
      | ~ v1_funct_1(C_26)
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3821,plain,(
    ! [C_225] :
      ( k1_funct_1('#skF_9',C_225) = k1_funct_1('#skF_8',C_225)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_6',C_225)),'#skF_6')
      | ~ r2_hidden(C_225,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_3815,c_18])).

tff(c_3874,plain,(
    ! [C_226] :
      ( k1_funct_1('#skF_9',C_226) = k1_funct_1('#skF_8',C_226)
      | ~ r2_hidden(k1_funct_1('#skF_7','#skF_4'('#skF_7','#skF_6',C_226)),'#skF_6')
      | ~ r2_hidden(C_226,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_3821])).

tff(c_3882,plain,(
    ! [C_227] :
      ( k1_funct_1('#skF_9',C_227) = k1_funct_1('#skF_8',C_227)
      | ~ r2_hidden(C_227,'#skF_6')
      | ~ r2_hidden('#skF_4'('#skF_7','#skF_6',C_227),k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_142,c_3874])).

tff(c_3931,plain,(
    ! [C_230] :
      ( k1_funct_1('#skF_9',C_230) = k1_funct_1('#skF_8',C_230)
      | ~ r2_hidden(C_230,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_109,c_3882])).

tff(c_4031,plain,(
    ! [B_232] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_8',B_232)) = k1_funct_1('#skF_8','#skF_5'('#skF_8',B_232))
      | B_232 = '#skF_8'
      | k1_relat_1(B_232) != '#skF_6'
      | ~ v1_funct_1(B_232)
      | ~ v1_relat_1(B_232) ) ),
    inference(resolution,[status(thm)],[c_282,c_3931])).

tff(c_22,plain,(
    ! [B_31,A_27] :
      ( k1_funct_1(B_31,'#skF_5'(A_27,B_31)) != k1_funct_1(A_27,'#skF_5'(A_27,B_31))
      | B_31 = A_27
      | k1_relat_1(B_31) != k1_relat_1(A_27)
      | ~ v1_funct_1(B_31)
      | ~ v1_relat_1(B_31)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4065,plain,
    ( k1_relat_1('#skF_9') != k1_relat_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | '#skF_9' = '#skF_8'
    | k1_relat_1('#skF_9') != '#skF_6'
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_4031,c_22])).

tff(c_4078,plain,(
    '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_30,c_42,c_40,c_30,c_32,c_4065])).

tff(c_4080,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_4078])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:58:47 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.89/2.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.89/2.09  
% 5.89/2.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.89/2.09  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_5
% 5.89/2.09  
% 5.89/2.09  %Foreground sorts:
% 5.89/2.09  
% 5.89/2.09  
% 5.89/2.09  %Background operators:
% 5.89/2.09  
% 5.89/2.09  
% 5.89/2.09  %Foreground operators:
% 5.89/2.09  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.89/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.89/2.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.89/2.09  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.89/2.09  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.89/2.09  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.89/2.09  tff('#skF_7', type, '#skF_7': $i).
% 5.89/2.09  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.89/2.09  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.89/2.09  tff('#skF_6', type, '#skF_6': $i).
% 5.89/2.09  tff('#skF_9', type, '#skF_9': $i).
% 5.89/2.09  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.89/2.09  tff('#skF_8', type, '#skF_8': $i).
% 5.89/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.89/2.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.89/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.89/2.09  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.89/2.09  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.89/2.09  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.89/2.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.89/2.09  
% 5.89/2.11  tff(f_99, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (![D]: ((v1_relat_1(D) & v1_funct_1(D)) => (((((A = k2_relat_1(B)) & (k1_relat_1(C) = A)) & (k1_relat_1(D) = A)) & (k5_relat_1(B, C) = k5_relat_1(B, D))) => (C = D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_funct_1)).
% 5.89/2.11  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 5.89/2.11  tff(f_33, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 5.89/2.11  tff(f_56, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 5.89/2.11  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 5.89/2.11  tff(c_26, plain, ('#skF_9'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.89/2.11  tff(c_38, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.89/2.11  tff(c_36, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.89/2.11  tff(c_30, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.89/2.11  tff(c_42, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.89/2.11  tff(c_40, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.89/2.11  tff(c_32, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.89/2.11  tff(c_272, plain, (![A_79, B_80]: (r2_hidden('#skF_5'(A_79, B_80), k1_relat_1(A_79)) | B_80=A_79 | k1_relat_1(B_80)!=k1_relat_1(A_79) | ~v1_funct_1(B_80) | ~v1_relat_1(B_80) | ~v1_funct_1(A_79) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.89/2.11  tff(c_278, plain, (![B_80]: (r2_hidden('#skF_5'('#skF_8', B_80), '#skF_6') | B_80='#skF_8' | k1_relat_1(B_80)!=k1_relat_1('#skF_8') | ~v1_funct_1(B_80) | ~v1_relat_1(B_80) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_272])).
% 5.89/2.11  tff(c_282, plain, (![B_80]: (r2_hidden('#skF_5'('#skF_8', B_80), '#skF_6') | B_80='#skF_8' | k1_relat_1(B_80)!='#skF_6' | ~v1_funct_1(B_80) | ~v1_relat_1(B_80))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_32, c_278])).
% 5.89/2.11  tff(c_46, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.89/2.11  tff(c_44, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.89/2.11  tff(c_34, plain, (k2_relat_1('#skF_7')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.89/2.11  tff(c_64, plain, (![A_40, C_41]: (r2_hidden(k4_tarski('#skF_4'(A_40, k2_relat_1(A_40), C_41), C_41), A_40) | ~r2_hidden(C_41, k2_relat_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.89/2.11  tff(c_70, plain, (![C_41]: (r2_hidden(k4_tarski('#skF_4'('#skF_7', '#skF_6', C_41), C_41), '#skF_7') | ~r2_hidden(C_41, k2_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_34, c_64])).
% 5.89/2.11  tff(c_72, plain, (![C_41]: (r2_hidden(k4_tarski('#skF_4'('#skF_7', '#skF_6', C_41), C_41), '#skF_7') | ~r2_hidden(C_41, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_70])).
% 5.89/2.11  tff(c_100, plain, (![A_49, C_50, B_51]: (r2_hidden(A_49, k1_relat_1(C_50)) | ~r2_hidden(k4_tarski(A_49, B_51), C_50) | ~v1_funct_1(C_50) | ~v1_relat_1(C_50))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.89/2.11  tff(c_103, plain, (![C_41]: (r2_hidden('#skF_4'('#skF_7', '#skF_6', C_41), k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(C_41, '#skF_6'))), inference(resolution, [status(thm)], [c_72, c_100])).
% 5.89/2.11  tff(c_109, plain, (![C_41]: (r2_hidden('#skF_4'('#skF_7', '#skF_6', C_41), k1_relat_1('#skF_7')) | ~r2_hidden(C_41, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_103])).
% 5.89/2.11  tff(c_113, plain, (![A_56, C_57]: (r2_hidden(k4_tarski(A_56, k1_funct_1(C_57, A_56)), C_57) | ~r2_hidden(A_56, k1_relat_1(C_57)) | ~v1_funct_1(C_57) | ~v1_relat_1(C_57))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.89/2.11  tff(c_4, plain, (![C_16, A_1, D_19]: (r2_hidden(C_16, k2_relat_1(A_1)) | ~r2_hidden(k4_tarski(D_19, C_16), A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.89/2.11  tff(c_132, plain, (![C_58, A_59]: (r2_hidden(k1_funct_1(C_58, A_59), k2_relat_1(C_58)) | ~r2_hidden(A_59, k1_relat_1(C_58)) | ~v1_funct_1(C_58) | ~v1_relat_1(C_58))), inference(resolution, [status(thm)], [c_113, c_4])).
% 5.89/2.11  tff(c_138, plain, (![A_59]: (r2_hidden(k1_funct_1('#skF_7', A_59), '#skF_6') | ~r2_hidden(A_59, k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_132])).
% 5.89/2.11  tff(c_142, plain, (![A_59]: (r2_hidden(k1_funct_1('#skF_7', A_59), '#skF_6') | ~r2_hidden(A_59, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_138])).
% 5.89/2.11  tff(c_80, plain, (![C_45, A_46, B_47]: (k1_funct_1(C_45, A_46)=B_47 | ~r2_hidden(k4_tarski(A_46, B_47), C_45) | ~v1_funct_1(C_45) | ~v1_relat_1(C_45))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.89/2.11  tff(c_83, plain, (![C_41]: (k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_6', C_41))=C_41 | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(C_41, '#skF_6'))), inference(resolution, [status(thm)], [c_72, c_80])).
% 5.89/2.11  tff(c_89, plain, (![C_41]: (k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_6', C_41))=C_41 | ~r2_hidden(C_41, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_83])).
% 5.89/2.11  tff(c_28, plain, (k5_relat_1('#skF_7', '#skF_9')=k5_relat_1('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.89/2.11  tff(c_298, plain, (![B_85, C_86, A_87]: (k1_funct_1(k5_relat_1(B_85, C_86), A_87)=k1_funct_1(C_86, k1_funct_1(B_85, A_87)) | ~r2_hidden(A_87, k1_relat_1(B_85)) | ~v1_funct_1(C_86) | ~v1_relat_1(C_86) | ~v1_funct_1(B_85) | ~v1_relat_1(B_85))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.89/2.11  tff(c_321, plain, (![C_86, C_41]: (k1_funct_1(k5_relat_1('#skF_7', C_86), '#skF_4'('#skF_7', '#skF_6', C_41))=k1_funct_1(C_86, k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_6', C_41))) | ~v1_funct_1(C_86) | ~v1_relat_1(C_86) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(C_41, '#skF_6'))), inference(resolution, [status(thm)], [c_109, c_298])).
% 5.89/2.11  tff(c_674, plain, (![C_108, C_109]: (k1_funct_1(k5_relat_1('#skF_7', C_108), '#skF_4'('#skF_7', '#skF_6', C_109))=k1_funct_1(C_108, k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_6', C_109))) | ~v1_funct_1(C_108) | ~v1_relat_1(C_108) | ~r2_hidden(C_109, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_321])).
% 5.89/2.11  tff(c_689, plain, (![C_109]: (k1_funct_1(k5_relat_1('#skF_7', '#skF_8'), '#skF_4'('#skF_7', '#skF_6', C_109))=k1_funct_1('#skF_9', k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_6', C_109))) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(C_109, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_674])).
% 5.89/2.11  tff(c_694, plain, (![C_110]: (k1_funct_1(k5_relat_1('#skF_7', '#skF_8'), '#skF_4'('#skF_7', '#skF_6', C_110))=k1_funct_1('#skF_9', k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_6', C_110))) | ~r2_hidden(C_110, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_689])).
% 5.89/2.11  tff(c_344, plain, (![C_86, C_41]: (k1_funct_1(k5_relat_1('#skF_7', C_86), '#skF_4'('#skF_7', '#skF_6', C_41))=k1_funct_1(C_86, k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_6', C_41))) | ~v1_funct_1(C_86) | ~v1_relat_1(C_86) | ~r2_hidden(C_41, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_321])).
% 5.89/2.11  tff(c_700, plain, (![C_110]: (k1_funct_1('#skF_9', k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_6', C_110)))=k1_funct_1('#skF_8', k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_6', C_110))) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(C_110, '#skF_6') | ~r2_hidden(C_110, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_694, c_344])).
% 5.89/2.11  tff(c_720, plain, (![C_111]: (k1_funct_1('#skF_9', k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_6', C_111)))=k1_funct_1('#skF_8', k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_6', C_111))) | ~r2_hidden(C_111, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_700])).
% 5.89/2.11  tff(c_745, plain, (![C_112]: (k1_funct_1('#skF_8', k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_6', C_112)))=k1_funct_1('#skF_9', C_112) | ~r2_hidden(C_112, '#skF_6') | ~r2_hidden(C_112, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_720])).
% 5.89/2.11  tff(c_16, plain, (![A_24, C_26]: (r2_hidden(k4_tarski(A_24, k1_funct_1(C_26, A_24)), C_26) | ~r2_hidden(A_24, k1_relat_1(C_26)) | ~v1_funct_1(C_26) | ~v1_relat_1(C_26))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.89/2.11  tff(c_754, plain, (![C_112]: (r2_hidden(k4_tarski(k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_6', C_112)), k1_funct_1('#skF_9', C_112)), '#skF_8') | ~r2_hidden(k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_6', C_112)), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(C_112, '#skF_6') | ~r2_hidden(C_112, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_745, c_16])).
% 5.89/2.11  tff(c_3681, plain, (![C_221]: (r2_hidden(k4_tarski(k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_6', C_221)), k1_funct_1('#skF_9', C_221)), '#skF_8') | ~r2_hidden(k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_6', C_221)), '#skF_6') | ~r2_hidden(C_221, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_32, c_754])).
% 5.89/2.11  tff(c_3815, plain, (![C_225]: (r2_hidden(k4_tarski(C_225, k1_funct_1('#skF_9', C_225)), '#skF_8') | ~r2_hidden(k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_6', C_225)), '#skF_6') | ~r2_hidden(C_225, '#skF_6') | ~r2_hidden(C_225, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_3681])).
% 5.89/2.11  tff(c_18, plain, (![C_26, A_24, B_25]: (k1_funct_1(C_26, A_24)=B_25 | ~r2_hidden(k4_tarski(A_24, B_25), C_26) | ~v1_funct_1(C_26) | ~v1_relat_1(C_26))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.89/2.11  tff(c_3821, plain, (![C_225]: (k1_funct_1('#skF_9', C_225)=k1_funct_1('#skF_8', C_225) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_6', C_225)), '#skF_6') | ~r2_hidden(C_225, '#skF_6'))), inference(resolution, [status(thm)], [c_3815, c_18])).
% 5.89/2.11  tff(c_3874, plain, (![C_226]: (k1_funct_1('#skF_9', C_226)=k1_funct_1('#skF_8', C_226) | ~r2_hidden(k1_funct_1('#skF_7', '#skF_4'('#skF_7', '#skF_6', C_226)), '#skF_6') | ~r2_hidden(C_226, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_3821])).
% 5.89/2.11  tff(c_3882, plain, (![C_227]: (k1_funct_1('#skF_9', C_227)=k1_funct_1('#skF_8', C_227) | ~r2_hidden(C_227, '#skF_6') | ~r2_hidden('#skF_4'('#skF_7', '#skF_6', C_227), k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_142, c_3874])).
% 5.89/2.11  tff(c_3931, plain, (![C_230]: (k1_funct_1('#skF_9', C_230)=k1_funct_1('#skF_8', C_230) | ~r2_hidden(C_230, '#skF_6'))), inference(resolution, [status(thm)], [c_109, c_3882])).
% 5.89/2.11  tff(c_4031, plain, (![B_232]: (k1_funct_1('#skF_9', '#skF_5'('#skF_8', B_232))=k1_funct_1('#skF_8', '#skF_5'('#skF_8', B_232)) | B_232='#skF_8' | k1_relat_1(B_232)!='#skF_6' | ~v1_funct_1(B_232) | ~v1_relat_1(B_232))), inference(resolution, [status(thm)], [c_282, c_3931])).
% 5.89/2.11  tff(c_22, plain, (![B_31, A_27]: (k1_funct_1(B_31, '#skF_5'(A_27, B_31))!=k1_funct_1(A_27, '#skF_5'(A_27, B_31)) | B_31=A_27 | k1_relat_1(B_31)!=k1_relat_1(A_27) | ~v1_funct_1(B_31) | ~v1_relat_1(B_31) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.89/2.11  tff(c_4065, plain, (k1_relat_1('#skF_9')!=k1_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | '#skF_9'='#skF_8' | k1_relat_1('#skF_9')!='#skF_6' | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_4031, c_22])).
% 5.89/2.11  tff(c_4078, plain, ('#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_30, c_42, c_40, c_30, c_32, c_4065])).
% 5.89/2.11  tff(c_4080, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_4078])).
% 5.89/2.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.89/2.11  
% 5.89/2.11  Inference rules
% 5.89/2.11  ----------------------
% 5.89/2.11  #Ref     : 1
% 5.89/2.11  #Sup     : 844
% 5.89/2.11  #Fact    : 0
% 5.89/2.11  #Define  : 0
% 5.89/2.11  #Split   : 4
% 5.89/2.11  #Chain   : 0
% 5.89/2.11  #Close   : 0
% 5.89/2.11  
% 5.89/2.11  Ordering : KBO
% 6.03/2.11  
% 6.03/2.11  Simplification rules
% 6.03/2.11  ----------------------
% 6.03/2.11  #Subsume      : 155
% 6.03/2.11  #Demod        : 1131
% 6.03/2.11  #Tautology    : 267
% 6.03/2.11  #SimpNegUnit  : 1
% 6.03/2.11  #BackRed      : 11
% 6.03/2.11  
% 6.03/2.11  #Partial instantiations: 0
% 6.03/2.11  #Strategies tried      : 1
% 6.03/2.11  
% 6.03/2.11  Timing (in seconds)
% 6.03/2.11  ----------------------
% 6.03/2.11  Preprocessing        : 0.31
% 6.03/2.11  Parsing              : 0.16
% 6.03/2.11  CNF conversion       : 0.03
% 6.03/2.11  Main loop            : 1.02
% 6.03/2.11  Inferencing          : 0.41
% 6.03/2.11  Reduction            : 0.31
% 6.03/2.11  Demodulation         : 0.21
% 6.03/2.11  BG Simplification    : 0.05
% 6.03/2.11  Subsumption          : 0.19
% 6.03/2.11  Abstraction          : 0.05
% 6.03/2.11  MUC search           : 0.00
% 6.03/2.11  Cooper               : 0.00
% 6.03/2.11  Total                : 1.36
% 6.03/2.11  Index Insertion      : 0.00
% 6.03/2.11  Index Deletion       : 0.00
% 6.03/2.11  Index Matching       : 0.00
% 6.03/2.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
