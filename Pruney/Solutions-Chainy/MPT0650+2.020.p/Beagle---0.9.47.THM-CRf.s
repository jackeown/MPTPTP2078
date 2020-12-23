%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:47 EST 2020

% Result     : Theorem 6.95s
% Output     : CNFRefutation 6.95s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 922 expanded)
%              Number of leaves         :   29 ( 342 expanded)
%              Depth                    :   30
%              Number of atoms          :  322 (2811 expanded)
%              Number of equality atoms :   59 ( 819 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_111,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( v2_funct_1(B)
            & r2_hidden(A,k2_relat_1(B)) )
         => ( A = k1_funct_1(B,k1_funct_1(k2_funct_1(B),A))
            & A = k1_funct_1(k5_relat_1(k2_funct_1(B),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k1_relat_1(B)) )
       => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
          & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_48,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_46,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_42,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_103,plain,(
    ! [A_51,C_52] :
      ( r2_hidden(k4_tarski('#skF_4'(A_51,k2_relat_1(A_51),C_52),C_52),A_51)
      | ~ r2_hidden(C_52,k2_relat_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_36,plain,(
    ! [C_34,A_32,B_33] :
      ( k1_funct_1(C_34,A_32) = B_33
      | ~ r2_hidden(k4_tarski(A_32,B_33),C_34)
      | ~ v1_funct_1(C_34)
      | ~ v1_relat_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_119,plain,(
    ! [A_51,C_52] :
      ( k1_funct_1(A_51,'#skF_4'(A_51,k2_relat_1(A_51),C_52)) = C_52
      | ~ v1_funct_1(A_51)
      | ~ v1_relat_1(A_51)
      | ~ r2_hidden(C_52,k2_relat_1(A_51)) ) ),
    inference(resolution,[status(thm)],[c_103,c_36])).

tff(c_16,plain,(
    ! [A_20,C_22,B_21] :
      ( r2_hidden(A_20,k1_relat_1(C_22))
      | ~ r2_hidden(k4_tarski(A_20,B_21),C_22)
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_120,plain,(
    ! [A_51,C_52] :
      ( r2_hidden('#skF_4'(A_51,k2_relat_1(A_51),C_52),k1_relat_1(A_51))
      | ~ v1_relat_1(A_51)
      | ~ r2_hidden(C_52,k2_relat_1(A_51)) ) ),
    inference(resolution,[status(thm)],[c_103,c_16])).

tff(c_26,plain,(
    ! [A_25] :
      ( v1_relat_1(k2_funct_1(A_25))
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_44,plain,(
    v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_71,plain,(
    ! [A_42] :
      ( k4_relat_1(A_42) = k2_funct_1(A_42)
      | ~ v2_funct_1(A_42)
      | ~ v1_funct_1(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_74,plain,
    ( k4_relat_1('#skF_6') = k2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_71])).

tff(c_77,plain,(
    k4_relat_1('#skF_6') = k2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_74])).

tff(c_18,plain,(
    ! [A_23] :
      ( k2_relat_1(k4_relat_1(A_23)) = k1_relat_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_84,plain,
    ( k2_relat_1(k2_funct_1('#skF_6')) = k1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_18])).

tff(c_90,plain,(
    k2_relat_1(k2_funct_1('#skF_6')) = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_84])).

tff(c_20,plain,(
    ! [A_23] :
      ( k1_relat_1(k4_relat_1(A_23)) = k2_relat_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_81,plain,
    ( k1_relat_1(k2_funct_1('#skF_6')) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_20])).

tff(c_88,plain,(
    k1_relat_1(k2_funct_1('#skF_6')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_81])).

tff(c_138,plain,(
    ! [A_54,C_55] :
      ( r2_hidden('#skF_4'(A_54,k2_relat_1(A_54),C_55),k1_relat_1(A_54))
      | ~ v1_relat_1(A_54)
      | ~ r2_hidden(C_55,k2_relat_1(A_54)) ) ),
    inference(resolution,[status(thm)],[c_103,c_16])).

tff(c_144,plain,(
    ! [C_55] :
      ( r2_hidden('#skF_4'(k2_funct_1('#skF_6'),k2_relat_1(k2_funct_1('#skF_6')),C_55),k2_relat_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6'))
      | ~ r2_hidden(C_55,k2_relat_1(k2_funct_1('#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_138])).

tff(c_152,plain,(
    ! [C_55] :
      ( r2_hidden('#skF_4'(k2_funct_1('#skF_6'),k1_relat_1('#skF_6'),C_55),k2_relat_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6'))
      | ~ r2_hidden(C_55,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_90,c_144])).

tff(c_222,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_152])).

tff(c_225,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_222])).

tff(c_229,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_225])).

tff(c_231,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_24,plain,(
    ! [A_25] :
      ( v1_funct_1(k2_funct_1(A_25))
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_153,plain,(
    ! [A_56,C_57] :
      ( r2_hidden(k4_tarski(A_56,k1_funct_1(C_57,A_56)),C_57)
      | ~ r2_hidden(A_56,k1_relat_1(C_57))
      | ~ v1_funct_1(C_57)
      | ~ v1_relat_1(C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4,plain,(
    ! [C_16,A_1,D_19] :
      ( r2_hidden(C_16,k2_relat_1(A_1))
      | ~ r2_hidden(k4_tarski(D_19,C_16),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_167,plain,(
    ! [C_58,A_59] :
      ( r2_hidden(k1_funct_1(C_58,A_59),k2_relat_1(C_58))
      | ~ r2_hidden(A_59,k1_relat_1(C_58))
      | ~ v1_funct_1(C_58)
      | ~ v1_relat_1(C_58) ) ),
    inference(resolution,[status(thm)],[c_153,c_4])).

tff(c_170,plain,(
    ! [A_59] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),A_59),k1_relat_1('#skF_6'))
      | ~ r2_hidden(A_59,k1_relat_1(k2_funct_1('#skF_6')))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_167])).

tff(c_174,plain,(
    ! [A_59] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),A_59),k1_relat_1('#skF_6'))
      | ~ r2_hidden(A_59,k2_relat_1('#skF_6'))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_170])).

tff(c_298,plain,(
    ! [A_59] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),A_59),k1_relat_1('#skF_6'))
      | ~ r2_hidden(A_59,k2_relat_1('#skF_6'))
      | ~ v1_funct_1(k2_funct_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_174])).

tff(c_299,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_298])).

tff(c_305,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_299])).

tff(c_309,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_305])).

tff(c_311,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_298])).

tff(c_166,plain,(
    ! [C_57,A_56] :
      ( r2_hidden(k1_funct_1(C_57,A_56),k2_relat_1(C_57))
      | ~ r2_hidden(A_56,k1_relat_1(C_57))
      | ~ v1_funct_1(C_57)
      | ~ v1_relat_1(C_57) ) ),
    inference(resolution,[status(thm)],[c_153,c_4])).

tff(c_32,plain,(
    ! [B_31,A_30] :
      ( k1_funct_1(k2_funct_1(B_31),k1_funct_1(B_31,A_30)) = A_30
      | ~ r2_hidden(A_30,k1_relat_1(B_31))
      | ~ v2_funct_1(B_31)
      | ~ v1_funct_1(B_31)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_310,plain,(
    ! [A_59] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),A_59),k1_relat_1('#skF_6'))
      | ~ r2_hidden(A_59,k2_relat_1('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_298])).

tff(c_370,plain,(
    ! [B_84,C_85,A_86] :
      ( k1_funct_1(k5_relat_1(B_84,C_85),A_86) = k1_funct_1(C_85,k1_funct_1(B_84,A_86))
      | ~ r2_hidden(A_86,k1_relat_1(B_84))
      | ~ v1_funct_1(C_85)
      | ~ v1_relat_1(C_85)
      | ~ v1_funct_1(B_84)
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_372,plain,(
    ! [C_85,A_59] :
      ( k1_funct_1(k5_relat_1('#skF_6',C_85),k1_funct_1(k2_funct_1('#skF_6'),A_59)) = k1_funct_1(C_85,k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),A_59)))
      | ~ v1_funct_1(C_85)
      | ~ v1_relat_1(C_85)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(A_59,k2_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_310,c_370])).

tff(c_1743,plain,(
    ! [C_149,A_150] :
      ( k1_funct_1(k5_relat_1('#skF_6',C_149),k1_funct_1(k2_funct_1('#skF_6'),A_150)) = k1_funct_1(C_149,k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),A_150)))
      | ~ v1_funct_1(C_149)
      | ~ v1_relat_1(C_149)
      | ~ r2_hidden(A_150,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_372])).

tff(c_1804,plain,(
    ! [C_149,A_30] :
      ( k1_funct_1(C_149,k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6',A_30)))) = k1_funct_1(k5_relat_1('#skF_6',C_149),A_30)
      | ~ v1_funct_1(C_149)
      | ~ v1_relat_1(C_149)
      | ~ r2_hidden(k1_funct_1('#skF_6',A_30),k2_relat_1('#skF_6'))
      | ~ r2_hidden(A_30,k1_relat_1('#skF_6'))
      | ~ v2_funct_1('#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1743])).

tff(c_2786,plain,(
    ! [C_184,A_185] :
      ( k1_funct_1(C_184,k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6',A_185)))) = k1_funct_1(k5_relat_1('#skF_6',C_184),A_185)
      | ~ v1_funct_1(C_184)
      | ~ v1_relat_1(C_184)
      | ~ r2_hidden(k1_funct_1('#skF_6',A_185),k2_relat_1('#skF_6'))
      | ~ r2_hidden(A_185,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_1804])).

tff(c_2926,plain,(
    ! [C_184,A_30] :
      ( k1_funct_1(k5_relat_1('#skF_6',C_184),A_30) = k1_funct_1(C_184,k1_funct_1('#skF_6',A_30))
      | ~ v1_funct_1(C_184)
      | ~ v1_relat_1(C_184)
      | ~ r2_hidden(k1_funct_1('#skF_6',A_30),k2_relat_1('#skF_6'))
      | ~ r2_hidden(A_30,k1_relat_1('#skF_6'))
      | ~ r2_hidden(A_30,k1_relat_1('#skF_6'))
      | ~ v2_funct_1('#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2786])).

tff(c_2977,plain,(
    ! [C_186,A_187] :
      ( k1_funct_1(k5_relat_1('#skF_6',C_186),A_187) = k1_funct_1(C_186,k1_funct_1('#skF_6',A_187))
      | ~ v1_funct_1(C_186)
      | ~ v1_relat_1(C_186)
      | ~ r2_hidden(k1_funct_1('#skF_6',A_187),k2_relat_1('#skF_6'))
      | ~ r2_hidden(A_187,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_2926])).

tff(c_2993,plain,(
    ! [C_186,A_56] :
      ( k1_funct_1(k5_relat_1('#skF_6',C_186),A_56) = k1_funct_1(C_186,k1_funct_1('#skF_6',A_56))
      | ~ v1_funct_1(C_186)
      | ~ v1_relat_1(C_186)
      | ~ r2_hidden(A_56,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_166,c_2977])).

tff(c_3131,plain,(
    ! [C_190,A_191] :
      ( k1_funct_1(k5_relat_1('#skF_6',C_190),A_191) = k1_funct_1(C_190,k1_funct_1('#skF_6',A_191))
      | ~ v1_funct_1(C_190)
      | ~ v1_relat_1(C_190)
      | ~ r2_hidden(A_191,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_2993])).

tff(c_3200,plain,(
    ! [C_190,C_52] :
      ( k1_funct_1(k5_relat_1('#skF_6',C_190),'#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_52)) = k1_funct_1(C_190,k1_funct_1('#skF_6','#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_52)))
      | ~ v1_funct_1(C_190)
      | ~ v1_relat_1(C_190)
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(C_52,k2_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_120,c_3131])).

tff(c_3645,plain,(
    ! [C_197,C_198] :
      ( k1_funct_1(k5_relat_1('#skF_6',C_197),'#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_198)) = k1_funct_1(C_197,k1_funct_1('#skF_6','#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_198)))
      | ~ v1_funct_1(C_197)
      | ~ v1_relat_1(C_197)
      | ~ r2_hidden(C_198,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3200])).

tff(c_30,plain,(
    ! [B_31,A_30] :
      ( k1_funct_1(k5_relat_1(B_31,k2_funct_1(B_31)),A_30) = A_30
      | ~ r2_hidden(A_30,k1_relat_1(B_31))
      | ~ v2_funct_1(B_31)
      | ~ v1_funct_1(B_31)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_3661,plain,(
    ! [C_198] :
      ( k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_198))) = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_198)
      | ~ r2_hidden('#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_198),k1_relat_1('#skF_6'))
      | ~ v2_funct_1('#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6'))
      | ~ r2_hidden(C_198,k2_relat_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3645,c_30])).

tff(c_3684,plain,(
    ! [C_199] :
      ( k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_199))) = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_199)
      | ~ r2_hidden('#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_199),k1_relat_1('#skF_6'))
      | ~ r2_hidden(C_199,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_311,c_48,c_46,c_44,c_3661])).

tff(c_3742,plain,(
    ! [C_52] :
      ( k1_funct_1(k2_funct_1('#skF_6'),C_52) = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_52)
      | ~ r2_hidden('#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_52),k1_relat_1('#skF_6'))
      | ~ r2_hidden(C_52,k2_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(C_52,k2_relat_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_3684])).

tff(c_3766,plain,(
    ! [C_200] :
      ( k1_funct_1(k2_funct_1('#skF_6'),C_200) = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_200)
      | ~ r2_hidden('#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_200),k1_relat_1('#skF_6'))
      | ~ r2_hidden(C_200,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_3742])).

tff(c_3770,plain,(
    ! [C_52] :
      ( k1_funct_1(k2_funct_1('#skF_6'),C_52) = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_52)
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(C_52,k2_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_120,c_3766])).

tff(c_3774,plain,(
    ! [C_201] :
      ( k1_funct_1(k2_funct_1('#skF_6'),C_201) = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_201)
      | ~ r2_hidden(C_201,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3770])).

tff(c_3930,plain,(
    k1_funct_1(k2_funct_1('#skF_6'),'#skF_5') = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_3774])).

tff(c_40,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),'#skF_5') != '#skF_5'
    | k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_70,plain,(
    k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_4004,plain,(
    k1_funct_1('#skF_6','#skF_4'('#skF_6',k2_relat_1('#skF_6'),'#skF_5')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3930,c_70])).

tff(c_4071,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ r2_hidden('#skF_5',k2_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_4004])).

tff(c_4075,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_48,c_46,c_4071])).

tff(c_4077,plain,(
    k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_4082,plain,(
    ! [A_205] :
      ( k4_relat_1(A_205) = k2_funct_1(A_205)
      | ~ v2_funct_1(A_205)
      | ~ v1_funct_1(A_205)
      | ~ v1_relat_1(A_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4085,plain,
    ( k4_relat_1('#skF_6') = k2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_4082])).

tff(c_4088,plain,(
    k4_relat_1('#skF_6') = k2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_4085])).

tff(c_4095,plain,
    ( k2_relat_1(k2_funct_1('#skF_6')) = k1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4088,c_18])).

tff(c_4101,plain,(
    k2_relat_1(k2_funct_1('#skF_6')) = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4095])).

tff(c_4092,plain,
    ( k1_relat_1(k2_funct_1('#skF_6')) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4088,c_20])).

tff(c_4099,plain,(
    k1_relat_1(k2_funct_1('#skF_6')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4092])).

tff(c_4112,plain,(
    ! [A_209,C_210] :
      ( r2_hidden(k4_tarski('#skF_4'(A_209,k2_relat_1(A_209),C_210),C_210),A_209)
      | ~ r2_hidden(C_210,k2_relat_1(A_209)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4134,plain,(
    ! [A_216,C_217] :
      ( r2_hidden('#skF_4'(A_216,k2_relat_1(A_216),C_217),k1_relat_1(A_216))
      | ~ v1_relat_1(A_216)
      | ~ r2_hidden(C_217,k2_relat_1(A_216)) ) ),
    inference(resolution,[status(thm)],[c_4112,c_16])).

tff(c_4137,plain,(
    ! [C_217] :
      ( r2_hidden('#skF_4'(k2_funct_1('#skF_6'),k1_relat_1('#skF_6'),C_217),k1_relat_1(k2_funct_1('#skF_6')))
      | ~ v1_relat_1(k2_funct_1('#skF_6'))
      | ~ r2_hidden(C_217,k2_relat_1(k2_funct_1('#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4101,c_4134])).

tff(c_4147,plain,(
    ! [C_217] :
      ( r2_hidden('#skF_4'(k2_funct_1('#skF_6'),k1_relat_1('#skF_6'),C_217),k2_relat_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6'))
      | ~ r2_hidden(C_217,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4101,c_4099,c_4137])).

tff(c_4407,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_4147])).

tff(c_4410,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_4407])).

tff(c_4414,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_4410])).

tff(c_4416,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_4147])).

tff(c_4165,plain,(
    ! [A_222,C_223] :
      ( r2_hidden(k4_tarski(A_222,k1_funct_1(C_223,A_222)),C_223)
      | ~ r2_hidden(A_222,k1_relat_1(C_223))
      | ~ v1_funct_1(C_223)
      | ~ v1_relat_1(C_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4184,plain,(
    ! [C_224,A_225] :
      ( r2_hidden(k1_funct_1(C_224,A_225),k2_relat_1(C_224))
      | ~ r2_hidden(A_225,k1_relat_1(C_224))
      | ~ v1_funct_1(C_224)
      | ~ v1_relat_1(C_224) ) ),
    inference(resolution,[status(thm)],[c_4165,c_4])).

tff(c_4187,plain,(
    ! [A_225] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),A_225),k1_relat_1('#skF_6'))
      | ~ r2_hidden(A_225,k1_relat_1(k2_funct_1('#skF_6')))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4101,c_4184])).

tff(c_4194,plain,(
    ! [A_225] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),A_225),k1_relat_1('#skF_6'))
      | ~ r2_hidden(A_225,k2_relat_1('#skF_6'))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4099,c_4187])).

tff(c_4479,plain,(
    ! [A_225] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),A_225),k1_relat_1('#skF_6'))
      | ~ r2_hidden(A_225,k2_relat_1('#skF_6'))
      | ~ v1_funct_1(k2_funct_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4416,c_4194])).

tff(c_4480,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_4479])).

tff(c_4483,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_4480])).

tff(c_4487,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_4483])).

tff(c_4489,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_4479])).

tff(c_4727,plain,(
    ! [B_274,C_275,A_276] :
      ( k1_funct_1(k5_relat_1(B_274,C_275),A_276) = k1_funct_1(C_275,k1_funct_1(B_274,A_276))
      | ~ r2_hidden(A_276,k1_relat_1(B_274))
      | ~ v1_funct_1(C_275)
      | ~ v1_relat_1(C_275)
      | ~ v1_funct_1(B_274)
      | ~ v1_relat_1(B_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_5039,plain,(
    ! [A_290,C_291,A_292] :
      ( k1_funct_1(k5_relat_1(k4_relat_1(A_290),C_291),A_292) = k1_funct_1(C_291,k1_funct_1(k4_relat_1(A_290),A_292))
      | ~ r2_hidden(A_292,k2_relat_1(A_290))
      | ~ v1_funct_1(C_291)
      | ~ v1_relat_1(C_291)
      | ~ v1_funct_1(k4_relat_1(A_290))
      | ~ v1_relat_1(k4_relat_1(A_290))
      | ~ v1_relat_1(A_290) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_4727])).

tff(c_5081,plain,(
    ! [C_291,A_292] :
      ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),C_291),A_292) = k1_funct_1(C_291,k1_funct_1(k4_relat_1('#skF_6'),A_292))
      | ~ r2_hidden(A_292,k2_relat_1('#skF_6'))
      | ~ v1_funct_1(C_291)
      | ~ v1_relat_1(C_291)
      | ~ v1_funct_1(k4_relat_1('#skF_6'))
      | ~ v1_relat_1(k4_relat_1('#skF_6'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4088,c_5039])).

tff(c_5104,plain,(
    ! [C_294,A_295] :
      ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),C_294),A_295) = k1_funct_1(C_294,k1_funct_1(k2_funct_1('#skF_6'),A_295))
      | ~ r2_hidden(A_295,k2_relat_1('#skF_6'))
      | ~ v1_funct_1(C_294)
      | ~ v1_relat_1(C_294) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4416,c_4088,c_4489,c_4088,c_4088,c_5081])).

tff(c_4076,plain,(
    k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),'#skF_5') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_5131,plain,
    ( k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) != '#skF_5'
    | ~ r2_hidden('#skF_5',k2_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_5104,c_4076])).

tff(c_5152,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_42,c_4077,c_5131])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:00:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.95/2.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.95/2.44  
% 6.95/2.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.95/2.45  %$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 6.95/2.45  
% 6.95/2.45  %Foreground sorts:
% 6.95/2.45  
% 6.95/2.45  
% 6.95/2.45  %Background operators:
% 6.95/2.45  
% 6.95/2.45  
% 6.95/2.45  %Foreground operators:
% 6.95/2.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.95/2.45  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.95/2.45  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.95/2.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.95/2.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.95/2.45  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.95/2.45  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.95/2.45  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 6.95/2.45  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.95/2.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.95/2.45  tff('#skF_5', type, '#skF_5': $i).
% 6.95/2.45  tff('#skF_6', type, '#skF_6': $i).
% 6.95/2.45  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.95/2.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.95/2.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.95/2.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.95/2.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.95/2.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.95/2.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.95/2.45  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 6.95/2.45  
% 6.95/2.47  tff(f_111, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k2_relat_1(B))) => ((A = k1_funct_1(B, k1_funct_1(k2_funct_1(B), A))) & (A = k1_funct_1(k5_relat_1(k2_funct_1(B), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_funct_1)).
% 6.95/2.47  tff(f_33, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 6.95/2.47  tff(f_98, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 6.95/2.47  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 6.95/2.47  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 6.95/2.47  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 6.95/2.47  tff(f_47, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 6.95/2.47  tff(f_88, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_funct_1)).
% 6.95/2.47  tff(f_76, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 6.95/2.47  tff(c_48, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.95/2.47  tff(c_46, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.95/2.47  tff(c_42, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.95/2.47  tff(c_103, plain, (![A_51, C_52]: (r2_hidden(k4_tarski('#skF_4'(A_51, k2_relat_1(A_51), C_52), C_52), A_51) | ~r2_hidden(C_52, k2_relat_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.95/2.47  tff(c_36, plain, (![C_34, A_32, B_33]: (k1_funct_1(C_34, A_32)=B_33 | ~r2_hidden(k4_tarski(A_32, B_33), C_34) | ~v1_funct_1(C_34) | ~v1_relat_1(C_34))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.95/2.47  tff(c_119, plain, (![A_51, C_52]: (k1_funct_1(A_51, '#skF_4'(A_51, k2_relat_1(A_51), C_52))=C_52 | ~v1_funct_1(A_51) | ~v1_relat_1(A_51) | ~r2_hidden(C_52, k2_relat_1(A_51)))), inference(resolution, [status(thm)], [c_103, c_36])).
% 6.95/2.47  tff(c_16, plain, (![A_20, C_22, B_21]: (r2_hidden(A_20, k1_relat_1(C_22)) | ~r2_hidden(k4_tarski(A_20, B_21), C_22) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.95/2.47  tff(c_120, plain, (![A_51, C_52]: (r2_hidden('#skF_4'(A_51, k2_relat_1(A_51), C_52), k1_relat_1(A_51)) | ~v1_relat_1(A_51) | ~r2_hidden(C_52, k2_relat_1(A_51)))), inference(resolution, [status(thm)], [c_103, c_16])).
% 6.95/2.47  tff(c_26, plain, (![A_25]: (v1_relat_1(k2_funct_1(A_25)) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.95/2.47  tff(c_44, plain, (v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.95/2.47  tff(c_71, plain, (![A_42]: (k4_relat_1(A_42)=k2_funct_1(A_42) | ~v2_funct_1(A_42) | ~v1_funct_1(A_42) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.95/2.47  tff(c_74, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_44, c_71])).
% 6.95/2.47  tff(c_77, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_74])).
% 6.95/2.47  tff(c_18, plain, (![A_23]: (k2_relat_1(k4_relat_1(A_23))=k1_relat_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.95/2.47  tff(c_84, plain, (k2_relat_1(k2_funct_1('#skF_6'))=k1_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_77, c_18])).
% 6.95/2.47  tff(c_90, plain, (k2_relat_1(k2_funct_1('#skF_6'))=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_84])).
% 6.95/2.47  tff(c_20, plain, (![A_23]: (k1_relat_1(k4_relat_1(A_23))=k2_relat_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.95/2.47  tff(c_81, plain, (k1_relat_1(k2_funct_1('#skF_6'))=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_77, c_20])).
% 6.95/2.47  tff(c_88, plain, (k1_relat_1(k2_funct_1('#skF_6'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_81])).
% 6.95/2.47  tff(c_138, plain, (![A_54, C_55]: (r2_hidden('#skF_4'(A_54, k2_relat_1(A_54), C_55), k1_relat_1(A_54)) | ~v1_relat_1(A_54) | ~r2_hidden(C_55, k2_relat_1(A_54)))), inference(resolution, [status(thm)], [c_103, c_16])).
% 6.95/2.47  tff(c_144, plain, (![C_55]: (r2_hidden('#skF_4'(k2_funct_1('#skF_6'), k2_relat_1(k2_funct_1('#skF_6')), C_55), k2_relat_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~r2_hidden(C_55, k2_relat_1(k2_funct_1('#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_88, c_138])).
% 6.95/2.47  tff(c_152, plain, (![C_55]: (r2_hidden('#skF_4'(k2_funct_1('#skF_6'), k1_relat_1('#skF_6'), C_55), k2_relat_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~r2_hidden(C_55, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_90, c_144])).
% 6.95/2.47  tff(c_222, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_152])).
% 6.95/2.47  tff(c_225, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_26, c_222])).
% 6.95/2.47  tff(c_229, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_225])).
% 6.95/2.47  tff(c_231, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_152])).
% 6.95/2.47  tff(c_24, plain, (![A_25]: (v1_funct_1(k2_funct_1(A_25)) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.95/2.47  tff(c_153, plain, (![A_56, C_57]: (r2_hidden(k4_tarski(A_56, k1_funct_1(C_57, A_56)), C_57) | ~r2_hidden(A_56, k1_relat_1(C_57)) | ~v1_funct_1(C_57) | ~v1_relat_1(C_57))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.95/2.47  tff(c_4, plain, (![C_16, A_1, D_19]: (r2_hidden(C_16, k2_relat_1(A_1)) | ~r2_hidden(k4_tarski(D_19, C_16), A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.95/2.47  tff(c_167, plain, (![C_58, A_59]: (r2_hidden(k1_funct_1(C_58, A_59), k2_relat_1(C_58)) | ~r2_hidden(A_59, k1_relat_1(C_58)) | ~v1_funct_1(C_58) | ~v1_relat_1(C_58))), inference(resolution, [status(thm)], [c_153, c_4])).
% 6.95/2.47  tff(c_170, plain, (![A_59]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), A_59), k1_relat_1('#skF_6')) | ~r2_hidden(A_59, k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_90, c_167])).
% 6.95/2.47  tff(c_174, plain, (![A_59]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), A_59), k1_relat_1('#skF_6')) | ~r2_hidden(A_59, k2_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_170])).
% 6.95/2.47  tff(c_298, plain, (![A_59]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), A_59), k1_relat_1('#skF_6')) | ~r2_hidden(A_59, k2_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_174])).
% 6.95/2.47  tff(c_299, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_298])).
% 6.95/2.47  tff(c_305, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_24, c_299])).
% 6.95/2.47  tff(c_309, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_305])).
% 6.95/2.47  tff(c_311, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_298])).
% 6.95/2.47  tff(c_166, plain, (![C_57, A_56]: (r2_hidden(k1_funct_1(C_57, A_56), k2_relat_1(C_57)) | ~r2_hidden(A_56, k1_relat_1(C_57)) | ~v1_funct_1(C_57) | ~v1_relat_1(C_57))), inference(resolution, [status(thm)], [c_153, c_4])).
% 6.95/2.47  tff(c_32, plain, (![B_31, A_30]: (k1_funct_1(k2_funct_1(B_31), k1_funct_1(B_31, A_30))=A_30 | ~r2_hidden(A_30, k1_relat_1(B_31)) | ~v2_funct_1(B_31) | ~v1_funct_1(B_31) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.95/2.47  tff(c_310, plain, (![A_59]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), A_59), k1_relat_1('#skF_6')) | ~r2_hidden(A_59, k2_relat_1('#skF_6')))), inference(splitRight, [status(thm)], [c_298])).
% 6.95/2.47  tff(c_370, plain, (![B_84, C_85, A_86]: (k1_funct_1(k5_relat_1(B_84, C_85), A_86)=k1_funct_1(C_85, k1_funct_1(B_84, A_86)) | ~r2_hidden(A_86, k1_relat_1(B_84)) | ~v1_funct_1(C_85) | ~v1_relat_1(C_85) | ~v1_funct_1(B_84) | ~v1_relat_1(B_84))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.95/2.47  tff(c_372, plain, (![C_85, A_59]: (k1_funct_1(k5_relat_1('#skF_6', C_85), k1_funct_1(k2_funct_1('#skF_6'), A_59))=k1_funct_1(C_85, k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), A_59))) | ~v1_funct_1(C_85) | ~v1_relat_1(C_85) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~r2_hidden(A_59, k2_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_310, c_370])).
% 6.95/2.47  tff(c_1743, plain, (![C_149, A_150]: (k1_funct_1(k5_relat_1('#skF_6', C_149), k1_funct_1(k2_funct_1('#skF_6'), A_150))=k1_funct_1(C_149, k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), A_150))) | ~v1_funct_1(C_149) | ~v1_relat_1(C_149) | ~r2_hidden(A_150, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_372])).
% 6.95/2.47  tff(c_1804, plain, (![C_149, A_30]: (k1_funct_1(C_149, k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', A_30))))=k1_funct_1(k5_relat_1('#skF_6', C_149), A_30) | ~v1_funct_1(C_149) | ~v1_relat_1(C_149) | ~r2_hidden(k1_funct_1('#skF_6', A_30), k2_relat_1('#skF_6')) | ~r2_hidden(A_30, k1_relat_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1743])).
% 6.95/2.47  tff(c_2786, plain, (![C_184, A_185]: (k1_funct_1(C_184, k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', A_185))))=k1_funct_1(k5_relat_1('#skF_6', C_184), A_185) | ~v1_funct_1(C_184) | ~v1_relat_1(C_184) | ~r2_hidden(k1_funct_1('#skF_6', A_185), k2_relat_1('#skF_6')) | ~r2_hidden(A_185, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_1804])).
% 6.95/2.47  tff(c_2926, plain, (![C_184, A_30]: (k1_funct_1(k5_relat_1('#skF_6', C_184), A_30)=k1_funct_1(C_184, k1_funct_1('#skF_6', A_30)) | ~v1_funct_1(C_184) | ~v1_relat_1(C_184) | ~r2_hidden(k1_funct_1('#skF_6', A_30), k2_relat_1('#skF_6')) | ~r2_hidden(A_30, k1_relat_1('#skF_6')) | ~r2_hidden(A_30, k1_relat_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_2786])).
% 6.95/2.47  tff(c_2977, plain, (![C_186, A_187]: (k1_funct_1(k5_relat_1('#skF_6', C_186), A_187)=k1_funct_1(C_186, k1_funct_1('#skF_6', A_187)) | ~v1_funct_1(C_186) | ~v1_relat_1(C_186) | ~r2_hidden(k1_funct_1('#skF_6', A_187), k2_relat_1('#skF_6')) | ~r2_hidden(A_187, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_2926])).
% 6.95/2.47  tff(c_2993, plain, (![C_186, A_56]: (k1_funct_1(k5_relat_1('#skF_6', C_186), A_56)=k1_funct_1(C_186, k1_funct_1('#skF_6', A_56)) | ~v1_funct_1(C_186) | ~v1_relat_1(C_186) | ~r2_hidden(A_56, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_166, c_2977])).
% 6.95/2.47  tff(c_3131, plain, (![C_190, A_191]: (k1_funct_1(k5_relat_1('#skF_6', C_190), A_191)=k1_funct_1(C_190, k1_funct_1('#skF_6', A_191)) | ~v1_funct_1(C_190) | ~v1_relat_1(C_190) | ~r2_hidden(A_191, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_2993])).
% 6.95/2.47  tff(c_3200, plain, (![C_190, C_52]: (k1_funct_1(k5_relat_1('#skF_6', C_190), '#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_52))=k1_funct_1(C_190, k1_funct_1('#skF_6', '#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_52))) | ~v1_funct_1(C_190) | ~v1_relat_1(C_190) | ~v1_relat_1('#skF_6') | ~r2_hidden(C_52, k2_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_120, c_3131])).
% 6.95/2.47  tff(c_3645, plain, (![C_197, C_198]: (k1_funct_1(k5_relat_1('#skF_6', C_197), '#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_198))=k1_funct_1(C_197, k1_funct_1('#skF_6', '#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_198))) | ~v1_funct_1(C_197) | ~v1_relat_1(C_197) | ~r2_hidden(C_198, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_3200])).
% 6.95/2.47  tff(c_30, plain, (![B_31, A_30]: (k1_funct_1(k5_relat_1(B_31, k2_funct_1(B_31)), A_30)=A_30 | ~r2_hidden(A_30, k1_relat_1(B_31)) | ~v2_funct_1(B_31) | ~v1_funct_1(B_31) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.95/2.47  tff(c_3661, plain, (![C_198]: (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_198)))='#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_198) | ~r2_hidden('#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_198), k1_relat_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~r2_hidden(C_198, k2_relat_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_3645, c_30])).
% 6.95/2.47  tff(c_3684, plain, (![C_199]: (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_199)))='#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_199) | ~r2_hidden('#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_199), k1_relat_1('#skF_6')) | ~r2_hidden(C_199, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_311, c_48, c_46, c_44, c_3661])).
% 6.95/2.47  tff(c_3742, plain, (![C_52]: (k1_funct_1(k2_funct_1('#skF_6'), C_52)='#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_52) | ~r2_hidden('#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_52), k1_relat_1('#skF_6')) | ~r2_hidden(C_52, k2_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~r2_hidden(C_52, k2_relat_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_119, c_3684])).
% 6.95/2.47  tff(c_3766, plain, (![C_200]: (k1_funct_1(k2_funct_1('#skF_6'), C_200)='#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_200) | ~r2_hidden('#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_200), k1_relat_1('#skF_6')) | ~r2_hidden(C_200, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_3742])).
% 6.95/2.47  tff(c_3770, plain, (![C_52]: (k1_funct_1(k2_funct_1('#skF_6'), C_52)='#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_52) | ~v1_relat_1('#skF_6') | ~r2_hidden(C_52, k2_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_120, c_3766])).
% 6.95/2.47  tff(c_3774, plain, (![C_201]: (k1_funct_1(k2_funct_1('#skF_6'), C_201)='#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_201) | ~r2_hidden(C_201, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_3770])).
% 6.95/2.47  tff(c_3930, plain, (k1_funct_1(k2_funct_1('#skF_6'), '#skF_5')='#skF_4'('#skF_6', k2_relat_1('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_42, c_3774])).
% 6.95/2.47  tff(c_40, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), '#skF_5')!='#skF_5' | k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.95/2.47  tff(c_70, plain, (k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_40])).
% 6.95/2.47  tff(c_4004, plain, (k1_funct_1('#skF_6', '#skF_4'('#skF_6', k2_relat_1('#skF_6'), '#skF_5'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3930, c_70])).
% 6.95/2.47  tff(c_4071, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~r2_hidden('#skF_5', k2_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_119, c_4004])).
% 6.95/2.47  tff(c_4075, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_48, c_46, c_4071])).
% 6.95/2.47  tff(c_4077, plain, (k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_40])).
% 6.95/2.47  tff(c_4082, plain, (![A_205]: (k4_relat_1(A_205)=k2_funct_1(A_205) | ~v2_funct_1(A_205) | ~v1_funct_1(A_205) | ~v1_relat_1(A_205))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.95/2.47  tff(c_4085, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_44, c_4082])).
% 6.95/2.47  tff(c_4088, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_4085])).
% 6.95/2.47  tff(c_4095, plain, (k2_relat_1(k2_funct_1('#skF_6'))=k1_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_4088, c_18])).
% 6.95/2.47  tff(c_4101, plain, (k2_relat_1(k2_funct_1('#skF_6'))=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4095])).
% 6.95/2.47  tff(c_4092, plain, (k1_relat_1(k2_funct_1('#skF_6'))=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_4088, c_20])).
% 6.95/2.47  tff(c_4099, plain, (k1_relat_1(k2_funct_1('#skF_6'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4092])).
% 6.95/2.47  tff(c_4112, plain, (![A_209, C_210]: (r2_hidden(k4_tarski('#skF_4'(A_209, k2_relat_1(A_209), C_210), C_210), A_209) | ~r2_hidden(C_210, k2_relat_1(A_209)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.95/2.47  tff(c_4134, plain, (![A_216, C_217]: (r2_hidden('#skF_4'(A_216, k2_relat_1(A_216), C_217), k1_relat_1(A_216)) | ~v1_relat_1(A_216) | ~r2_hidden(C_217, k2_relat_1(A_216)))), inference(resolution, [status(thm)], [c_4112, c_16])).
% 6.95/2.47  tff(c_4137, plain, (![C_217]: (r2_hidden('#skF_4'(k2_funct_1('#skF_6'), k1_relat_1('#skF_6'), C_217), k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~r2_hidden(C_217, k2_relat_1(k2_funct_1('#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_4101, c_4134])).
% 6.95/2.47  tff(c_4147, plain, (![C_217]: (r2_hidden('#skF_4'(k2_funct_1('#skF_6'), k1_relat_1('#skF_6'), C_217), k2_relat_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~r2_hidden(C_217, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_4101, c_4099, c_4137])).
% 6.95/2.47  tff(c_4407, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_4147])).
% 6.95/2.47  tff(c_4410, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_26, c_4407])).
% 6.95/2.47  tff(c_4414, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_4410])).
% 6.95/2.47  tff(c_4416, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_4147])).
% 6.95/2.47  tff(c_4165, plain, (![A_222, C_223]: (r2_hidden(k4_tarski(A_222, k1_funct_1(C_223, A_222)), C_223) | ~r2_hidden(A_222, k1_relat_1(C_223)) | ~v1_funct_1(C_223) | ~v1_relat_1(C_223))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.95/2.47  tff(c_4184, plain, (![C_224, A_225]: (r2_hidden(k1_funct_1(C_224, A_225), k2_relat_1(C_224)) | ~r2_hidden(A_225, k1_relat_1(C_224)) | ~v1_funct_1(C_224) | ~v1_relat_1(C_224))), inference(resolution, [status(thm)], [c_4165, c_4])).
% 6.95/2.47  tff(c_4187, plain, (![A_225]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), A_225), k1_relat_1('#skF_6')) | ~r2_hidden(A_225, k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_4101, c_4184])).
% 6.95/2.47  tff(c_4194, plain, (![A_225]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), A_225), k1_relat_1('#skF_6')) | ~r2_hidden(A_225, k2_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_4099, c_4187])).
% 6.95/2.47  tff(c_4479, plain, (![A_225]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), A_225), k1_relat_1('#skF_6')) | ~r2_hidden(A_225, k2_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_4416, c_4194])).
% 6.95/2.47  tff(c_4480, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_4479])).
% 6.95/2.47  tff(c_4483, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_24, c_4480])).
% 6.95/2.47  tff(c_4487, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_4483])).
% 6.95/2.47  tff(c_4489, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_4479])).
% 6.95/2.47  tff(c_4727, plain, (![B_274, C_275, A_276]: (k1_funct_1(k5_relat_1(B_274, C_275), A_276)=k1_funct_1(C_275, k1_funct_1(B_274, A_276)) | ~r2_hidden(A_276, k1_relat_1(B_274)) | ~v1_funct_1(C_275) | ~v1_relat_1(C_275) | ~v1_funct_1(B_274) | ~v1_relat_1(B_274))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.95/2.47  tff(c_5039, plain, (![A_290, C_291, A_292]: (k1_funct_1(k5_relat_1(k4_relat_1(A_290), C_291), A_292)=k1_funct_1(C_291, k1_funct_1(k4_relat_1(A_290), A_292)) | ~r2_hidden(A_292, k2_relat_1(A_290)) | ~v1_funct_1(C_291) | ~v1_relat_1(C_291) | ~v1_funct_1(k4_relat_1(A_290)) | ~v1_relat_1(k4_relat_1(A_290)) | ~v1_relat_1(A_290))), inference(superposition, [status(thm), theory('equality')], [c_20, c_4727])).
% 6.95/2.47  tff(c_5081, plain, (![C_291, A_292]: (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), C_291), A_292)=k1_funct_1(C_291, k1_funct_1(k4_relat_1('#skF_6'), A_292)) | ~r2_hidden(A_292, k2_relat_1('#skF_6')) | ~v1_funct_1(C_291) | ~v1_relat_1(C_291) | ~v1_funct_1(k4_relat_1('#skF_6')) | ~v1_relat_1(k4_relat_1('#skF_6')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_4088, c_5039])).
% 6.95/2.47  tff(c_5104, plain, (![C_294, A_295]: (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), C_294), A_295)=k1_funct_1(C_294, k1_funct_1(k2_funct_1('#skF_6'), A_295)) | ~r2_hidden(A_295, k2_relat_1('#skF_6')) | ~v1_funct_1(C_294) | ~v1_relat_1(C_294))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4416, c_4088, c_4489, c_4088, c_4088, c_5081])).
% 6.95/2.47  tff(c_4076, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), '#skF_5')!='#skF_5'), inference(splitRight, [status(thm)], [c_40])).
% 6.95/2.47  tff(c_5131, plain, (k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))!='#skF_5' | ~r2_hidden('#skF_5', k2_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_5104, c_4076])).
% 6.95/2.47  tff(c_5152, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_42, c_4077, c_5131])).
% 6.95/2.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.95/2.47  
% 6.95/2.47  Inference rules
% 6.95/2.47  ----------------------
% 6.95/2.47  #Ref     : 0
% 6.95/2.47  #Sup     : 1096
% 6.95/2.47  #Fact    : 0
% 6.95/2.47  #Define  : 0
% 6.95/2.47  #Split   : 13
% 6.95/2.47  #Chain   : 0
% 6.95/2.47  #Close   : 0
% 6.95/2.47  
% 6.95/2.47  Ordering : KBO
% 6.95/2.47  
% 6.95/2.47  Simplification rules
% 6.95/2.47  ----------------------
% 6.95/2.47  #Subsume      : 218
% 6.95/2.47  #Demod        : 1337
% 6.95/2.47  #Tautology    : 256
% 6.95/2.47  #SimpNegUnit  : 0
% 6.95/2.47  #BackRed      : 3
% 6.95/2.47  
% 6.95/2.47  #Partial instantiations: 0
% 6.95/2.47  #Strategies tried      : 1
% 6.95/2.47  
% 6.95/2.47  Timing (in seconds)
% 6.95/2.47  ----------------------
% 6.95/2.47  Preprocessing        : 0.34
% 6.95/2.47  Parsing              : 0.18
% 6.95/2.47  CNF conversion       : 0.02
% 6.95/2.47  Main loop            : 1.30
% 6.95/2.47  Inferencing          : 0.49
% 6.95/2.47  Reduction            : 0.40
% 6.95/2.47  Demodulation         : 0.28
% 6.95/2.47  BG Simplification    : 0.07
% 6.95/2.47  Subsumption          : 0.26
% 6.95/2.47  Abstraction          : 0.09
% 6.95/2.47  MUC search           : 0.00
% 6.95/2.47  Cooper               : 0.00
% 6.95/2.47  Total                : 1.69
% 6.95/2.47  Index Insertion      : 0.00
% 6.95/2.47  Index Deletion       : 0.00
% 6.95/2.47  Index Matching       : 0.00
% 6.95/2.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
