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
% DateTime   : Thu Dec  3 10:03:46 EST 2020

% Result     : Theorem 7.16s
% Output     : CNFRefutation 7.44s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 658 expanded)
%              Number of leaves         :   32 ( 249 expanded)
%              Depth                    :   23
%              Number of atoms          :  292 (1835 expanded)
%              Number of equality atoms :   81 ( 609 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

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

tff(f_119,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( v2_funct_1(B)
            & r2_hidden(A,k2_relat_1(B)) )
         => ( A = k1_funct_1(B,k1_funct_1(k2_funct_1(B),A))
            & A = k1_funct_1(k5_relat_1(k2_funct_1(B),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_42,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k1_relat_1(B)) )
       => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
          & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(c_50,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_56,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_16,plain,(
    ! [A_7,C_43] :
      ( k1_funct_1(A_7,'#skF_4'(A_7,k2_relat_1(A_7),C_43)) = C_43
      | ~ r2_hidden(C_43,k2_relat_1(A_7))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    ! [A_7,C_43] :
      ( r2_hidden('#skF_4'(A_7,k2_relat_1(A_7),C_43),k1_relat_1(A_7))
      | ~ r2_hidden(C_43,k2_relat_1(A_7))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_38,plain,(
    ! [A_49] : v1_relat_1(k6_relat_1(A_49)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_40,plain,(
    ! [A_49] : v1_funct_1(k6_relat_1(A_49)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_10,plain,(
    ! [A_5] : k2_relat_1(k6_relat_1(A_5)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8,plain,(
    ! [A_5] : k1_relat_1(k6_relat_1(A_5)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_517,plain,(
    ! [A_86,C_87] :
      ( r2_hidden('#skF_4'(A_86,k2_relat_1(A_86),C_87),k1_relat_1(A_86))
      | ~ r2_hidden(C_87,k2_relat_1(A_86))
      | ~ v1_funct_1(A_86)
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_547,plain,(
    ! [A_5,C_87] :
      ( r2_hidden('#skF_4'(k6_relat_1(A_5),A_5,C_87),k1_relat_1(k6_relat_1(A_5)))
      | ~ r2_hidden(C_87,k2_relat_1(k6_relat_1(A_5)))
      | ~ v1_funct_1(k6_relat_1(A_5))
      | ~ v1_relat_1(k6_relat_1(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_517])).

tff(c_556,plain,(
    ! [A_5,C_87] :
      ( r2_hidden('#skF_4'(k6_relat_1(A_5),A_5,C_87),A_5)
      | ~ r2_hidden(C_87,A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40,c_10,c_8,c_547])).

tff(c_374,plain,(
    ! [A_79,C_80] :
      ( k1_funct_1(A_79,'#skF_4'(A_79,k2_relat_1(A_79),C_80)) = C_80
      | ~ r2_hidden(C_80,k2_relat_1(A_79))
      | ~ v1_funct_1(A_79)
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_396,plain,(
    ! [A_5,C_80] :
      ( k1_funct_1(k6_relat_1(A_5),'#skF_4'(k6_relat_1(A_5),A_5,C_80)) = C_80
      | ~ r2_hidden(C_80,k2_relat_1(k6_relat_1(A_5)))
      | ~ v1_funct_1(k6_relat_1(A_5))
      | ~ v1_relat_1(k6_relat_1(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_374])).

tff(c_404,plain,(
    ! [A_5,C_80] :
      ( k1_funct_1(k6_relat_1(A_5),'#skF_4'(k6_relat_1(A_5),A_5,C_80)) = C_80
      | ~ r2_hidden(C_80,A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40,c_10,c_396])).

tff(c_98,plain,(
    ! [A_64] :
      ( k5_relat_1(A_64,k6_relat_1(k2_relat_1(A_64))) = A_64
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_110,plain,(
    ! [A_5] :
      ( k5_relat_1(k6_relat_1(A_5),k6_relat_1(A_5)) = k6_relat_1(A_5)
      | ~ v1_relat_1(k6_relat_1(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_98])).

tff(c_114,plain,(
    ! [A_5] : k5_relat_1(k6_relat_1(A_5),k6_relat_1(A_5)) = k6_relat_1(A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_110])).

tff(c_2018,plain,(
    ! [C_146,B_147,A_148] :
      ( k1_funct_1(k5_relat_1(C_146,B_147),A_148) = k1_funct_1(B_147,k1_funct_1(C_146,A_148))
      | ~ r2_hidden(A_148,k1_relat_1(k5_relat_1(C_146,B_147)))
      | ~ v1_funct_1(C_146)
      | ~ v1_relat_1(C_146)
      | ~ v1_funct_1(B_147)
      | ~ v1_relat_1(B_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2143,plain,(
    ! [A_5,A_148] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_5),k6_relat_1(A_5)),A_148) = k1_funct_1(k6_relat_1(A_5),k1_funct_1(k6_relat_1(A_5),A_148))
      | ~ r2_hidden(A_148,k1_relat_1(k6_relat_1(A_5)))
      | ~ v1_funct_1(k6_relat_1(A_5))
      | ~ v1_relat_1(k6_relat_1(A_5))
      | ~ v1_funct_1(k6_relat_1(A_5))
      | ~ v1_relat_1(k6_relat_1(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_2018])).

tff(c_2201,plain,(
    ! [A_149,A_150] :
      ( k1_funct_1(k6_relat_1(A_149),k1_funct_1(k6_relat_1(A_149),A_150)) = k1_funct_1(k6_relat_1(A_149),A_150)
      | ~ r2_hidden(A_150,A_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40,c_38,c_40,c_8,c_114,c_2143])).

tff(c_3029,plain,(
    ! [A_173,C_174] :
      ( k1_funct_1(k6_relat_1(A_173),'#skF_4'(k6_relat_1(A_173),A_173,C_174)) = k1_funct_1(k6_relat_1(A_173),C_174)
      | ~ r2_hidden('#skF_4'(k6_relat_1(A_173),A_173,C_174),A_173)
      | ~ r2_hidden(C_174,A_173) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_404,c_2201])).

tff(c_3114,plain,(
    ! [A_176,C_177] :
      ( k1_funct_1(k6_relat_1(A_176),C_177) = C_177
      | ~ r2_hidden(C_177,A_176)
      | ~ r2_hidden('#skF_4'(k6_relat_1(A_176),A_176,C_177),A_176)
      | ~ r2_hidden(C_177,A_176) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3029,c_404])).

tff(c_3119,plain,(
    ! [A_178,C_179] :
      ( k1_funct_1(k6_relat_1(A_178),C_179) = C_179
      | ~ r2_hidden(C_179,A_178) ) ),
    inference(resolution,[status(thm)],[c_556,c_3114])).

tff(c_14,plain,(
    ! [A_7,D_46] :
      ( r2_hidden(k1_funct_1(A_7,D_46),k2_relat_1(A_7))
      | ~ r2_hidden(D_46,k1_relat_1(A_7))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_52,plain,(
    v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_46,plain,(
    ! [B_55,A_54] :
      ( k1_funct_1(k2_funct_1(B_55),k1_funct_1(B_55,A_54)) = A_54
      | ~ r2_hidden(A_54,k1_relat_1(B_55))
      | ~ v2_funct_1(B_55)
      | ~ v1_funct_1(B_55)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_36,plain,(
    ! [A_48] :
      ( v1_relat_1(k2_funct_1(A_48))
      | ~ v1_funct_1(A_48)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_115,plain,(
    ! [A_65] :
      ( k4_relat_1(A_65) = k2_funct_1(A_65)
      | ~ v2_funct_1(A_65)
      | ~ v1_funct_1(A_65)
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_118,plain,
    ( k4_relat_1('#skF_6') = k2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_115])).

tff(c_121,plain,(
    k4_relat_1('#skF_6') = k2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_118])).

tff(c_4,plain,(
    ! [A_4] :
      ( k2_relat_1(k4_relat_1(A_4)) = k1_relat_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_125,plain,
    ( k2_relat_1(k2_funct_1('#skF_6')) = k1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_4])).

tff(c_132,plain,(
    k2_relat_1(k2_funct_1('#skF_6')) = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_125])).

tff(c_12,plain,(
    ! [A_6] :
      ( k5_relat_1(A_6,k6_relat_1(k2_relat_1(A_6))) = A_6
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_139,plain,
    ( k5_relat_1(k2_funct_1('#skF_6'),k6_relat_1(k1_relat_1('#skF_6'))) = k2_funct_1('#skF_6')
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_12])).

tff(c_147,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_150,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_147])).

tff(c_154,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_150])).

tff(c_156,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_34,plain,(
    ! [A_48] :
      ( v1_funct_1(k2_funct_1(A_48))
      | ~ v1_funct_1(A_48)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6,plain,(
    ! [A_4] :
      ( k1_relat_1(k4_relat_1(A_4)) = k2_relat_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_128,plain,
    ( k1_relat_1(k2_funct_1('#skF_6')) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_6])).

tff(c_134,plain,(
    k1_relat_1(k2_funct_1('#skF_6')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_128])).

tff(c_192,plain,(
    ! [A_69,D_70] :
      ( r2_hidden(k1_funct_1(A_69,D_70),k2_relat_1(A_69))
      | ~ r2_hidden(D_70,k1_relat_1(A_69))
      | ~ v1_funct_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_195,plain,(
    ! [D_70] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),D_70),k1_relat_1('#skF_6'))
      | ~ r2_hidden(D_70,k1_relat_1(k2_funct_1('#skF_6')))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_192])).

tff(c_203,plain,(
    ! [D_70] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),D_70),k1_relat_1('#skF_6'))
      | ~ r2_hidden(D_70,k2_relat_1('#skF_6'))
      | ~ v1_funct_1(k2_funct_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_134,c_195])).

tff(c_443,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_203])).

tff(c_446,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_443])).

tff(c_450,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_446])).

tff(c_452,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_203])).

tff(c_155,plain,(
    k5_relat_1(k2_funct_1('#skF_6'),k6_relat_1(k1_relat_1('#skF_6'))) = k2_funct_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_2140,plain,(
    ! [A_148] :
      ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),k6_relat_1(k1_relat_1('#skF_6'))),A_148) = k1_funct_1(k6_relat_1(k1_relat_1('#skF_6')),k1_funct_1(k2_funct_1('#skF_6'),A_148))
      | ~ r2_hidden(A_148,k1_relat_1(k2_funct_1('#skF_6')))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6'))
      | ~ v1_funct_1(k6_relat_1(k1_relat_1('#skF_6')))
      | ~ v1_relat_1(k6_relat_1(k1_relat_1('#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_2018])).

tff(c_2250,plain,(
    ! [A_151] :
      ( k1_funct_1(k6_relat_1(k1_relat_1('#skF_6')),k1_funct_1(k2_funct_1('#skF_6'),A_151)) = k1_funct_1(k2_funct_1('#skF_6'),A_151)
      | ~ r2_hidden(A_151,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40,c_156,c_452,c_134,c_155,c_2140])).

tff(c_2278,plain,(
    ! [A_54] :
      ( k1_funct_1(k6_relat_1(k1_relat_1('#skF_6')),A_54) = k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6',A_54))
      | ~ r2_hidden(k1_funct_1('#skF_6',A_54),k2_relat_1('#skF_6'))
      | ~ r2_hidden(A_54,k1_relat_1('#skF_6'))
      | ~ v2_funct_1('#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_2250])).

tff(c_2434,plain,(
    ! [A_157] :
      ( k1_funct_1(k6_relat_1(k1_relat_1('#skF_6')),A_157) = k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6',A_157))
      | ~ r2_hidden(k1_funct_1('#skF_6',A_157),k2_relat_1('#skF_6'))
      | ~ r2_hidden(A_157,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2278])).

tff(c_2444,plain,(
    ! [D_46] :
      ( k1_funct_1(k6_relat_1(k1_relat_1('#skF_6')),D_46) = k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6',D_46))
      | ~ r2_hidden(D_46,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_14,c_2434])).

tff(c_2449,plain,(
    ! [D_46] :
      ( k1_funct_1(k6_relat_1(k1_relat_1('#skF_6')),D_46) = k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6',D_46))
      | ~ r2_hidden(D_46,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_2444])).

tff(c_3284,plain,(
    ! [C_182] :
      ( k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6',C_182)) = C_182
      | ~ r2_hidden(C_182,k1_relat_1('#skF_6'))
      | ~ r2_hidden(C_182,k1_relat_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3119,c_2449])).

tff(c_3328,plain,(
    ! [C_43] :
      ( k1_funct_1(k2_funct_1('#skF_6'),C_43) = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_43)
      | ~ r2_hidden('#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_43),k1_relat_1('#skF_6'))
      | ~ r2_hidden('#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_43),k1_relat_1('#skF_6'))
      | ~ r2_hidden(C_43,k2_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_3284])).

tff(c_3727,plain,(
    ! [C_206] :
      ( k1_funct_1(k2_funct_1('#skF_6'),C_206) = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_206)
      | ~ r2_hidden('#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_206),k1_relat_1('#skF_6'))
      | ~ r2_hidden(C_206,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_3328])).

tff(c_3731,plain,(
    ! [C_43] :
      ( k1_funct_1(k2_funct_1('#skF_6'),C_43) = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_43)
      | ~ r2_hidden(C_43,k2_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_18,c_3727])).

tff(c_3735,plain,(
    ! [C_207] :
      ( k1_funct_1(k2_funct_1('#skF_6'),C_207) = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_207)
      | ~ r2_hidden(C_207,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_3731])).

tff(c_3816,plain,(
    k1_funct_1(k2_funct_1('#skF_6'),'#skF_5') = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_3735])).

tff(c_48,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),'#skF_5') != '#skF_5'
    | k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_78,plain,(
    k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_3858,plain,(
    k1_funct_1('#skF_6','#skF_4'('#skF_6',k2_relat_1('#skF_6'),'#skF_5')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3816,c_78])).

tff(c_3898,plain,
    ( ~ r2_hidden('#skF_5',k2_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_3858])).

tff(c_3902,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_3898])).

tff(c_3904,plain,(
    k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_3954,plain,(
    ! [A_215] :
      ( k4_relat_1(A_215) = k2_funct_1(A_215)
      | ~ v2_funct_1(A_215)
      | ~ v1_funct_1(A_215)
      | ~ v1_relat_1(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3957,plain,
    ( k4_relat_1('#skF_6') = k2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_3954])).

tff(c_3960,plain,(
    k4_relat_1('#skF_6') = k2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_3957])).

tff(c_3964,plain,
    ( k2_relat_1(k2_funct_1('#skF_6')) = k1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3960,c_4])).

tff(c_3971,plain,(
    k2_relat_1(k2_funct_1('#skF_6')) = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3964])).

tff(c_3978,plain,
    ( k5_relat_1(k2_funct_1('#skF_6'),k6_relat_1(k1_relat_1('#skF_6'))) = k2_funct_1('#skF_6')
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3971,c_12])).

tff(c_3986,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_3978])).

tff(c_3989,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_3986])).

tff(c_3993,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_3989])).

tff(c_3995,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_3978])).

tff(c_3967,plain,
    ( k1_relat_1(k2_funct_1('#skF_6')) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3960,c_6])).

tff(c_3973,plain,(
    k1_relat_1(k2_funct_1('#skF_6')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3967])).

tff(c_4047,plain,(
    ! [A_220,D_221] :
      ( r2_hidden(k1_funct_1(A_220,D_221),k2_relat_1(A_220))
      | ~ r2_hidden(D_221,k1_relat_1(A_220))
      | ~ v1_funct_1(A_220)
      | ~ v1_relat_1(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4050,plain,(
    ! [D_221] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),D_221),k1_relat_1('#skF_6'))
      | ~ r2_hidden(D_221,k1_relat_1(k2_funct_1('#skF_6')))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3971,c_4047])).

tff(c_4061,plain,(
    ! [D_221] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),D_221),k1_relat_1('#skF_6'))
      | ~ r2_hidden(D_221,k2_relat_1('#skF_6'))
      | ~ v1_funct_1(k2_funct_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3995,c_3973,c_4050])).

tff(c_4273,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_4061])).

tff(c_4276,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_4273])).

tff(c_4280,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4276])).

tff(c_4282,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_4061])).

tff(c_3994,plain,(
    k5_relat_1(k2_funct_1('#skF_6'),k6_relat_1(k1_relat_1('#skF_6'))) = k2_funct_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_3978])).

tff(c_4000,plain,(
    ! [A_216,B_217] :
      ( k10_relat_1(A_216,k1_relat_1(B_217)) = k1_relat_1(k5_relat_1(A_216,B_217))
      | ~ v1_relat_1(B_217)
      | ~ v1_relat_1(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4015,plain,(
    ! [A_216,A_5] :
      ( k1_relat_1(k5_relat_1(A_216,k6_relat_1(A_5))) = k10_relat_1(A_216,A_5)
      | ~ v1_relat_1(k6_relat_1(A_5))
      | ~ v1_relat_1(A_216) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_4000])).

tff(c_4022,plain,(
    ! [A_218,A_219] :
      ( k1_relat_1(k5_relat_1(A_218,k6_relat_1(A_219))) = k10_relat_1(A_218,A_219)
      | ~ v1_relat_1(A_218) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4015])).

tff(c_4034,plain,
    ( k10_relat_1(k2_funct_1('#skF_6'),k1_relat_1('#skF_6')) = k1_relat_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3994,c_4022])).

tff(c_4044,plain,(
    k10_relat_1(k2_funct_1('#skF_6'),k1_relat_1('#skF_6')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3995,c_3973,c_4034])).

tff(c_2,plain,(
    ! [A_1,B_3] :
      ( k10_relat_1(A_1,k1_relat_1(B_3)) = k1_relat_1(k5_relat_1(A_1,B_3))
      | ~ v1_relat_1(B_3)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4090,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6')) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4044,c_2])).

tff(c_4097,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3995,c_56,c_4090])).

tff(c_5725,plain,(
    ! [C_294,B_295,A_296] :
      ( k1_funct_1(k5_relat_1(C_294,B_295),A_296) = k1_funct_1(B_295,k1_funct_1(C_294,A_296))
      | ~ r2_hidden(A_296,k1_relat_1(k5_relat_1(C_294,B_295)))
      | ~ v1_funct_1(C_294)
      | ~ v1_relat_1(C_294)
      | ~ v1_funct_1(B_295)
      | ~ v1_relat_1(B_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_5835,plain,(
    ! [A_296] :
      ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),A_296) = k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),A_296))
      | ~ r2_hidden(A_296,k2_relat_1('#skF_6'))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4097,c_5725])).

tff(c_6003,plain,(
    ! [A_301] :
      ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),A_301) = k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),A_301))
      | ~ r2_hidden(A_301,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_3995,c_4282,c_5835])).

tff(c_3903,plain,(
    k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),'#skF_5') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_6025,plain,
    ( k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) != '#skF_5'
    | ~ r2_hidden('#skF_5',k2_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6003,c_3903])).

tff(c_6043,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_3904,c_6025])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:30:32 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.16/2.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.16/2.48  
% 7.16/2.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.16/2.48  %$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 7.16/2.48  
% 7.16/2.48  %Foreground sorts:
% 7.16/2.48  
% 7.16/2.48  
% 7.16/2.48  %Background operators:
% 7.16/2.48  
% 7.16/2.48  
% 7.16/2.48  %Foreground operators:
% 7.16/2.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.16/2.48  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.16/2.48  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.16/2.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.16/2.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.16/2.48  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.16/2.48  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 7.16/2.48  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.16/2.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.16/2.48  tff('#skF_5', type, '#skF_5': $i).
% 7.16/2.48  tff('#skF_6', type, '#skF_6': $i).
% 7.16/2.48  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.16/2.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.16/2.48  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.16/2.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.16/2.48  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.16/2.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.16/2.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.16/2.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.16/2.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.16/2.48  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 7.16/2.48  
% 7.44/2.51  tff(f_119, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k2_relat_1(B))) => ((A = k1_funct_1(B, k1_funct_1(k2_funct_1(B), A))) & (A = k1_funct_1(k5_relat_1(k2_funct_1(B), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_funct_1)).
% 7.44/2.51  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 7.44/2.51  tff(f_81, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 7.44/2.51  tff(f_42, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 7.44/2.51  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 7.44/2.51  tff(f_94, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) => (k1_funct_1(k5_relat_1(C, B), A) = k1_funct_1(B, k1_funct_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_funct_1)).
% 7.44/2.51  tff(f_106, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_funct_1)).
% 7.44/2.51  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 7.44/2.51  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 7.44/2.51  tff(f_38, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 7.44/2.51  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 7.44/2.51  tff(c_50, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.44/2.51  tff(c_56, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.44/2.51  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.44/2.51  tff(c_16, plain, (![A_7, C_43]: (k1_funct_1(A_7, '#skF_4'(A_7, k2_relat_1(A_7), C_43))=C_43 | ~r2_hidden(C_43, k2_relat_1(A_7)) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.44/2.51  tff(c_18, plain, (![A_7, C_43]: (r2_hidden('#skF_4'(A_7, k2_relat_1(A_7), C_43), k1_relat_1(A_7)) | ~r2_hidden(C_43, k2_relat_1(A_7)) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.44/2.51  tff(c_38, plain, (![A_49]: (v1_relat_1(k6_relat_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.44/2.51  tff(c_40, plain, (![A_49]: (v1_funct_1(k6_relat_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.44/2.51  tff(c_10, plain, (![A_5]: (k2_relat_1(k6_relat_1(A_5))=A_5)), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.44/2.51  tff(c_8, plain, (![A_5]: (k1_relat_1(k6_relat_1(A_5))=A_5)), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.44/2.51  tff(c_517, plain, (![A_86, C_87]: (r2_hidden('#skF_4'(A_86, k2_relat_1(A_86), C_87), k1_relat_1(A_86)) | ~r2_hidden(C_87, k2_relat_1(A_86)) | ~v1_funct_1(A_86) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.44/2.51  tff(c_547, plain, (![A_5, C_87]: (r2_hidden('#skF_4'(k6_relat_1(A_5), A_5, C_87), k1_relat_1(k6_relat_1(A_5))) | ~r2_hidden(C_87, k2_relat_1(k6_relat_1(A_5))) | ~v1_funct_1(k6_relat_1(A_5)) | ~v1_relat_1(k6_relat_1(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_517])).
% 7.44/2.51  tff(c_556, plain, (![A_5, C_87]: (r2_hidden('#skF_4'(k6_relat_1(A_5), A_5, C_87), A_5) | ~r2_hidden(C_87, A_5))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40, c_10, c_8, c_547])).
% 7.44/2.51  tff(c_374, plain, (![A_79, C_80]: (k1_funct_1(A_79, '#skF_4'(A_79, k2_relat_1(A_79), C_80))=C_80 | ~r2_hidden(C_80, k2_relat_1(A_79)) | ~v1_funct_1(A_79) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.44/2.51  tff(c_396, plain, (![A_5, C_80]: (k1_funct_1(k6_relat_1(A_5), '#skF_4'(k6_relat_1(A_5), A_5, C_80))=C_80 | ~r2_hidden(C_80, k2_relat_1(k6_relat_1(A_5))) | ~v1_funct_1(k6_relat_1(A_5)) | ~v1_relat_1(k6_relat_1(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_374])).
% 7.44/2.51  tff(c_404, plain, (![A_5, C_80]: (k1_funct_1(k6_relat_1(A_5), '#skF_4'(k6_relat_1(A_5), A_5, C_80))=C_80 | ~r2_hidden(C_80, A_5))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40, c_10, c_396])).
% 7.44/2.51  tff(c_98, plain, (![A_64]: (k5_relat_1(A_64, k6_relat_1(k2_relat_1(A_64)))=A_64 | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.44/2.51  tff(c_110, plain, (![A_5]: (k5_relat_1(k6_relat_1(A_5), k6_relat_1(A_5))=k6_relat_1(A_5) | ~v1_relat_1(k6_relat_1(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_98])).
% 7.44/2.51  tff(c_114, plain, (![A_5]: (k5_relat_1(k6_relat_1(A_5), k6_relat_1(A_5))=k6_relat_1(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_110])).
% 7.44/2.51  tff(c_2018, plain, (![C_146, B_147, A_148]: (k1_funct_1(k5_relat_1(C_146, B_147), A_148)=k1_funct_1(B_147, k1_funct_1(C_146, A_148)) | ~r2_hidden(A_148, k1_relat_1(k5_relat_1(C_146, B_147))) | ~v1_funct_1(C_146) | ~v1_relat_1(C_146) | ~v1_funct_1(B_147) | ~v1_relat_1(B_147))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.44/2.51  tff(c_2143, plain, (![A_5, A_148]: (k1_funct_1(k5_relat_1(k6_relat_1(A_5), k6_relat_1(A_5)), A_148)=k1_funct_1(k6_relat_1(A_5), k1_funct_1(k6_relat_1(A_5), A_148)) | ~r2_hidden(A_148, k1_relat_1(k6_relat_1(A_5))) | ~v1_funct_1(k6_relat_1(A_5)) | ~v1_relat_1(k6_relat_1(A_5)) | ~v1_funct_1(k6_relat_1(A_5)) | ~v1_relat_1(k6_relat_1(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_114, c_2018])).
% 7.44/2.51  tff(c_2201, plain, (![A_149, A_150]: (k1_funct_1(k6_relat_1(A_149), k1_funct_1(k6_relat_1(A_149), A_150))=k1_funct_1(k6_relat_1(A_149), A_150) | ~r2_hidden(A_150, A_149))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40, c_38, c_40, c_8, c_114, c_2143])).
% 7.44/2.51  tff(c_3029, plain, (![A_173, C_174]: (k1_funct_1(k6_relat_1(A_173), '#skF_4'(k6_relat_1(A_173), A_173, C_174))=k1_funct_1(k6_relat_1(A_173), C_174) | ~r2_hidden('#skF_4'(k6_relat_1(A_173), A_173, C_174), A_173) | ~r2_hidden(C_174, A_173))), inference(superposition, [status(thm), theory('equality')], [c_404, c_2201])).
% 7.44/2.51  tff(c_3114, plain, (![A_176, C_177]: (k1_funct_1(k6_relat_1(A_176), C_177)=C_177 | ~r2_hidden(C_177, A_176) | ~r2_hidden('#skF_4'(k6_relat_1(A_176), A_176, C_177), A_176) | ~r2_hidden(C_177, A_176))), inference(superposition, [status(thm), theory('equality')], [c_3029, c_404])).
% 7.44/2.51  tff(c_3119, plain, (![A_178, C_179]: (k1_funct_1(k6_relat_1(A_178), C_179)=C_179 | ~r2_hidden(C_179, A_178))), inference(resolution, [status(thm)], [c_556, c_3114])).
% 7.44/2.51  tff(c_14, plain, (![A_7, D_46]: (r2_hidden(k1_funct_1(A_7, D_46), k2_relat_1(A_7)) | ~r2_hidden(D_46, k1_relat_1(A_7)) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.44/2.51  tff(c_52, plain, (v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.44/2.51  tff(c_46, plain, (![B_55, A_54]: (k1_funct_1(k2_funct_1(B_55), k1_funct_1(B_55, A_54))=A_54 | ~r2_hidden(A_54, k1_relat_1(B_55)) | ~v2_funct_1(B_55) | ~v1_funct_1(B_55) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.44/2.51  tff(c_36, plain, (![A_48]: (v1_relat_1(k2_funct_1(A_48)) | ~v1_funct_1(A_48) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.44/2.51  tff(c_115, plain, (![A_65]: (k4_relat_1(A_65)=k2_funct_1(A_65) | ~v2_funct_1(A_65) | ~v1_funct_1(A_65) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.44/2.51  tff(c_118, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_115])).
% 7.44/2.51  tff(c_121, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_118])).
% 7.44/2.51  tff(c_4, plain, (![A_4]: (k2_relat_1(k4_relat_1(A_4))=k1_relat_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.44/2.51  tff(c_125, plain, (k2_relat_1(k2_funct_1('#skF_6'))=k1_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_121, c_4])).
% 7.44/2.51  tff(c_132, plain, (k2_relat_1(k2_funct_1('#skF_6'))=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_125])).
% 7.44/2.51  tff(c_12, plain, (![A_6]: (k5_relat_1(A_6, k6_relat_1(k2_relat_1(A_6)))=A_6 | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.44/2.51  tff(c_139, plain, (k5_relat_1(k2_funct_1('#skF_6'), k6_relat_1(k1_relat_1('#skF_6')))=k2_funct_1('#skF_6') | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_132, c_12])).
% 7.44/2.51  tff(c_147, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_139])).
% 7.44/2.51  tff(c_150, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_36, c_147])).
% 7.44/2.51  tff(c_154, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_150])).
% 7.44/2.51  tff(c_156, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_139])).
% 7.44/2.51  tff(c_34, plain, (![A_48]: (v1_funct_1(k2_funct_1(A_48)) | ~v1_funct_1(A_48) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.44/2.51  tff(c_6, plain, (![A_4]: (k1_relat_1(k4_relat_1(A_4))=k2_relat_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.44/2.51  tff(c_128, plain, (k1_relat_1(k2_funct_1('#skF_6'))=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_121, c_6])).
% 7.44/2.51  tff(c_134, plain, (k1_relat_1(k2_funct_1('#skF_6'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_128])).
% 7.44/2.51  tff(c_192, plain, (![A_69, D_70]: (r2_hidden(k1_funct_1(A_69, D_70), k2_relat_1(A_69)) | ~r2_hidden(D_70, k1_relat_1(A_69)) | ~v1_funct_1(A_69) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.44/2.51  tff(c_195, plain, (![D_70]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), D_70), k1_relat_1('#skF_6')) | ~r2_hidden(D_70, k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_132, c_192])).
% 7.44/2.51  tff(c_203, plain, (![D_70]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), D_70), k1_relat_1('#skF_6')) | ~r2_hidden(D_70, k2_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_134, c_195])).
% 7.44/2.51  tff(c_443, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_203])).
% 7.44/2.51  tff(c_446, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_34, c_443])).
% 7.44/2.51  tff(c_450, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_446])).
% 7.44/2.51  tff(c_452, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_203])).
% 7.44/2.51  tff(c_155, plain, (k5_relat_1(k2_funct_1('#skF_6'), k6_relat_1(k1_relat_1('#skF_6')))=k2_funct_1('#skF_6')), inference(splitRight, [status(thm)], [c_139])).
% 7.44/2.51  tff(c_2140, plain, (![A_148]: (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), k6_relat_1(k1_relat_1('#skF_6'))), A_148)=k1_funct_1(k6_relat_1(k1_relat_1('#skF_6')), k1_funct_1(k2_funct_1('#skF_6'), A_148)) | ~r2_hidden(A_148, k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v1_funct_1(k6_relat_1(k1_relat_1('#skF_6'))) | ~v1_relat_1(k6_relat_1(k1_relat_1('#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_155, c_2018])).
% 7.44/2.51  tff(c_2250, plain, (![A_151]: (k1_funct_1(k6_relat_1(k1_relat_1('#skF_6')), k1_funct_1(k2_funct_1('#skF_6'), A_151))=k1_funct_1(k2_funct_1('#skF_6'), A_151) | ~r2_hidden(A_151, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40, c_156, c_452, c_134, c_155, c_2140])).
% 7.44/2.51  tff(c_2278, plain, (![A_54]: (k1_funct_1(k6_relat_1(k1_relat_1('#skF_6')), A_54)=k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', A_54)) | ~r2_hidden(k1_funct_1('#skF_6', A_54), k2_relat_1('#skF_6')) | ~r2_hidden(A_54, k1_relat_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_2250])).
% 7.44/2.51  tff(c_2434, plain, (![A_157]: (k1_funct_1(k6_relat_1(k1_relat_1('#skF_6')), A_157)=k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', A_157)) | ~r2_hidden(k1_funct_1('#skF_6', A_157), k2_relat_1('#skF_6')) | ~r2_hidden(A_157, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2278])).
% 7.44/2.51  tff(c_2444, plain, (![D_46]: (k1_funct_1(k6_relat_1(k1_relat_1('#skF_6')), D_46)=k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', D_46)) | ~r2_hidden(D_46, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_14, c_2434])).
% 7.44/2.51  tff(c_2449, plain, (![D_46]: (k1_funct_1(k6_relat_1(k1_relat_1('#skF_6')), D_46)=k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', D_46)) | ~r2_hidden(D_46, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_2444])).
% 7.44/2.51  tff(c_3284, plain, (![C_182]: (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', C_182))=C_182 | ~r2_hidden(C_182, k1_relat_1('#skF_6')) | ~r2_hidden(C_182, k1_relat_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_3119, c_2449])).
% 7.44/2.51  tff(c_3328, plain, (![C_43]: (k1_funct_1(k2_funct_1('#skF_6'), C_43)='#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_43) | ~r2_hidden('#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_43), k1_relat_1('#skF_6')) | ~r2_hidden('#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_43), k1_relat_1('#skF_6')) | ~r2_hidden(C_43, k2_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_3284])).
% 7.44/2.51  tff(c_3727, plain, (![C_206]: (k1_funct_1(k2_funct_1('#skF_6'), C_206)='#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_206) | ~r2_hidden('#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_206), k1_relat_1('#skF_6')) | ~r2_hidden(C_206, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_3328])).
% 7.44/2.51  tff(c_3731, plain, (![C_43]: (k1_funct_1(k2_funct_1('#skF_6'), C_43)='#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_43) | ~r2_hidden(C_43, k2_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_18, c_3727])).
% 7.44/2.51  tff(c_3735, plain, (![C_207]: (k1_funct_1(k2_funct_1('#skF_6'), C_207)='#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_207) | ~r2_hidden(C_207, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_3731])).
% 7.44/2.51  tff(c_3816, plain, (k1_funct_1(k2_funct_1('#skF_6'), '#skF_5')='#skF_4'('#skF_6', k2_relat_1('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_50, c_3735])).
% 7.44/2.51  tff(c_48, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), '#skF_5')!='#skF_5' | k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.44/2.51  tff(c_78, plain, (k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_48])).
% 7.44/2.51  tff(c_3858, plain, (k1_funct_1('#skF_6', '#skF_4'('#skF_6', k2_relat_1('#skF_6'), '#skF_5'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3816, c_78])).
% 7.44/2.51  tff(c_3898, plain, (~r2_hidden('#skF_5', k2_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_16, c_3858])).
% 7.44/2.51  tff(c_3902, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_3898])).
% 7.44/2.51  tff(c_3904, plain, (k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_48])).
% 7.44/2.51  tff(c_3954, plain, (![A_215]: (k4_relat_1(A_215)=k2_funct_1(A_215) | ~v2_funct_1(A_215) | ~v1_funct_1(A_215) | ~v1_relat_1(A_215))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.44/2.51  tff(c_3957, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_3954])).
% 7.44/2.51  tff(c_3960, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_3957])).
% 7.44/2.51  tff(c_3964, plain, (k2_relat_1(k2_funct_1('#skF_6'))=k1_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3960, c_4])).
% 7.44/2.51  tff(c_3971, plain, (k2_relat_1(k2_funct_1('#skF_6'))=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_3964])).
% 7.44/2.51  tff(c_3978, plain, (k5_relat_1(k2_funct_1('#skF_6'), k6_relat_1(k1_relat_1('#skF_6')))=k2_funct_1('#skF_6') | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3971, c_12])).
% 7.44/2.51  tff(c_3986, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_3978])).
% 7.44/2.51  tff(c_3989, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_36, c_3986])).
% 7.44/2.51  tff(c_3993, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_3989])).
% 7.44/2.51  tff(c_3995, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_3978])).
% 7.44/2.51  tff(c_3967, plain, (k1_relat_1(k2_funct_1('#skF_6'))=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3960, c_6])).
% 7.44/2.51  tff(c_3973, plain, (k1_relat_1(k2_funct_1('#skF_6'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_3967])).
% 7.44/2.51  tff(c_4047, plain, (![A_220, D_221]: (r2_hidden(k1_funct_1(A_220, D_221), k2_relat_1(A_220)) | ~r2_hidden(D_221, k1_relat_1(A_220)) | ~v1_funct_1(A_220) | ~v1_relat_1(A_220))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.44/2.51  tff(c_4050, plain, (![D_221]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), D_221), k1_relat_1('#skF_6')) | ~r2_hidden(D_221, k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_3971, c_4047])).
% 7.44/2.51  tff(c_4061, plain, (![D_221]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), D_221), k1_relat_1('#skF_6')) | ~r2_hidden(D_221, k2_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_3995, c_3973, c_4050])).
% 7.44/2.51  tff(c_4273, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_4061])).
% 7.44/2.51  tff(c_4276, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_34, c_4273])).
% 7.44/2.51  tff(c_4280, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_4276])).
% 7.44/2.51  tff(c_4282, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_4061])).
% 7.44/2.51  tff(c_3994, plain, (k5_relat_1(k2_funct_1('#skF_6'), k6_relat_1(k1_relat_1('#skF_6')))=k2_funct_1('#skF_6')), inference(splitRight, [status(thm)], [c_3978])).
% 7.44/2.51  tff(c_4000, plain, (![A_216, B_217]: (k10_relat_1(A_216, k1_relat_1(B_217))=k1_relat_1(k5_relat_1(A_216, B_217)) | ~v1_relat_1(B_217) | ~v1_relat_1(A_216))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.44/2.51  tff(c_4015, plain, (![A_216, A_5]: (k1_relat_1(k5_relat_1(A_216, k6_relat_1(A_5)))=k10_relat_1(A_216, A_5) | ~v1_relat_1(k6_relat_1(A_5)) | ~v1_relat_1(A_216))), inference(superposition, [status(thm), theory('equality')], [c_8, c_4000])).
% 7.44/2.51  tff(c_4022, plain, (![A_218, A_219]: (k1_relat_1(k5_relat_1(A_218, k6_relat_1(A_219)))=k10_relat_1(A_218, A_219) | ~v1_relat_1(A_218))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4015])).
% 7.44/2.51  tff(c_4034, plain, (k10_relat_1(k2_funct_1('#skF_6'), k1_relat_1('#skF_6'))=k1_relat_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3994, c_4022])).
% 7.44/2.51  tff(c_4044, plain, (k10_relat_1(k2_funct_1('#skF_6'), k1_relat_1('#skF_6'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3995, c_3973, c_4034])).
% 7.44/2.51  tff(c_2, plain, (![A_1, B_3]: (k10_relat_1(A_1, k1_relat_1(B_3))=k1_relat_1(k5_relat_1(A_1, B_3)) | ~v1_relat_1(B_3) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.44/2.51  tff(c_4090, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'))=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_4044, c_2])).
% 7.44/2.51  tff(c_4097, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3995, c_56, c_4090])).
% 7.44/2.51  tff(c_5725, plain, (![C_294, B_295, A_296]: (k1_funct_1(k5_relat_1(C_294, B_295), A_296)=k1_funct_1(B_295, k1_funct_1(C_294, A_296)) | ~r2_hidden(A_296, k1_relat_1(k5_relat_1(C_294, B_295))) | ~v1_funct_1(C_294) | ~v1_relat_1(C_294) | ~v1_funct_1(B_295) | ~v1_relat_1(B_295))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.44/2.51  tff(c_5835, plain, (![A_296]: (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), A_296)=k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), A_296)) | ~r2_hidden(A_296, k2_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_4097, c_5725])).
% 7.44/2.51  tff(c_6003, plain, (![A_301]: (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), A_301)=k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), A_301)) | ~r2_hidden(A_301, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_3995, c_4282, c_5835])).
% 7.44/2.51  tff(c_3903, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), '#skF_5')!='#skF_5'), inference(splitRight, [status(thm)], [c_48])).
% 7.44/2.51  tff(c_6025, plain, (k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))!='#skF_5' | ~r2_hidden('#skF_5', k2_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_6003, c_3903])).
% 7.44/2.51  tff(c_6043, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_3904, c_6025])).
% 7.44/2.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.44/2.51  
% 7.44/2.51  Inference rules
% 7.44/2.51  ----------------------
% 7.44/2.51  #Ref     : 2
% 7.44/2.51  #Sup     : 1463
% 7.44/2.51  #Fact    : 0
% 7.44/2.51  #Define  : 0
% 7.44/2.51  #Split   : 18
% 7.44/2.51  #Chain   : 0
% 7.44/2.51  #Close   : 0
% 7.44/2.51  
% 7.44/2.51  Ordering : KBO
% 7.44/2.51  
% 7.44/2.51  Simplification rules
% 7.44/2.51  ----------------------
% 7.44/2.51  #Subsume      : 233
% 7.44/2.51  #Demod        : 1524
% 7.44/2.51  #Tautology    : 317
% 7.44/2.51  #SimpNegUnit  : 0
% 7.44/2.51  #BackRed      : 1
% 7.44/2.51  
% 7.44/2.51  #Partial instantiations: 0
% 7.44/2.51  #Strategies tried      : 1
% 7.44/2.51  
% 7.44/2.51  Timing (in seconds)
% 7.44/2.51  ----------------------
% 7.44/2.51  Preprocessing        : 0.33
% 7.44/2.51  Parsing              : 0.17
% 7.44/2.51  CNF conversion       : 0.03
% 7.44/2.51  Main loop            : 1.39
% 7.44/2.51  Inferencing          : 0.47
% 7.44/2.51  Reduction            : 0.52
% 7.44/2.51  Demodulation         : 0.39
% 7.44/2.51  BG Simplification    : 0.08
% 7.44/2.51  Subsumption          : 0.23
% 7.44/2.51  Abstraction          : 0.09
% 7.44/2.51  MUC search           : 0.00
% 7.44/2.51  Cooper               : 0.00
% 7.44/2.51  Total                : 1.77
% 7.44/2.51  Index Insertion      : 0.00
% 7.44/2.51  Index Deletion       : 0.00
% 7.44/2.51  Index Matching       : 0.00
% 7.44/2.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
