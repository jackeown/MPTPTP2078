%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:45 EST 2020

% Result     : Theorem 7.28s
% Output     : CNFRefutation 7.28s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 965 expanded)
%              Number of leaves         :   34 ( 366 expanded)
%              Depth                    :   23
%              Number of atoms          :  302 (2831 expanded)
%              Number of equality atoms :   86 ( 884 expanded)
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

tff(f_127,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( v2_funct_1(B)
            & r2_hidden(A,k2_relat_1(B)) )
         => ( A = k1_funct_1(B,k1_funct_1(k2_funct_1(B),A))
            & A = k1_funct_1(k5_relat_1(k2_funct_1(B),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_69,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_50,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

tff(f_114,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k1_relat_1(B)) )
       => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
          & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

tff(c_54,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_60,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_58,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_56,plain,(
    v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_155,plain,(
    ! [A_70] :
      ( k4_relat_1(A_70) = k2_funct_1(A_70)
      | ~ v2_funct_1(A_70)
      | ~ v1_funct_1(A_70)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_161,plain,
    ( k4_relat_1('#skF_6') = k2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_155])).

tff(c_167,plain,(
    k4_relat_1('#skF_6') = k2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_161])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_relat_1(k4_relat_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_180,plain,
    ( v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_2])).

tff(c_190,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_180])).

tff(c_4,plain,(
    ! [A_2] :
      ( k4_relat_1(k4_relat_1(A_2)) = A_2
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_177,plain,
    ( k4_relat_1(k2_funct_1('#skF_6')) = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_4])).

tff(c_188,plain,(
    k4_relat_1(k2_funct_1('#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_177])).

tff(c_10,plain,(
    ! [A_6] :
      ( k1_relat_1(k4_relat_1(A_6)) = k2_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_174,plain,
    ( k1_relat_1(k2_funct_1('#skF_6')) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_10])).

tff(c_186,plain,(
    k1_relat_1(k2_funct_1('#skF_6')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_174])).

tff(c_8,plain,(
    ! [A_6] :
      ( k2_relat_1(k4_relat_1(A_6)) = k1_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_536,plain,(
    ! [A_85,C_86] :
      ( k1_funct_1(A_85,'#skF_4'(A_85,k2_relat_1(A_85),C_86)) = C_86
      | ~ r2_hidden(C_86,k2_relat_1(A_85))
      | ~ v1_funct_1(A_85)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4051,plain,(
    ! [A_180,C_181] :
      ( k1_funct_1(k4_relat_1(A_180),'#skF_4'(k4_relat_1(A_180),k1_relat_1(A_180),C_181)) = C_181
      | ~ r2_hidden(C_181,k2_relat_1(k4_relat_1(A_180)))
      | ~ v1_funct_1(k4_relat_1(A_180))
      | ~ v1_relat_1(k4_relat_1(A_180))
      | ~ v1_relat_1(A_180) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_536])).

tff(c_4158,plain,(
    ! [C_181] :
      ( k1_funct_1(k4_relat_1(k2_funct_1('#skF_6')),'#skF_4'(k4_relat_1(k2_funct_1('#skF_6')),k2_relat_1('#skF_6'),C_181)) = C_181
      | ~ r2_hidden(C_181,k2_relat_1(k4_relat_1(k2_funct_1('#skF_6'))))
      | ~ v1_funct_1(k4_relat_1(k2_funct_1('#skF_6')))
      | ~ v1_relat_1(k4_relat_1(k2_funct_1('#skF_6')))
      | ~ v1_relat_1(k2_funct_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_4051])).

tff(c_4194,plain,(
    ! [C_181] :
      ( k1_funct_1('#skF_6','#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_181)) = C_181
      | ~ r2_hidden(C_181,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_60,c_188,c_58,c_188,c_188,c_188,c_188,c_4158])).

tff(c_171,plain,
    ( k2_relat_1(k2_funct_1('#skF_6')) = k1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_8])).

tff(c_184,plain,(
    k2_relat_1(k2_funct_1('#skF_6')) = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_171])).

tff(c_674,plain,(
    ! [A_92,C_93] :
      ( r2_hidden('#skF_4'(A_92,k2_relat_1(A_92),C_93),k1_relat_1(A_92))
      | ~ r2_hidden(C_93,k2_relat_1(A_92))
      | ~ v1_funct_1(A_92)
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3588,plain,(
    ! [A_172,C_173] :
      ( r2_hidden('#skF_4'(k4_relat_1(A_172),k2_relat_1(k4_relat_1(A_172)),C_173),k2_relat_1(A_172))
      | ~ r2_hidden(C_173,k2_relat_1(k4_relat_1(A_172)))
      | ~ v1_funct_1(k4_relat_1(A_172))
      | ~ v1_relat_1(k4_relat_1(A_172))
      | ~ v1_relat_1(A_172) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_674])).

tff(c_3615,plain,(
    ! [C_173] :
      ( r2_hidden('#skF_4'(k4_relat_1(k2_funct_1('#skF_6')),k2_relat_1(k4_relat_1(k2_funct_1('#skF_6'))),C_173),k1_relat_1('#skF_6'))
      | ~ r2_hidden(C_173,k2_relat_1(k4_relat_1(k2_funct_1('#skF_6'))))
      | ~ v1_funct_1(k4_relat_1(k2_funct_1('#skF_6')))
      | ~ v1_relat_1(k4_relat_1(k2_funct_1('#skF_6')))
      | ~ v1_relat_1(k2_funct_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_3588])).

tff(c_3652,plain,(
    ! [C_173] :
      ( r2_hidden('#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_173),k1_relat_1('#skF_6'))
      | ~ r2_hidden(C_173,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_60,c_188,c_58,c_188,c_188,c_188,c_188,c_3615])).

tff(c_4205,plain,(
    ! [C_182] :
      ( k1_funct_1('#skF_6','#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_182)) = C_182
      | ~ r2_hidden(C_182,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_60,c_188,c_58,c_188,c_188,c_188,c_188,c_4158])).

tff(c_38,plain,(
    ! [A_50] :
      ( v1_funct_1(k2_funct_1(A_50))
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_337,plain,(
    ! [A_78,D_79] :
      ( r2_hidden(k1_funct_1(A_78,D_79),k2_relat_1(A_78))
      | ~ r2_hidden(D_79,k1_relat_1(A_78))
      | ~ v1_funct_1(A_78)
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_340,plain,(
    ! [D_79] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),D_79),k1_relat_1('#skF_6'))
      | ~ r2_hidden(D_79,k1_relat_1(k2_funct_1('#skF_6')))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_337])).

tff(c_348,plain,(
    ! [D_79] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),D_79),k1_relat_1('#skF_6'))
      | ~ r2_hidden(D_79,k2_relat_1('#skF_6'))
      | ~ v1_funct_1(k2_funct_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_186,c_340])).

tff(c_595,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_348])).

tff(c_599,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_595])).

tff(c_603,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_599])).

tff(c_605,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_348])).

tff(c_6,plain,(
    ! [A_3,B_5] :
      ( k10_relat_1(A_3,k1_relat_1(B_5)) = k1_relat_1(k5_relat_1(A_3,B_5))
      | ~ v1_relat_1(B_5)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_129,plain,(
    ! [A_68] :
      ( k5_relat_1(A_68,k6_relat_1(k2_relat_1(A_68))) = A_68
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_461,plain,(
    ! [A_84] :
      ( k5_relat_1(k4_relat_1(A_84),k6_relat_1(k1_relat_1(A_84))) = k4_relat_1(A_84)
      | ~ v1_relat_1(k4_relat_1(A_84))
      | ~ v1_relat_1(A_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_129])).

tff(c_1637,plain,(
    ! [A_125] :
      ( k5_relat_1(A_125,k6_relat_1(k1_relat_1(k4_relat_1(A_125)))) = k4_relat_1(k4_relat_1(A_125))
      | ~ v1_relat_1(k4_relat_1(k4_relat_1(A_125)))
      | ~ v1_relat_1(k4_relat_1(A_125))
      | ~ v1_relat_1(A_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_461])).

tff(c_2006,plain,(
    ! [A_144] :
      ( k5_relat_1(A_144,k6_relat_1(k2_relat_1(A_144))) = k4_relat_1(k4_relat_1(A_144))
      | ~ v1_relat_1(k4_relat_1(k4_relat_1(A_144)))
      | ~ v1_relat_1(k4_relat_1(A_144))
      | ~ v1_relat_1(A_144)
      | ~ v1_relat_1(A_144) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1637])).

tff(c_2031,plain,(
    ! [A_145] :
      ( k5_relat_1(A_145,k6_relat_1(k2_relat_1(A_145))) = k4_relat_1(k4_relat_1(A_145))
      | ~ v1_relat_1(A_145)
      | ~ v1_relat_1(k4_relat_1(A_145)) ) ),
    inference(resolution,[status(thm)],[c_2,c_2006])).

tff(c_42,plain,(
    ! [A_51] : v1_relat_1(k6_relat_1(A_51)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_12,plain,(
    ! [A_7] : k1_relat_1(k6_relat_1(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_230,plain,(
    ! [A_71,B_72] :
      ( k10_relat_1(A_71,k1_relat_1(B_72)) = k1_relat_1(k5_relat_1(A_71,B_72))
      | ~ v1_relat_1(B_72)
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_245,plain,(
    ! [A_71,A_7] :
      ( k1_relat_1(k5_relat_1(A_71,k6_relat_1(A_7))) = k10_relat_1(A_71,A_7)
      | ~ v1_relat_1(k6_relat_1(A_7))
      | ~ v1_relat_1(A_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_230])).

tff(c_251,plain,(
    ! [A_71,A_7] :
      ( k1_relat_1(k5_relat_1(A_71,k6_relat_1(A_7))) = k10_relat_1(A_71,A_7)
      | ~ v1_relat_1(A_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_245])).

tff(c_2077,plain,(
    ! [A_146] :
      ( k1_relat_1(k4_relat_1(k4_relat_1(A_146))) = k10_relat_1(A_146,k2_relat_1(A_146))
      | ~ v1_relat_1(A_146)
      | ~ v1_relat_1(A_146)
      | ~ v1_relat_1(k4_relat_1(A_146)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2031,c_251])).

tff(c_2229,plain,(
    ! [A_148] :
      ( k10_relat_1(A_148,k2_relat_1(A_148)) = k2_relat_1(k4_relat_1(A_148))
      | ~ v1_relat_1(k4_relat_1(A_148))
      | ~ v1_relat_1(A_148)
      | ~ v1_relat_1(A_148)
      | ~ v1_relat_1(k4_relat_1(A_148)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2077,c_10])).

tff(c_2257,plain,(
    ! [A_149] :
      ( k10_relat_1(A_149,k2_relat_1(A_149)) = k2_relat_1(k4_relat_1(A_149))
      | ~ v1_relat_1(k4_relat_1(A_149))
      | ~ v1_relat_1(A_149) ) ),
    inference(resolution,[status(thm)],[c_2,c_2229])).

tff(c_2285,plain,(
    ! [A_150] :
      ( k10_relat_1(A_150,k2_relat_1(A_150)) = k2_relat_1(k4_relat_1(A_150))
      | ~ v1_relat_1(A_150) ) ),
    inference(resolution,[status(thm)],[c_2,c_2257])).

tff(c_2339,plain,(
    ! [A_151] :
      ( k10_relat_1(k4_relat_1(A_151),k1_relat_1(A_151)) = k2_relat_1(k4_relat_1(k4_relat_1(A_151)))
      | ~ v1_relat_1(k4_relat_1(A_151))
      | ~ v1_relat_1(A_151) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_2285])).

tff(c_2997,plain,(
    ! [B_164] :
      ( k2_relat_1(k4_relat_1(k4_relat_1(B_164))) = k1_relat_1(k5_relat_1(k4_relat_1(B_164),B_164))
      | ~ v1_relat_1(k4_relat_1(B_164))
      | ~ v1_relat_1(B_164)
      | ~ v1_relat_1(B_164)
      | ~ v1_relat_1(k4_relat_1(B_164)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_2339])).

tff(c_3130,plain,
    ( k2_relat_1(k4_relat_1(k4_relat_1(k2_funct_1('#skF_6')))) = k1_relat_1(k5_relat_1('#skF_6',k2_funct_1('#skF_6')))
    | ~ v1_relat_1(k4_relat_1(k2_funct_1('#skF_6')))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k4_relat_1(k2_funct_1('#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_2997])).

tff(c_3168,plain,(
    k1_relat_1(k5_relat_1('#skF_6',k2_funct_1('#skF_6'))) = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_188,c_190,c_190,c_60,c_188,c_184,c_167,c_188,c_3130])).

tff(c_46,plain,(
    ! [C_55,B_53,A_52] :
      ( k1_funct_1(k5_relat_1(C_55,B_53),A_52) = k1_funct_1(B_53,k1_funct_1(C_55,A_52))
      | ~ r2_hidden(A_52,k1_relat_1(k5_relat_1(C_55,B_53)))
      | ~ v1_funct_1(C_55)
      | ~ v1_relat_1(C_55)
      | ~ v1_funct_1(B_53)
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_3290,plain,(
    ! [A_52] :
      ( k1_funct_1(k5_relat_1('#skF_6',k2_funct_1('#skF_6')),A_52) = k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6',A_52))
      | ~ r2_hidden(A_52,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3168,c_46])).

tff(c_3386,plain,(
    ! [A_169] :
      ( k1_funct_1(k5_relat_1('#skF_6',k2_funct_1('#skF_6')),A_169) = k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6',A_169))
      | ~ r2_hidden(A_169,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_605,c_60,c_58,c_3290])).

tff(c_48,plain,(
    ! [B_57,A_56] :
      ( k1_funct_1(k5_relat_1(B_57,k2_funct_1(B_57)),A_56) = A_56
      | ~ r2_hidden(A_56,k1_relat_1(B_57))
      | ~ v2_funct_1(B_57)
      | ~ v1_funct_1(B_57)
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_3400,plain,(
    ! [A_169] :
      ( k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6',A_169)) = A_169
      | ~ r2_hidden(A_169,k1_relat_1('#skF_6'))
      | ~ v2_funct_1('#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(A_169,k1_relat_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3386,c_48])).

tff(c_3430,plain,(
    ! [A_169] :
      ( k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6',A_169)) = A_169
      | ~ r2_hidden(A_169,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_3400])).

tff(c_4251,plain,(
    ! [C_183] :
      ( k1_funct_1(k2_funct_1('#skF_6'),C_183) = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_183)
      | ~ r2_hidden('#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_183),k1_relat_1('#skF_6'))
      | ~ r2_hidden(C_183,k2_relat_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4205,c_3430])).

tff(c_4263,plain,(
    ! [C_184] :
      ( k1_funct_1(k2_funct_1('#skF_6'),C_184) = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),C_184)
      | ~ r2_hidden(C_184,k2_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_3652,c_4251])).

tff(c_4340,plain,(
    k1_funct_1(k2_funct_1('#skF_6'),'#skF_5') = '#skF_4'('#skF_6',k2_relat_1('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_4263])).

tff(c_52,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),'#skF_5') != '#skF_5'
    | k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_82,plain,(
    k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_4341,plain,(
    k1_funct_1('#skF_6','#skF_4'('#skF_6',k2_relat_1('#skF_6'),'#skF_5')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4340,c_82])).

tff(c_4371,plain,(
    ~ r2_hidden('#skF_5',k2_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4194,c_4341])).

tff(c_4378,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4371])).

tff(c_4380,plain,(
    k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_4457,plain,(
    ! [A_192] :
      ( k4_relat_1(A_192) = k2_funct_1(A_192)
      | ~ v2_funct_1(A_192)
      | ~ v1_funct_1(A_192)
      | ~ v1_relat_1(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4463,plain,
    ( k4_relat_1('#skF_6') = k2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_4457])).

tff(c_4469,plain,(
    k4_relat_1('#skF_6') = k2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_4463])).

tff(c_4482,plain,
    ( v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4469,c_2])).

tff(c_4492,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_4482])).

tff(c_4476,plain,
    ( k1_relat_1(k2_funct_1('#skF_6')) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4469,c_10])).

tff(c_4488,plain,(
    k1_relat_1(k2_funct_1('#skF_6')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_4476])).

tff(c_4473,plain,
    ( k2_relat_1(k2_funct_1('#skF_6')) = k1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4469,c_8])).

tff(c_4486,plain,(
    k2_relat_1(k2_funct_1('#skF_6')) = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_4473])).

tff(c_4585,plain,(
    ! [A_198,D_199] :
      ( r2_hidden(k1_funct_1(A_198,D_199),k2_relat_1(A_198))
      | ~ r2_hidden(D_199,k1_relat_1(A_198))
      | ~ v1_funct_1(A_198)
      | ~ v1_relat_1(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4588,plain,(
    ! [D_199] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),D_199),k1_relat_1('#skF_6'))
      | ~ r2_hidden(D_199,k1_relat_1(k2_funct_1('#skF_6')))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4486,c_4585])).

tff(c_4599,plain,(
    ! [D_199] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_6'),D_199),k1_relat_1('#skF_6'))
      | ~ r2_hidden(D_199,k2_relat_1('#skF_6'))
      | ~ v1_funct_1(k2_funct_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4492,c_4488,c_4588])).

tff(c_4811,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_4599])).

tff(c_4814,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_4811])).

tff(c_4818,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_4814])).

tff(c_4820,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_4599])).

tff(c_16,plain,(
    ! [A_8] :
      ( k5_relat_1(A_8,k6_relat_1(k2_relat_1(A_8))) = A_8
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4538,plain,
    ( k5_relat_1(k2_funct_1('#skF_6'),k6_relat_1(k1_relat_1('#skF_6'))) = k2_funct_1('#skF_6')
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4486,c_16])).

tff(c_4542,plain,(
    k5_relat_1(k2_funct_1('#skF_6'),k6_relat_1(k1_relat_1('#skF_6'))) = k2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4492,c_4538])).

tff(c_4494,plain,(
    ! [A_193,B_194] :
      ( k10_relat_1(A_193,k1_relat_1(B_194)) = k1_relat_1(k5_relat_1(A_193,B_194))
      | ~ v1_relat_1(B_194)
      | ~ v1_relat_1(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4506,plain,(
    ! [A_193,A_7] :
      ( k1_relat_1(k5_relat_1(A_193,k6_relat_1(A_7))) = k10_relat_1(A_193,A_7)
      | ~ v1_relat_1(k6_relat_1(A_7))
      | ~ v1_relat_1(A_193) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_4494])).

tff(c_4560,plain,(
    ! [A_196,A_197] :
      ( k1_relat_1(k5_relat_1(A_196,k6_relat_1(A_197))) = k10_relat_1(A_196,A_197)
      | ~ v1_relat_1(A_196) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_4506])).

tff(c_4572,plain,
    ( k10_relat_1(k2_funct_1('#skF_6'),k1_relat_1('#skF_6')) = k1_relat_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4542,c_4560])).

tff(c_4582,plain,(
    k10_relat_1(k2_funct_1('#skF_6'),k1_relat_1('#skF_6')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4492,c_4488,c_4572])).

tff(c_4628,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6')) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4582,c_6])).

tff(c_4635,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4492,c_60,c_4628])).

tff(c_6406,plain,(
    ! [C_269,B_270,A_271] :
      ( k1_funct_1(k5_relat_1(C_269,B_270),A_271) = k1_funct_1(B_270,k1_funct_1(C_269,A_271))
      | ~ r2_hidden(A_271,k1_relat_1(k5_relat_1(C_269,B_270)))
      | ~ v1_funct_1(C_269)
      | ~ v1_relat_1(C_269)
      | ~ v1_funct_1(B_270)
      | ~ v1_relat_1(B_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_6513,plain,(
    ! [A_271] :
      ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),A_271) = k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),A_271))
      | ~ r2_hidden(A_271,k2_relat_1('#skF_6'))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4635,c_6406])).

tff(c_6659,plain,(
    ! [A_273] :
      ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),A_273) = k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),A_273))
      | ~ r2_hidden(A_273,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_4492,c_4820,c_6513])).

tff(c_4379,plain,(
    k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'),'#skF_6'),'#skF_5') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_6681,plain,
    ( k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),'#skF_5')) != '#skF_5'
    | ~ r2_hidden('#skF_5',k2_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6659,c_4379])).

tff(c_6699,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4380,c_6681])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 15:07:42 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.28/2.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.28/2.49  
% 7.28/2.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.28/2.49  %$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 7.28/2.49  
% 7.28/2.49  %Foreground sorts:
% 7.28/2.49  
% 7.28/2.49  
% 7.28/2.49  %Background operators:
% 7.28/2.49  
% 7.28/2.49  
% 7.28/2.49  %Foreground operators:
% 7.28/2.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.28/2.49  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.28/2.49  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.28/2.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.28/2.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.28/2.49  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.28/2.49  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 7.28/2.49  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.28/2.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.28/2.49  tff('#skF_5', type, '#skF_5': $i).
% 7.28/2.49  tff('#skF_6', type, '#skF_6': $i).
% 7.28/2.49  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.28/2.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.28/2.49  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.28/2.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.28/2.49  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.28/2.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.28/2.49  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.28/2.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.28/2.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.28/2.49  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 7.28/2.49  
% 7.28/2.51  tff(f_127, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k2_relat_1(B))) => ((A = k1_funct_1(B, k1_funct_1(k2_funct_1(B), A))) & (A = k1_funct_1(k5_relat_1(k2_funct_1(B), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_funct_1)).
% 7.28/2.51  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 7.28/2.51  tff(f_29, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 7.28/2.51  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 7.28/2.51  tff(f_46, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 7.28/2.51  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 7.28/2.51  tff(f_85, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 7.28/2.51  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 7.28/2.51  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 7.28/2.51  tff(f_89, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 7.28/2.51  tff(f_50, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 7.28/2.51  tff(f_102, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) => (k1_funct_1(k5_relat_1(C, B), A) = k1_funct_1(B, k1_funct_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_funct_1)).
% 7.28/2.51  tff(f_114, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_funct_1)).
% 7.28/2.51  tff(c_54, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.28/2.51  tff(c_60, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.28/2.51  tff(c_58, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.28/2.51  tff(c_56, plain, (v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.28/2.51  tff(c_155, plain, (![A_70]: (k4_relat_1(A_70)=k2_funct_1(A_70) | ~v2_funct_1(A_70) | ~v1_funct_1(A_70) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.28/2.51  tff(c_161, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_155])).
% 7.28/2.51  tff(c_167, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_161])).
% 7.28/2.51  tff(c_2, plain, (![A_1]: (v1_relat_1(k4_relat_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.28/2.51  tff(c_180, plain, (v1_relat_1(k2_funct_1('#skF_6')) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_167, c_2])).
% 7.28/2.51  tff(c_190, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_180])).
% 7.28/2.51  tff(c_4, plain, (![A_2]: (k4_relat_1(k4_relat_1(A_2))=A_2 | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.28/2.51  tff(c_177, plain, (k4_relat_1(k2_funct_1('#skF_6'))='#skF_6' | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_167, c_4])).
% 7.28/2.51  tff(c_188, plain, (k4_relat_1(k2_funct_1('#skF_6'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_177])).
% 7.28/2.51  tff(c_10, plain, (![A_6]: (k1_relat_1(k4_relat_1(A_6))=k2_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.28/2.51  tff(c_174, plain, (k1_relat_1(k2_funct_1('#skF_6'))=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_167, c_10])).
% 7.28/2.51  tff(c_186, plain, (k1_relat_1(k2_funct_1('#skF_6'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_174])).
% 7.28/2.51  tff(c_8, plain, (![A_6]: (k2_relat_1(k4_relat_1(A_6))=k1_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.28/2.51  tff(c_536, plain, (![A_85, C_86]: (k1_funct_1(A_85, '#skF_4'(A_85, k2_relat_1(A_85), C_86))=C_86 | ~r2_hidden(C_86, k2_relat_1(A_85)) | ~v1_funct_1(A_85) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.28/2.51  tff(c_4051, plain, (![A_180, C_181]: (k1_funct_1(k4_relat_1(A_180), '#skF_4'(k4_relat_1(A_180), k1_relat_1(A_180), C_181))=C_181 | ~r2_hidden(C_181, k2_relat_1(k4_relat_1(A_180))) | ~v1_funct_1(k4_relat_1(A_180)) | ~v1_relat_1(k4_relat_1(A_180)) | ~v1_relat_1(A_180))), inference(superposition, [status(thm), theory('equality')], [c_8, c_536])).
% 7.28/2.51  tff(c_4158, plain, (![C_181]: (k1_funct_1(k4_relat_1(k2_funct_1('#skF_6')), '#skF_4'(k4_relat_1(k2_funct_1('#skF_6')), k2_relat_1('#skF_6'), C_181))=C_181 | ~r2_hidden(C_181, k2_relat_1(k4_relat_1(k2_funct_1('#skF_6')))) | ~v1_funct_1(k4_relat_1(k2_funct_1('#skF_6'))) | ~v1_relat_1(k4_relat_1(k2_funct_1('#skF_6'))) | ~v1_relat_1(k2_funct_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_186, c_4051])).
% 7.28/2.51  tff(c_4194, plain, (![C_181]: (k1_funct_1('#skF_6', '#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_181))=C_181 | ~r2_hidden(C_181, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_190, c_60, c_188, c_58, c_188, c_188, c_188, c_188, c_4158])).
% 7.28/2.51  tff(c_171, plain, (k2_relat_1(k2_funct_1('#skF_6'))=k1_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_167, c_8])).
% 7.28/2.51  tff(c_184, plain, (k2_relat_1(k2_funct_1('#skF_6'))=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_171])).
% 7.28/2.51  tff(c_674, plain, (![A_92, C_93]: (r2_hidden('#skF_4'(A_92, k2_relat_1(A_92), C_93), k1_relat_1(A_92)) | ~r2_hidden(C_93, k2_relat_1(A_92)) | ~v1_funct_1(A_92) | ~v1_relat_1(A_92))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.28/2.51  tff(c_3588, plain, (![A_172, C_173]: (r2_hidden('#skF_4'(k4_relat_1(A_172), k2_relat_1(k4_relat_1(A_172)), C_173), k2_relat_1(A_172)) | ~r2_hidden(C_173, k2_relat_1(k4_relat_1(A_172))) | ~v1_funct_1(k4_relat_1(A_172)) | ~v1_relat_1(k4_relat_1(A_172)) | ~v1_relat_1(A_172))), inference(superposition, [status(thm), theory('equality')], [c_10, c_674])).
% 7.28/2.51  tff(c_3615, plain, (![C_173]: (r2_hidden('#skF_4'(k4_relat_1(k2_funct_1('#skF_6')), k2_relat_1(k4_relat_1(k2_funct_1('#skF_6'))), C_173), k1_relat_1('#skF_6')) | ~r2_hidden(C_173, k2_relat_1(k4_relat_1(k2_funct_1('#skF_6')))) | ~v1_funct_1(k4_relat_1(k2_funct_1('#skF_6'))) | ~v1_relat_1(k4_relat_1(k2_funct_1('#skF_6'))) | ~v1_relat_1(k2_funct_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_184, c_3588])).
% 7.28/2.51  tff(c_3652, plain, (![C_173]: (r2_hidden('#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_173), k1_relat_1('#skF_6')) | ~r2_hidden(C_173, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_190, c_60, c_188, c_58, c_188, c_188, c_188, c_188, c_3615])).
% 7.28/2.51  tff(c_4205, plain, (![C_182]: (k1_funct_1('#skF_6', '#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_182))=C_182 | ~r2_hidden(C_182, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_190, c_60, c_188, c_58, c_188, c_188, c_188, c_188, c_4158])).
% 7.28/2.51  tff(c_38, plain, (![A_50]: (v1_funct_1(k2_funct_1(A_50)) | ~v1_funct_1(A_50) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.28/2.51  tff(c_337, plain, (![A_78, D_79]: (r2_hidden(k1_funct_1(A_78, D_79), k2_relat_1(A_78)) | ~r2_hidden(D_79, k1_relat_1(A_78)) | ~v1_funct_1(A_78) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.28/2.51  tff(c_340, plain, (![D_79]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), D_79), k1_relat_1('#skF_6')) | ~r2_hidden(D_79, k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_184, c_337])).
% 7.28/2.51  tff(c_348, plain, (![D_79]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), D_79), k1_relat_1('#skF_6')) | ~r2_hidden(D_79, k2_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_190, c_186, c_340])).
% 7.28/2.51  tff(c_595, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_348])).
% 7.28/2.51  tff(c_599, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_38, c_595])).
% 7.28/2.51  tff(c_603, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_599])).
% 7.28/2.51  tff(c_605, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_348])).
% 7.28/2.51  tff(c_6, plain, (![A_3, B_5]: (k10_relat_1(A_3, k1_relat_1(B_5))=k1_relat_1(k5_relat_1(A_3, B_5)) | ~v1_relat_1(B_5) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.28/2.51  tff(c_129, plain, (![A_68]: (k5_relat_1(A_68, k6_relat_1(k2_relat_1(A_68)))=A_68 | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.28/2.51  tff(c_461, plain, (![A_84]: (k5_relat_1(k4_relat_1(A_84), k6_relat_1(k1_relat_1(A_84)))=k4_relat_1(A_84) | ~v1_relat_1(k4_relat_1(A_84)) | ~v1_relat_1(A_84))), inference(superposition, [status(thm), theory('equality')], [c_8, c_129])).
% 7.28/2.51  tff(c_1637, plain, (![A_125]: (k5_relat_1(A_125, k6_relat_1(k1_relat_1(k4_relat_1(A_125))))=k4_relat_1(k4_relat_1(A_125)) | ~v1_relat_1(k4_relat_1(k4_relat_1(A_125))) | ~v1_relat_1(k4_relat_1(A_125)) | ~v1_relat_1(A_125))), inference(superposition, [status(thm), theory('equality')], [c_4, c_461])).
% 7.28/2.51  tff(c_2006, plain, (![A_144]: (k5_relat_1(A_144, k6_relat_1(k2_relat_1(A_144)))=k4_relat_1(k4_relat_1(A_144)) | ~v1_relat_1(k4_relat_1(k4_relat_1(A_144))) | ~v1_relat_1(k4_relat_1(A_144)) | ~v1_relat_1(A_144) | ~v1_relat_1(A_144))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1637])).
% 7.28/2.51  tff(c_2031, plain, (![A_145]: (k5_relat_1(A_145, k6_relat_1(k2_relat_1(A_145)))=k4_relat_1(k4_relat_1(A_145)) | ~v1_relat_1(A_145) | ~v1_relat_1(k4_relat_1(A_145)))), inference(resolution, [status(thm)], [c_2, c_2006])).
% 7.28/2.51  tff(c_42, plain, (![A_51]: (v1_relat_1(k6_relat_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.28/2.51  tff(c_12, plain, (![A_7]: (k1_relat_1(k6_relat_1(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.28/2.51  tff(c_230, plain, (![A_71, B_72]: (k10_relat_1(A_71, k1_relat_1(B_72))=k1_relat_1(k5_relat_1(A_71, B_72)) | ~v1_relat_1(B_72) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.28/2.51  tff(c_245, plain, (![A_71, A_7]: (k1_relat_1(k5_relat_1(A_71, k6_relat_1(A_7)))=k10_relat_1(A_71, A_7) | ~v1_relat_1(k6_relat_1(A_7)) | ~v1_relat_1(A_71))), inference(superposition, [status(thm), theory('equality')], [c_12, c_230])).
% 7.28/2.51  tff(c_251, plain, (![A_71, A_7]: (k1_relat_1(k5_relat_1(A_71, k6_relat_1(A_7)))=k10_relat_1(A_71, A_7) | ~v1_relat_1(A_71))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_245])).
% 7.28/2.51  tff(c_2077, plain, (![A_146]: (k1_relat_1(k4_relat_1(k4_relat_1(A_146)))=k10_relat_1(A_146, k2_relat_1(A_146)) | ~v1_relat_1(A_146) | ~v1_relat_1(A_146) | ~v1_relat_1(k4_relat_1(A_146)))), inference(superposition, [status(thm), theory('equality')], [c_2031, c_251])).
% 7.28/2.51  tff(c_2229, plain, (![A_148]: (k10_relat_1(A_148, k2_relat_1(A_148))=k2_relat_1(k4_relat_1(A_148)) | ~v1_relat_1(k4_relat_1(A_148)) | ~v1_relat_1(A_148) | ~v1_relat_1(A_148) | ~v1_relat_1(k4_relat_1(A_148)))), inference(superposition, [status(thm), theory('equality')], [c_2077, c_10])).
% 7.28/2.51  tff(c_2257, plain, (![A_149]: (k10_relat_1(A_149, k2_relat_1(A_149))=k2_relat_1(k4_relat_1(A_149)) | ~v1_relat_1(k4_relat_1(A_149)) | ~v1_relat_1(A_149))), inference(resolution, [status(thm)], [c_2, c_2229])).
% 7.28/2.51  tff(c_2285, plain, (![A_150]: (k10_relat_1(A_150, k2_relat_1(A_150))=k2_relat_1(k4_relat_1(A_150)) | ~v1_relat_1(A_150))), inference(resolution, [status(thm)], [c_2, c_2257])).
% 7.28/2.51  tff(c_2339, plain, (![A_151]: (k10_relat_1(k4_relat_1(A_151), k1_relat_1(A_151))=k2_relat_1(k4_relat_1(k4_relat_1(A_151))) | ~v1_relat_1(k4_relat_1(A_151)) | ~v1_relat_1(A_151))), inference(superposition, [status(thm), theory('equality')], [c_8, c_2285])).
% 7.28/2.51  tff(c_2997, plain, (![B_164]: (k2_relat_1(k4_relat_1(k4_relat_1(B_164)))=k1_relat_1(k5_relat_1(k4_relat_1(B_164), B_164)) | ~v1_relat_1(k4_relat_1(B_164)) | ~v1_relat_1(B_164) | ~v1_relat_1(B_164) | ~v1_relat_1(k4_relat_1(B_164)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_2339])).
% 7.28/2.51  tff(c_3130, plain, (k2_relat_1(k4_relat_1(k4_relat_1(k2_funct_1('#skF_6'))))=k1_relat_1(k5_relat_1('#skF_6', k2_funct_1('#skF_6'))) | ~v1_relat_1(k4_relat_1(k2_funct_1('#skF_6'))) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k4_relat_1(k2_funct_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_188, c_2997])).
% 7.28/2.51  tff(c_3168, plain, (k1_relat_1(k5_relat_1('#skF_6', k2_funct_1('#skF_6')))=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_188, c_190, c_190, c_60, c_188, c_184, c_167, c_188, c_3130])).
% 7.28/2.51  tff(c_46, plain, (![C_55, B_53, A_52]: (k1_funct_1(k5_relat_1(C_55, B_53), A_52)=k1_funct_1(B_53, k1_funct_1(C_55, A_52)) | ~r2_hidden(A_52, k1_relat_1(k5_relat_1(C_55, B_53))) | ~v1_funct_1(C_55) | ~v1_relat_1(C_55) | ~v1_funct_1(B_53) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.28/2.51  tff(c_3290, plain, (![A_52]: (k1_funct_1(k5_relat_1('#skF_6', k2_funct_1('#skF_6')), A_52)=k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', A_52)) | ~r2_hidden(A_52, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_3168, c_46])).
% 7.28/2.51  tff(c_3386, plain, (![A_169]: (k1_funct_1(k5_relat_1('#skF_6', k2_funct_1('#skF_6')), A_169)=k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', A_169)) | ~r2_hidden(A_169, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_190, c_605, c_60, c_58, c_3290])).
% 7.28/2.51  tff(c_48, plain, (![B_57, A_56]: (k1_funct_1(k5_relat_1(B_57, k2_funct_1(B_57)), A_56)=A_56 | ~r2_hidden(A_56, k1_relat_1(B_57)) | ~v2_funct_1(B_57) | ~v1_funct_1(B_57) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.28/2.51  tff(c_3400, plain, (![A_169]: (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', A_169))=A_169 | ~r2_hidden(A_169, k1_relat_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~r2_hidden(A_169, k1_relat_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_3386, c_48])).
% 7.28/2.51  tff(c_3430, plain, (![A_169]: (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', A_169))=A_169 | ~r2_hidden(A_169, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_3400])).
% 7.28/2.51  tff(c_4251, plain, (![C_183]: (k1_funct_1(k2_funct_1('#skF_6'), C_183)='#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_183) | ~r2_hidden('#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_183), k1_relat_1('#skF_6')) | ~r2_hidden(C_183, k2_relat_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_4205, c_3430])).
% 7.28/2.51  tff(c_4263, plain, (![C_184]: (k1_funct_1(k2_funct_1('#skF_6'), C_184)='#skF_4'('#skF_6', k2_relat_1('#skF_6'), C_184) | ~r2_hidden(C_184, k2_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_3652, c_4251])).
% 7.28/2.51  tff(c_4340, plain, (k1_funct_1(k2_funct_1('#skF_6'), '#skF_5')='#skF_4'('#skF_6', k2_relat_1('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_54, c_4263])).
% 7.28/2.51  tff(c_52, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), '#skF_5')!='#skF_5' | k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.28/2.51  tff(c_82, plain, (k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_52])).
% 7.28/2.51  tff(c_4341, plain, (k1_funct_1('#skF_6', '#skF_4'('#skF_6', k2_relat_1('#skF_6'), '#skF_5'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4340, c_82])).
% 7.28/2.51  tff(c_4371, plain, (~r2_hidden('#skF_5', k2_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_4194, c_4341])).
% 7.28/2.51  tff(c_4378, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_4371])).
% 7.28/2.51  tff(c_4380, plain, (k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_52])).
% 7.28/2.51  tff(c_4457, plain, (![A_192]: (k4_relat_1(A_192)=k2_funct_1(A_192) | ~v2_funct_1(A_192) | ~v1_funct_1(A_192) | ~v1_relat_1(A_192))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.28/2.51  tff(c_4463, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_56, c_4457])).
% 7.28/2.51  tff(c_4469, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_4463])).
% 7.28/2.51  tff(c_4482, plain, (v1_relat_1(k2_funct_1('#skF_6')) | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_4469, c_2])).
% 7.28/2.51  tff(c_4492, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_4482])).
% 7.28/2.51  tff(c_4476, plain, (k1_relat_1(k2_funct_1('#skF_6'))=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_4469, c_10])).
% 7.28/2.51  tff(c_4488, plain, (k1_relat_1(k2_funct_1('#skF_6'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_4476])).
% 7.28/2.51  tff(c_4473, plain, (k2_relat_1(k2_funct_1('#skF_6'))=k1_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_4469, c_8])).
% 7.28/2.51  tff(c_4486, plain, (k2_relat_1(k2_funct_1('#skF_6'))=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_4473])).
% 7.28/2.51  tff(c_4585, plain, (![A_198, D_199]: (r2_hidden(k1_funct_1(A_198, D_199), k2_relat_1(A_198)) | ~r2_hidden(D_199, k1_relat_1(A_198)) | ~v1_funct_1(A_198) | ~v1_relat_1(A_198))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.28/2.51  tff(c_4588, plain, (![D_199]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), D_199), k1_relat_1('#skF_6')) | ~r2_hidden(D_199, k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_4486, c_4585])).
% 7.28/2.51  tff(c_4599, plain, (![D_199]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_6'), D_199), k1_relat_1('#skF_6')) | ~r2_hidden(D_199, k2_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_4492, c_4488, c_4588])).
% 7.28/2.51  tff(c_4811, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_4599])).
% 7.28/2.51  tff(c_4814, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_38, c_4811])).
% 7.28/2.51  tff(c_4818, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_4814])).
% 7.28/2.51  tff(c_4820, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_4599])).
% 7.28/2.51  tff(c_16, plain, (![A_8]: (k5_relat_1(A_8, k6_relat_1(k2_relat_1(A_8)))=A_8 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.28/2.51  tff(c_4538, plain, (k5_relat_1(k2_funct_1('#skF_6'), k6_relat_1(k1_relat_1('#skF_6')))=k2_funct_1('#skF_6') | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_4486, c_16])).
% 7.28/2.51  tff(c_4542, plain, (k5_relat_1(k2_funct_1('#skF_6'), k6_relat_1(k1_relat_1('#skF_6')))=k2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4492, c_4538])).
% 7.28/2.51  tff(c_4494, plain, (![A_193, B_194]: (k10_relat_1(A_193, k1_relat_1(B_194))=k1_relat_1(k5_relat_1(A_193, B_194)) | ~v1_relat_1(B_194) | ~v1_relat_1(A_193))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.28/2.51  tff(c_4506, plain, (![A_193, A_7]: (k1_relat_1(k5_relat_1(A_193, k6_relat_1(A_7)))=k10_relat_1(A_193, A_7) | ~v1_relat_1(k6_relat_1(A_7)) | ~v1_relat_1(A_193))), inference(superposition, [status(thm), theory('equality')], [c_12, c_4494])).
% 7.28/2.51  tff(c_4560, plain, (![A_196, A_197]: (k1_relat_1(k5_relat_1(A_196, k6_relat_1(A_197)))=k10_relat_1(A_196, A_197) | ~v1_relat_1(A_196))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_4506])).
% 7.28/2.51  tff(c_4572, plain, (k10_relat_1(k2_funct_1('#skF_6'), k1_relat_1('#skF_6'))=k1_relat_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_4542, c_4560])).
% 7.28/2.51  tff(c_4582, plain, (k10_relat_1(k2_funct_1('#skF_6'), k1_relat_1('#skF_6'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4492, c_4488, c_4572])).
% 7.28/2.51  tff(c_4628, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'))=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_4582, c_6])).
% 7.28/2.51  tff(c_4635, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4492, c_60, c_4628])).
% 7.28/2.51  tff(c_6406, plain, (![C_269, B_270, A_271]: (k1_funct_1(k5_relat_1(C_269, B_270), A_271)=k1_funct_1(B_270, k1_funct_1(C_269, A_271)) | ~r2_hidden(A_271, k1_relat_1(k5_relat_1(C_269, B_270))) | ~v1_funct_1(C_269) | ~v1_relat_1(C_269) | ~v1_funct_1(B_270) | ~v1_relat_1(B_270))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.28/2.51  tff(c_6513, plain, (![A_271]: (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), A_271)=k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), A_271)) | ~r2_hidden(A_271, k2_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_4635, c_6406])).
% 7.28/2.51  tff(c_6659, plain, (![A_273]: (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), A_273)=k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), A_273)) | ~r2_hidden(A_273, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_4492, c_4820, c_6513])).
% 7.28/2.51  tff(c_4379, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_6'), '#skF_6'), '#skF_5')!='#skF_5'), inference(splitRight, [status(thm)], [c_52])).
% 7.28/2.51  tff(c_6681, plain, (k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'))!='#skF_5' | ~r2_hidden('#skF_5', k2_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_6659, c_4379])).
% 7.28/2.51  tff(c_6699, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_4380, c_6681])).
% 7.28/2.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.28/2.51  
% 7.28/2.51  Inference rules
% 7.28/2.51  ----------------------
% 7.28/2.51  #Ref     : 0
% 7.28/2.51  #Sup     : 1609
% 7.28/2.51  #Fact    : 0
% 7.28/2.51  #Define  : 0
% 7.28/2.51  #Split   : 17
% 7.28/2.51  #Chain   : 0
% 7.28/2.51  #Close   : 0
% 7.28/2.51  
% 7.28/2.51  Ordering : KBO
% 7.28/2.51  
% 7.28/2.51  Simplification rules
% 7.28/2.51  ----------------------
% 7.28/2.51  #Subsume      : 183
% 7.28/2.51  #Demod        : 2352
% 7.28/2.51  #Tautology    : 605
% 7.28/2.51  #SimpNegUnit  : 0
% 7.28/2.51  #BackRed      : 3
% 7.28/2.51  
% 7.28/2.51  #Partial instantiations: 0
% 7.28/2.51  #Strategies tried      : 1
% 7.28/2.51  
% 7.28/2.51  Timing (in seconds)
% 7.28/2.51  ----------------------
% 7.28/2.52  Preprocessing        : 0.34
% 7.28/2.52  Parsing              : 0.17
% 7.28/2.52  CNF conversion       : 0.03
% 7.28/2.52  Main loop            : 1.38
% 7.28/2.52  Inferencing          : 0.46
% 7.28/2.52  Reduction            : 0.54
% 7.28/2.52  Demodulation         : 0.42
% 7.28/2.52  BG Simplification    : 0.07
% 7.28/2.52  Subsumption          : 0.23
% 7.28/2.52  Abstraction          : 0.08
% 7.28/2.52  MUC search           : 0.00
% 7.28/2.52  Cooper               : 0.00
% 7.28/2.52  Total                : 1.76
% 7.28/2.52  Index Insertion      : 0.00
% 7.28/2.52  Index Deletion       : 0.00
% 7.28/2.52  Index Matching       : 0.00
% 7.28/2.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
