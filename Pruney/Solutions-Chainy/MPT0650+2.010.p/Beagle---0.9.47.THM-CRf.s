%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:45 EST 2020

% Result     : Theorem 8.17s
% Output     : CNFRefutation 8.46s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 602 expanded)
%              Number of leaves         :   33 ( 227 expanded)
%              Depth                    :   23
%              Number of atoms          :  267 (1714 expanded)
%              Number of equality atoms :   75 ( 561 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_128,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( v2_funct_1(B)
            & r2_hidden(A,k2_relat_1(B)) )
         => ( A = k1_funct_1(B,k1_funct_1(k2_funct_1(B),A))
            & A = k1_funct_1(k5_relat_1(k2_funct_1(B),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).

tff(f_57,axiom,(
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

tff(f_115,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k1_relat_1(B)) )
       => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
          & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(c_54,plain,(
    r2_hidden('#skF_6',k2_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_60,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_58,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_12,plain,(
    ! [A_6,C_42] :
      ( k1_funct_1(A_6,'#skF_4'(A_6,k2_relat_1(A_6),C_42)) = C_42
      | ~ r2_hidden(C_42,k2_relat_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_14,plain,(
    ! [A_6,C_42] :
      ( r2_hidden('#skF_4'(A_6,k2_relat_1(A_6),C_42),k1_relat_1(A_6))
      | ~ r2_hidden(C_42,k2_relat_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10,plain,(
    ! [A_6,D_45] :
      ( r2_hidden(k1_funct_1(A_6,D_45),k2_relat_1(A_6))
      | ~ r2_hidden(D_45,k1_relat_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_56,plain,(
    v2_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_50,plain,(
    ! [B_59,A_58] :
      ( k1_funct_1(k2_funct_1(B_59),k1_funct_1(B_59,A_58)) = A_58
      | ~ r2_hidden(A_58,k1_relat_1(B_59))
      | ~ v2_funct_1(B_59)
      | ~ v1_funct_1(B_59)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_34,plain,(
    ! [A_48] : v1_relat_1(k6_relat_1(A_48)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_36,plain,(
    ! [A_48] : v1_funct_1(k6_relat_1(A_48)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_32,plain,(
    ! [A_47] :
      ( v1_relat_1(k2_funct_1(A_47))
      | ~ v1_funct_1(A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_122,plain,(
    ! [A_70] :
      ( k4_relat_1(A_70) = k2_funct_1(A_70)
      | ~ v2_funct_1(A_70)
      | ~ v1_funct_1(A_70)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_125,plain,
    ( k4_relat_1('#skF_7') = k2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_122])).

tff(c_128,plain,(
    k4_relat_1('#skF_7') = k2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_125])).

tff(c_4,plain,(
    ! [A_4] :
      ( k2_relat_1(k4_relat_1(A_4)) = k1_relat_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_135,plain,
    ( k2_relat_1(k2_funct_1('#skF_7')) = k1_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_4])).

tff(c_141,plain,(
    k2_relat_1(k2_funct_1('#skF_7')) = k1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_135])).

tff(c_8,plain,(
    ! [A_5] :
      ( k5_relat_1(A_5,k6_relat_1(k2_relat_1(A_5))) = A_5
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_150,plain,
    ( k5_relat_1(k2_funct_1('#skF_7'),k6_relat_1(k1_relat_1('#skF_7'))) = k2_funct_1('#skF_7')
    | ~ v1_relat_1(k2_funct_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_8])).

tff(c_154,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_157,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_154])).

tff(c_161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_157])).

tff(c_163,plain,(
    v1_relat_1(k2_funct_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_30,plain,(
    ! [A_47] :
      ( v1_funct_1(k2_funct_1(A_47))
      | ~ v1_funct_1(A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6,plain,(
    ! [A_4] :
      ( k1_relat_1(k4_relat_1(A_4)) = k2_relat_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_132,plain,
    ( k1_relat_1(k2_funct_1('#skF_7')) = k2_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_6])).

tff(c_139,plain,(
    k1_relat_1(k2_funct_1('#skF_7')) = k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_132])).

tff(c_210,plain,(
    ! [A_75,D_76] :
      ( r2_hidden(k1_funct_1(A_75,D_76),k2_relat_1(A_75))
      | ~ r2_hidden(D_76,k1_relat_1(A_75))
      | ~ v1_funct_1(A_75)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_213,plain,(
    ! [D_76] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_7'),D_76),k1_relat_1('#skF_7'))
      | ~ r2_hidden(D_76,k1_relat_1(k2_funct_1('#skF_7')))
      | ~ v1_funct_1(k2_funct_1('#skF_7'))
      | ~ v1_relat_1(k2_funct_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_210])).

tff(c_221,plain,(
    ! [D_76] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_7'),D_76),k1_relat_1('#skF_7'))
      | ~ r2_hidden(D_76,k2_relat_1('#skF_7'))
      | ~ v1_funct_1(k2_funct_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_139,c_213])).

tff(c_327,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_377,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_30,c_327])).

tff(c_381,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_377])).

tff(c_383,plain,(
    v1_funct_1(k2_funct_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_162,plain,(
    k5_relat_1(k2_funct_1('#skF_7'),k6_relat_1(k1_relat_1('#skF_7'))) = k2_funct_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_1902,plain,(
    ! [C_174,B_175,A_176] :
      ( k1_funct_1(k5_relat_1(C_174,B_175),A_176) = k1_funct_1(B_175,k1_funct_1(C_174,A_176))
      | ~ r2_hidden(A_176,k1_relat_1(k5_relat_1(C_174,B_175)))
      | ~ v1_funct_1(C_174)
      | ~ v1_relat_1(C_174)
      | ~ v1_funct_1(B_175)
      | ~ v1_relat_1(B_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2002,plain,(
    ! [A_176] :
      ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_7'),k6_relat_1(k1_relat_1('#skF_7'))),A_176) = k1_funct_1(k6_relat_1(k1_relat_1('#skF_7')),k1_funct_1(k2_funct_1('#skF_7'),A_176))
      | ~ r2_hidden(A_176,k1_relat_1(k2_funct_1('#skF_7')))
      | ~ v1_funct_1(k2_funct_1('#skF_7'))
      | ~ v1_relat_1(k2_funct_1('#skF_7'))
      | ~ v1_funct_1(k6_relat_1(k1_relat_1('#skF_7')))
      | ~ v1_relat_1(k6_relat_1(k1_relat_1('#skF_7'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_1902])).

tff(c_2129,plain,(
    ! [A_181] :
      ( k1_funct_1(k6_relat_1(k1_relat_1('#skF_7')),k1_funct_1(k2_funct_1('#skF_7'),A_181)) = k1_funct_1(k2_funct_1('#skF_7'),A_181)
      | ~ r2_hidden(A_181,k2_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36,c_163,c_383,c_139,c_162,c_2002])).

tff(c_2160,plain,(
    ! [A_58] :
      ( k1_funct_1(k6_relat_1(k1_relat_1('#skF_7')),A_58) = k1_funct_1(k2_funct_1('#skF_7'),k1_funct_1('#skF_7',A_58))
      | ~ r2_hidden(k1_funct_1('#skF_7',A_58),k2_relat_1('#skF_7'))
      | ~ r2_hidden(A_58,k1_relat_1('#skF_7'))
      | ~ v2_funct_1('#skF_7')
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_2129])).

tff(c_3928,plain,(
    ! [A_227] :
      ( k1_funct_1(k6_relat_1(k1_relat_1('#skF_7')),A_227) = k1_funct_1(k2_funct_1('#skF_7'),k1_funct_1('#skF_7',A_227))
      | ~ r2_hidden(k1_funct_1('#skF_7',A_227),k2_relat_1('#skF_7'))
      | ~ r2_hidden(A_227,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_2160])).

tff(c_3938,plain,(
    ! [D_45] :
      ( k1_funct_1(k6_relat_1(k1_relat_1('#skF_7')),D_45) = k1_funct_1(k2_funct_1('#skF_7'),k1_funct_1('#skF_7',D_45))
      | ~ r2_hidden(D_45,k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_10,c_3928])).

tff(c_3944,plain,(
    ! [D_228] :
      ( k1_funct_1(k6_relat_1(k1_relat_1('#skF_7')),D_228) = k1_funct_1(k2_funct_1('#skF_7'),k1_funct_1('#skF_7',D_228))
      | ~ r2_hidden(D_228,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_3938])).

tff(c_44,plain,(
    ! [A_53,C_57] :
      ( k1_funct_1(k6_relat_1(A_53),C_57) = C_57
      | ~ r2_hidden(C_57,A_53)
      | ~ v1_funct_1(k6_relat_1(A_53))
      | ~ v1_relat_1(k6_relat_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_64,plain,(
    ! [A_53,C_57] :
      ( k1_funct_1(k6_relat_1(A_53),C_57) = C_57
      | ~ r2_hidden(C_57,A_53)
      | ~ v1_relat_1(k6_relat_1(A_53)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_44])).

tff(c_68,plain,(
    ! [A_53,C_57] :
      ( k1_funct_1(k6_relat_1(A_53),C_57) = C_57
      | ~ r2_hidden(C_57,A_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_64])).

tff(c_4123,plain,(
    ! [D_233] :
      ( k1_funct_1(k2_funct_1('#skF_7'),k1_funct_1('#skF_7',D_233)) = D_233
      | ~ r2_hidden(D_233,k1_relat_1('#skF_7'))
      | ~ r2_hidden(D_233,k1_relat_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3944,c_68])).

tff(c_4167,plain,(
    ! [C_42] :
      ( k1_funct_1(k2_funct_1('#skF_7'),C_42) = '#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_42)
      | ~ r2_hidden('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_42),k1_relat_1('#skF_7'))
      | ~ r2_hidden('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_42),k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_42,k2_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_4123])).

tff(c_5583,plain,(
    ! [C_255] :
      ( k1_funct_1(k2_funct_1('#skF_7'),C_255) = '#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_255)
      | ~ r2_hidden('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_255),k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_255,k2_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_4167])).

tff(c_5587,plain,(
    ! [C_42] :
      ( k1_funct_1(k2_funct_1('#skF_7'),C_42) = '#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_42)
      | ~ r2_hidden(C_42,k2_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_14,c_5583])).

tff(c_5666,plain,(
    ! [C_258] :
      ( k1_funct_1(k2_funct_1('#skF_7'),C_258) = '#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_258)
      | ~ r2_hidden(C_258,k2_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_5587])).

tff(c_5804,plain,(
    k1_funct_1(k2_funct_1('#skF_7'),'#skF_6') = '#skF_4'('#skF_7',k2_relat_1('#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_5666])).

tff(c_52,plain,
    ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_7'),'#skF_7'),'#skF_6') != '#skF_6'
    | k1_funct_1('#skF_7',k1_funct_1(k2_funct_1('#skF_7'),'#skF_6')) != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_90,plain,(
    k1_funct_1('#skF_7',k1_funct_1(k2_funct_1('#skF_7'),'#skF_6')) != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_5805,plain,(
    k1_funct_1('#skF_7','#skF_4'('#skF_7',k2_relat_1('#skF_7'),'#skF_6')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5804,c_90])).

tff(c_5845,plain,
    ( ~ r2_hidden('#skF_6',k2_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_5805])).

tff(c_5849,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_5845])).

tff(c_5851,plain,(
    k1_funct_1('#skF_7',k1_funct_1(k2_funct_1('#skF_7'),'#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_5887,plain,(
    ! [A_264] :
      ( k4_relat_1(A_264) = k2_funct_1(A_264)
      | ~ v2_funct_1(A_264)
      | ~ v1_funct_1(A_264)
      | ~ v1_relat_1(A_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_5890,plain,
    ( k4_relat_1('#skF_7') = k2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_5887])).

tff(c_5893,plain,(
    k4_relat_1('#skF_7') = k2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_5890])).

tff(c_5900,plain,
    ( k2_relat_1(k2_funct_1('#skF_7')) = k1_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_5893,c_4])).

tff(c_5906,plain,(
    k2_relat_1(k2_funct_1('#skF_7')) = k1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_5900])).

tff(c_5915,plain,
    ( k5_relat_1(k2_funct_1('#skF_7'),k6_relat_1(k1_relat_1('#skF_7'))) = k2_funct_1('#skF_7')
    | ~ v1_relat_1(k2_funct_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5906,c_8])).

tff(c_5919,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_5915])).

tff(c_5922,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_5919])).

tff(c_5926,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_5922])).

tff(c_5928,plain,(
    v1_relat_1(k2_funct_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_5915])).

tff(c_5897,plain,
    ( k1_relat_1(k2_funct_1('#skF_7')) = k2_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_5893,c_6])).

tff(c_5904,plain,(
    k1_relat_1(k2_funct_1('#skF_7')) = k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_5897])).

tff(c_5975,plain,(
    ! [A_269,D_270] :
      ( r2_hidden(k1_funct_1(A_269,D_270),k2_relat_1(A_269))
      | ~ r2_hidden(D_270,k1_relat_1(A_269))
      | ~ v1_funct_1(A_269)
      | ~ v1_relat_1(A_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_5978,plain,(
    ! [D_270] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_7'),D_270),k1_relat_1('#skF_7'))
      | ~ r2_hidden(D_270,k1_relat_1(k2_funct_1('#skF_7')))
      | ~ v1_funct_1(k2_funct_1('#skF_7'))
      | ~ v1_relat_1(k2_funct_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5906,c_5975])).

tff(c_5989,plain,(
    ! [D_270] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_7'),D_270),k1_relat_1('#skF_7'))
      | ~ r2_hidden(D_270,k2_relat_1('#skF_7'))
      | ~ v1_funct_1(k2_funct_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5928,c_5904,c_5978])).

tff(c_6097,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_5989])).

tff(c_6147,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_30,c_6097])).

tff(c_6151,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_6147])).

tff(c_6153,plain,(
    v1_funct_1(k2_funct_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_5989])).

tff(c_5927,plain,(
    k5_relat_1(k2_funct_1('#skF_7'),k6_relat_1(k1_relat_1('#skF_7'))) = k2_funct_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_5915])).

tff(c_46,plain,(
    ! [A_53] :
      ( k1_relat_1(k6_relat_1(A_53)) = A_53
      | ~ v1_funct_1(k6_relat_1(A_53))
      | ~ v1_relat_1(k6_relat_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_62,plain,(
    ! [A_53] :
      ( k1_relat_1(k6_relat_1(A_53)) = A_53
      | ~ v1_relat_1(k6_relat_1(A_53)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_46])).

tff(c_66,plain,(
    ! [A_53] : k1_relat_1(k6_relat_1(A_53)) = A_53 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_62])).

tff(c_5933,plain,(
    ! [A_265,B_266] :
      ( k10_relat_1(A_265,k1_relat_1(B_266)) = k1_relat_1(k5_relat_1(A_265,B_266))
      | ~ v1_relat_1(B_266)
      | ~ v1_relat_1(A_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5948,plain,(
    ! [A_265,A_53] :
      ( k1_relat_1(k5_relat_1(A_265,k6_relat_1(A_53))) = k10_relat_1(A_265,A_53)
      | ~ v1_relat_1(k6_relat_1(A_53))
      | ~ v1_relat_1(A_265) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_5933])).

tff(c_5955,plain,(
    ! [A_267,A_268] :
      ( k1_relat_1(k5_relat_1(A_267,k6_relat_1(A_268))) = k10_relat_1(A_267,A_268)
      | ~ v1_relat_1(A_267) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_5948])).

tff(c_5967,plain,
    ( k10_relat_1(k2_funct_1('#skF_7'),k1_relat_1('#skF_7')) = k1_relat_1(k2_funct_1('#skF_7'))
    | ~ v1_relat_1(k2_funct_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5927,c_5955])).

tff(c_5974,plain,(
    k10_relat_1(k2_funct_1('#skF_7'),k1_relat_1('#skF_7')) = k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5928,c_5904,c_5967])).

tff(c_2,plain,(
    ! [A_1,B_3] :
      ( k10_relat_1(A_1,k1_relat_1(B_3)) = k1_relat_1(k5_relat_1(A_1,B_3))
      | ~ v1_relat_1(B_3)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5997,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_7'),'#skF_7')) = k2_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_funct_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5974,c_2])).

tff(c_6004,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_7'),'#skF_7')) = k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5928,c_60,c_5997])).

tff(c_8251,plain,(
    ! [C_381,B_382,A_383] :
      ( k1_funct_1(k5_relat_1(C_381,B_382),A_383) = k1_funct_1(B_382,k1_funct_1(C_381,A_383))
      | ~ r2_hidden(A_383,k1_relat_1(k5_relat_1(C_381,B_382)))
      | ~ v1_funct_1(C_381)
      | ~ v1_relat_1(C_381)
      | ~ v1_funct_1(B_382)
      | ~ v1_relat_1(B_382) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_8337,plain,(
    ! [A_383] :
      ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_7'),'#skF_7'),A_383) = k1_funct_1('#skF_7',k1_funct_1(k2_funct_1('#skF_7'),A_383))
      | ~ r2_hidden(A_383,k2_relat_1('#skF_7'))
      | ~ v1_funct_1(k2_funct_1('#skF_7'))
      | ~ v1_relat_1(k2_funct_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6004,c_8251])).

tff(c_8438,plain,(
    ! [A_385] :
      ( k1_funct_1(k5_relat_1(k2_funct_1('#skF_7'),'#skF_7'),A_385) = k1_funct_1('#skF_7',k1_funct_1(k2_funct_1('#skF_7'),A_385))
      | ~ r2_hidden(A_385,k2_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_5928,c_6153,c_8337])).

tff(c_5850,plain,(
    k1_funct_1(k5_relat_1(k2_funct_1('#skF_7'),'#skF_7'),'#skF_6') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_8464,plain,
    ( k1_funct_1('#skF_7',k1_funct_1(k2_funct_1('#skF_7'),'#skF_6')) != '#skF_6'
    | ~ r2_hidden('#skF_6',k2_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8438,c_5850])).

tff(c_8483,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_5851,c_8464])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:06:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.17/2.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.17/2.75  
% 8.17/2.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.17/2.75  %$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5
% 8.17/2.75  
% 8.17/2.75  %Foreground sorts:
% 8.17/2.75  
% 8.17/2.75  
% 8.17/2.75  %Background operators:
% 8.17/2.75  
% 8.17/2.75  
% 8.17/2.75  %Foreground operators:
% 8.17/2.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.17/2.75  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.17/2.75  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.17/2.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.17/2.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.17/2.75  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.17/2.75  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 8.17/2.75  tff('#skF_7', type, '#skF_7': $i).
% 8.17/2.75  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.17/2.75  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.17/2.75  tff('#skF_6', type, '#skF_6': $i).
% 8.17/2.75  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.17/2.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.17/2.75  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 8.17/2.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.17/2.75  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.17/2.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.17/2.75  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.17/2.75  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.17/2.75  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 8.17/2.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.17/2.75  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 8.17/2.75  
% 8.46/2.78  tff(f_128, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k2_relat_1(B))) => ((A = k1_funct_1(B, k1_funct_1(k2_funct_1(B), A))) & (A = k1_funct_1(k5_relat_1(k2_funct_1(B), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_funct_1)).
% 8.46/2.78  tff(f_57, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 8.46/2.78  tff(f_115, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_funct_1)).
% 8.46/2.78  tff(f_77, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 8.46/2.78  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 8.46/2.78  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 8.46/2.78  tff(f_38, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 8.46/2.78  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 8.46/2.78  tff(f_90, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) => (k1_funct_1(k5_relat_1(C, B), A) = k1_funct_1(B, k1_funct_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_funct_1)).
% 8.46/2.78  tff(f_103, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 8.46/2.78  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 8.46/2.78  tff(c_54, plain, (r2_hidden('#skF_6', k2_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.46/2.78  tff(c_60, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.46/2.78  tff(c_58, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.46/2.78  tff(c_12, plain, (![A_6, C_42]: (k1_funct_1(A_6, '#skF_4'(A_6, k2_relat_1(A_6), C_42))=C_42 | ~r2_hidden(C_42, k2_relat_1(A_6)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.46/2.78  tff(c_14, plain, (![A_6, C_42]: (r2_hidden('#skF_4'(A_6, k2_relat_1(A_6), C_42), k1_relat_1(A_6)) | ~r2_hidden(C_42, k2_relat_1(A_6)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.46/2.78  tff(c_10, plain, (![A_6, D_45]: (r2_hidden(k1_funct_1(A_6, D_45), k2_relat_1(A_6)) | ~r2_hidden(D_45, k1_relat_1(A_6)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.46/2.78  tff(c_56, plain, (v2_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.46/2.78  tff(c_50, plain, (![B_59, A_58]: (k1_funct_1(k2_funct_1(B_59), k1_funct_1(B_59, A_58))=A_58 | ~r2_hidden(A_58, k1_relat_1(B_59)) | ~v2_funct_1(B_59) | ~v1_funct_1(B_59) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.46/2.78  tff(c_34, plain, (![A_48]: (v1_relat_1(k6_relat_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.46/2.78  tff(c_36, plain, (![A_48]: (v1_funct_1(k6_relat_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.46/2.78  tff(c_32, plain, (![A_47]: (v1_relat_1(k2_funct_1(A_47)) | ~v1_funct_1(A_47) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.46/2.78  tff(c_122, plain, (![A_70]: (k4_relat_1(A_70)=k2_funct_1(A_70) | ~v2_funct_1(A_70) | ~v1_funct_1(A_70) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.46/2.78  tff(c_125, plain, (k4_relat_1('#skF_7')=k2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_56, c_122])).
% 8.46/2.78  tff(c_128, plain, (k4_relat_1('#skF_7')=k2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_125])).
% 8.46/2.78  tff(c_4, plain, (![A_4]: (k2_relat_1(k4_relat_1(A_4))=k1_relat_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.46/2.78  tff(c_135, plain, (k2_relat_1(k2_funct_1('#skF_7'))=k1_relat_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_128, c_4])).
% 8.46/2.78  tff(c_141, plain, (k2_relat_1(k2_funct_1('#skF_7'))=k1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_135])).
% 8.46/2.78  tff(c_8, plain, (![A_5]: (k5_relat_1(A_5, k6_relat_1(k2_relat_1(A_5)))=A_5 | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.46/2.78  tff(c_150, plain, (k5_relat_1(k2_funct_1('#skF_7'), k6_relat_1(k1_relat_1('#skF_7')))=k2_funct_1('#skF_7') | ~v1_relat_1(k2_funct_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_141, c_8])).
% 8.46/2.78  tff(c_154, plain, (~v1_relat_1(k2_funct_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_150])).
% 8.46/2.78  tff(c_157, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_32, c_154])).
% 8.46/2.78  tff(c_161, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_157])).
% 8.46/2.78  tff(c_163, plain, (v1_relat_1(k2_funct_1('#skF_7'))), inference(splitRight, [status(thm)], [c_150])).
% 8.46/2.78  tff(c_30, plain, (![A_47]: (v1_funct_1(k2_funct_1(A_47)) | ~v1_funct_1(A_47) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.46/2.78  tff(c_6, plain, (![A_4]: (k1_relat_1(k4_relat_1(A_4))=k2_relat_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.46/2.78  tff(c_132, plain, (k1_relat_1(k2_funct_1('#skF_7'))=k2_relat_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_128, c_6])).
% 8.46/2.78  tff(c_139, plain, (k1_relat_1(k2_funct_1('#skF_7'))=k2_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_132])).
% 8.46/2.78  tff(c_210, plain, (![A_75, D_76]: (r2_hidden(k1_funct_1(A_75, D_76), k2_relat_1(A_75)) | ~r2_hidden(D_76, k1_relat_1(A_75)) | ~v1_funct_1(A_75) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.46/2.78  tff(c_213, plain, (![D_76]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_7'), D_76), k1_relat_1('#skF_7')) | ~r2_hidden(D_76, k1_relat_1(k2_funct_1('#skF_7'))) | ~v1_funct_1(k2_funct_1('#skF_7')) | ~v1_relat_1(k2_funct_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_141, c_210])).
% 8.46/2.78  tff(c_221, plain, (![D_76]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_7'), D_76), k1_relat_1('#skF_7')) | ~r2_hidden(D_76, k2_relat_1('#skF_7')) | ~v1_funct_1(k2_funct_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_139, c_213])).
% 8.46/2.78  tff(c_327, plain, (~v1_funct_1(k2_funct_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_221])).
% 8.46/2.78  tff(c_377, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_30, c_327])).
% 8.46/2.78  tff(c_381, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_377])).
% 8.46/2.78  tff(c_383, plain, (v1_funct_1(k2_funct_1('#skF_7'))), inference(splitRight, [status(thm)], [c_221])).
% 8.46/2.78  tff(c_162, plain, (k5_relat_1(k2_funct_1('#skF_7'), k6_relat_1(k1_relat_1('#skF_7')))=k2_funct_1('#skF_7')), inference(splitRight, [status(thm)], [c_150])).
% 8.46/2.78  tff(c_1902, plain, (![C_174, B_175, A_176]: (k1_funct_1(k5_relat_1(C_174, B_175), A_176)=k1_funct_1(B_175, k1_funct_1(C_174, A_176)) | ~r2_hidden(A_176, k1_relat_1(k5_relat_1(C_174, B_175))) | ~v1_funct_1(C_174) | ~v1_relat_1(C_174) | ~v1_funct_1(B_175) | ~v1_relat_1(B_175))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.46/2.78  tff(c_2002, plain, (![A_176]: (k1_funct_1(k5_relat_1(k2_funct_1('#skF_7'), k6_relat_1(k1_relat_1('#skF_7'))), A_176)=k1_funct_1(k6_relat_1(k1_relat_1('#skF_7')), k1_funct_1(k2_funct_1('#skF_7'), A_176)) | ~r2_hidden(A_176, k1_relat_1(k2_funct_1('#skF_7'))) | ~v1_funct_1(k2_funct_1('#skF_7')) | ~v1_relat_1(k2_funct_1('#skF_7')) | ~v1_funct_1(k6_relat_1(k1_relat_1('#skF_7'))) | ~v1_relat_1(k6_relat_1(k1_relat_1('#skF_7'))))), inference(superposition, [status(thm), theory('equality')], [c_162, c_1902])).
% 8.46/2.78  tff(c_2129, plain, (![A_181]: (k1_funct_1(k6_relat_1(k1_relat_1('#skF_7')), k1_funct_1(k2_funct_1('#skF_7'), A_181))=k1_funct_1(k2_funct_1('#skF_7'), A_181) | ~r2_hidden(A_181, k2_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36, c_163, c_383, c_139, c_162, c_2002])).
% 8.46/2.78  tff(c_2160, plain, (![A_58]: (k1_funct_1(k6_relat_1(k1_relat_1('#skF_7')), A_58)=k1_funct_1(k2_funct_1('#skF_7'), k1_funct_1('#skF_7', A_58)) | ~r2_hidden(k1_funct_1('#skF_7', A_58), k2_relat_1('#skF_7')) | ~r2_hidden(A_58, k1_relat_1('#skF_7')) | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_2129])).
% 8.46/2.78  tff(c_3928, plain, (![A_227]: (k1_funct_1(k6_relat_1(k1_relat_1('#skF_7')), A_227)=k1_funct_1(k2_funct_1('#skF_7'), k1_funct_1('#skF_7', A_227)) | ~r2_hidden(k1_funct_1('#skF_7', A_227), k2_relat_1('#skF_7')) | ~r2_hidden(A_227, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_2160])).
% 8.46/2.78  tff(c_3938, plain, (![D_45]: (k1_funct_1(k6_relat_1(k1_relat_1('#skF_7')), D_45)=k1_funct_1(k2_funct_1('#skF_7'), k1_funct_1('#skF_7', D_45)) | ~r2_hidden(D_45, k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_10, c_3928])).
% 8.46/2.78  tff(c_3944, plain, (![D_228]: (k1_funct_1(k6_relat_1(k1_relat_1('#skF_7')), D_228)=k1_funct_1(k2_funct_1('#skF_7'), k1_funct_1('#skF_7', D_228)) | ~r2_hidden(D_228, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_3938])).
% 8.46/2.78  tff(c_44, plain, (![A_53, C_57]: (k1_funct_1(k6_relat_1(A_53), C_57)=C_57 | ~r2_hidden(C_57, A_53) | ~v1_funct_1(k6_relat_1(A_53)) | ~v1_relat_1(k6_relat_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.46/2.78  tff(c_64, plain, (![A_53, C_57]: (k1_funct_1(k6_relat_1(A_53), C_57)=C_57 | ~r2_hidden(C_57, A_53) | ~v1_relat_1(k6_relat_1(A_53)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_44])).
% 8.46/2.78  tff(c_68, plain, (![A_53, C_57]: (k1_funct_1(k6_relat_1(A_53), C_57)=C_57 | ~r2_hidden(C_57, A_53))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_64])).
% 8.46/2.78  tff(c_4123, plain, (![D_233]: (k1_funct_1(k2_funct_1('#skF_7'), k1_funct_1('#skF_7', D_233))=D_233 | ~r2_hidden(D_233, k1_relat_1('#skF_7')) | ~r2_hidden(D_233, k1_relat_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_3944, c_68])).
% 8.46/2.78  tff(c_4167, plain, (![C_42]: (k1_funct_1(k2_funct_1('#skF_7'), C_42)='#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_42) | ~r2_hidden('#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_42), k1_relat_1('#skF_7')) | ~r2_hidden('#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_42), k1_relat_1('#skF_7')) | ~r2_hidden(C_42, k2_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_4123])).
% 8.46/2.78  tff(c_5583, plain, (![C_255]: (k1_funct_1(k2_funct_1('#skF_7'), C_255)='#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_255) | ~r2_hidden('#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_255), k1_relat_1('#skF_7')) | ~r2_hidden(C_255, k2_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_4167])).
% 8.46/2.78  tff(c_5587, plain, (![C_42]: (k1_funct_1(k2_funct_1('#skF_7'), C_42)='#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_42) | ~r2_hidden(C_42, k2_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_14, c_5583])).
% 8.46/2.78  tff(c_5666, plain, (![C_258]: (k1_funct_1(k2_funct_1('#skF_7'), C_258)='#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_258) | ~r2_hidden(C_258, k2_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_5587])).
% 8.46/2.78  tff(c_5804, plain, (k1_funct_1(k2_funct_1('#skF_7'), '#skF_6')='#skF_4'('#skF_7', k2_relat_1('#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_54, c_5666])).
% 8.46/2.78  tff(c_52, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_7'), '#skF_7'), '#skF_6')!='#skF_6' | k1_funct_1('#skF_7', k1_funct_1(k2_funct_1('#skF_7'), '#skF_6'))!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.46/2.78  tff(c_90, plain, (k1_funct_1('#skF_7', k1_funct_1(k2_funct_1('#skF_7'), '#skF_6'))!='#skF_6'), inference(splitLeft, [status(thm)], [c_52])).
% 8.46/2.78  tff(c_5805, plain, (k1_funct_1('#skF_7', '#skF_4'('#skF_7', k2_relat_1('#skF_7'), '#skF_6'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_5804, c_90])).
% 8.46/2.78  tff(c_5845, plain, (~r2_hidden('#skF_6', k2_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_12, c_5805])).
% 8.46/2.78  tff(c_5849, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_5845])).
% 8.46/2.78  tff(c_5851, plain, (k1_funct_1('#skF_7', k1_funct_1(k2_funct_1('#skF_7'), '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_52])).
% 8.46/2.78  tff(c_5887, plain, (![A_264]: (k4_relat_1(A_264)=k2_funct_1(A_264) | ~v2_funct_1(A_264) | ~v1_funct_1(A_264) | ~v1_relat_1(A_264))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.46/2.78  tff(c_5890, plain, (k4_relat_1('#skF_7')=k2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_56, c_5887])).
% 8.46/2.78  tff(c_5893, plain, (k4_relat_1('#skF_7')=k2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_5890])).
% 8.46/2.78  tff(c_5900, plain, (k2_relat_1(k2_funct_1('#skF_7'))=k1_relat_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_5893, c_4])).
% 8.46/2.78  tff(c_5906, plain, (k2_relat_1(k2_funct_1('#skF_7'))=k1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_5900])).
% 8.46/2.78  tff(c_5915, plain, (k5_relat_1(k2_funct_1('#skF_7'), k6_relat_1(k1_relat_1('#skF_7')))=k2_funct_1('#skF_7') | ~v1_relat_1(k2_funct_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_5906, c_8])).
% 8.46/2.78  tff(c_5919, plain, (~v1_relat_1(k2_funct_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_5915])).
% 8.46/2.78  tff(c_5922, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_32, c_5919])).
% 8.46/2.78  tff(c_5926, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_5922])).
% 8.46/2.78  tff(c_5928, plain, (v1_relat_1(k2_funct_1('#skF_7'))), inference(splitRight, [status(thm)], [c_5915])).
% 8.46/2.78  tff(c_5897, plain, (k1_relat_1(k2_funct_1('#skF_7'))=k2_relat_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_5893, c_6])).
% 8.46/2.78  tff(c_5904, plain, (k1_relat_1(k2_funct_1('#skF_7'))=k2_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_5897])).
% 8.46/2.78  tff(c_5975, plain, (![A_269, D_270]: (r2_hidden(k1_funct_1(A_269, D_270), k2_relat_1(A_269)) | ~r2_hidden(D_270, k1_relat_1(A_269)) | ~v1_funct_1(A_269) | ~v1_relat_1(A_269))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.46/2.78  tff(c_5978, plain, (![D_270]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_7'), D_270), k1_relat_1('#skF_7')) | ~r2_hidden(D_270, k1_relat_1(k2_funct_1('#skF_7'))) | ~v1_funct_1(k2_funct_1('#skF_7')) | ~v1_relat_1(k2_funct_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_5906, c_5975])).
% 8.46/2.78  tff(c_5989, plain, (![D_270]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_7'), D_270), k1_relat_1('#skF_7')) | ~r2_hidden(D_270, k2_relat_1('#skF_7')) | ~v1_funct_1(k2_funct_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_5928, c_5904, c_5978])).
% 8.46/2.78  tff(c_6097, plain, (~v1_funct_1(k2_funct_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_5989])).
% 8.46/2.78  tff(c_6147, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_30, c_6097])).
% 8.46/2.78  tff(c_6151, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_6147])).
% 8.46/2.78  tff(c_6153, plain, (v1_funct_1(k2_funct_1('#skF_7'))), inference(splitRight, [status(thm)], [c_5989])).
% 8.46/2.78  tff(c_5927, plain, (k5_relat_1(k2_funct_1('#skF_7'), k6_relat_1(k1_relat_1('#skF_7')))=k2_funct_1('#skF_7')), inference(splitRight, [status(thm)], [c_5915])).
% 8.46/2.78  tff(c_46, plain, (![A_53]: (k1_relat_1(k6_relat_1(A_53))=A_53 | ~v1_funct_1(k6_relat_1(A_53)) | ~v1_relat_1(k6_relat_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.46/2.78  tff(c_62, plain, (![A_53]: (k1_relat_1(k6_relat_1(A_53))=A_53 | ~v1_relat_1(k6_relat_1(A_53)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_46])).
% 8.46/2.78  tff(c_66, plain, (![A_53]: (k1_relat_1(k6_relat_1(A_53))=A_53)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_62])).
% 8.46/2.78  tff(c_5933, plain, (![A_265, B_266]: (k10_relat_1(A_265, k1_relat_1(B_266))=k1_relat_1(k5_relat_1(A_265, B_266)) | ~v1_relat_1(B_266) | ~v1_relat_1(A_265))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.46/2.78  tff(c_5948, plain, (![A_265, A_53]: (k1_relat_1(k5_relat_1(A_265, k6_relat_1(A_53)))=k10_relat_1(A_265, A_53) | ~v1_relat_1(k6_relat_1(A_53)) | ~v1_relat_1(A_265))), inference(superposition, [status(thm), theory('equality')], [c_66, c_5933])).
% 8.46/2.78  tff(c_5955, plain, (![A_267, A_268]: (k1_relat_1(k5_relat_1(A_267, k6_relat_1(A_268)))=k10_relat_1(A_267, A_268) | ~v1_relat_1(A_267))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_5948])).
% 8.46/2.78  tff(c_5967, plain, (k10_relat_1(k2_funct_1('#skF_7'), k1_relat_1('#skF_7'))=k1_relat_1(k2_funct_1('#skF_7')) | ~v1_relat_1(k2_funct_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_5927, c_5955])).
% 8.46/2.78  tff(c_5974, plain, (k10_relat_1(k2_funct_1('#skF_7'), k1_relat_1('#skF_7'))=k2_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_5928, c_5904, c_5967])).
% 8.46/2.78  tff(c_2, plain, (![A_1, B_3]: (k10_relat_1(A_1, k1_relat_1(B_3))=k1_relat_1(k5_relat_1(A_1, B_3)) | ~v1_relat_1(B_3) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.46/2.78  tff(c_5997, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_7'), '#skF_7'))=k2_relat_1('#skF_7') | ~v1_relat_1('#skF_7') | ~v1_relat_1(k2_funct_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_5974, c_2])).
% 8.46/2.78  tff(c_6004, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_7'), '#skF_7'))=k2_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_5928, c_60, c_5997])).
% 8.46/2.78  tff(c_8251, plain, (![C_381, B_382, A_383]: (k1_funct_1(k5_relat_1(C_381, B_382), A_383)=k1_funct_1(B_382, k1_funct_1(C_381, A_383)) | ~r2_hidden(A_383, k1_relat_1(k5_relat_1(C_381, B_382))) | ~v1_funct_1(C_381) | ~v1_relat_1(C_381) | ~v1_funct_1(B_382) | ~v1_relat_1(B_382))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.46/2.78  tff(c_8337, plain, (![A_383]: (k1_funct_1(k5_relat_1(k2_funct_1('#skF_7'), '#skF_7'), A_383)=k1_funct_1('#skF_7', k1_funct_1(k2_funct_1('#skF_7'), A_383)) | ~r2_hidden(A_383, k2_relat_1('#skF_7')) | ~v1_funct_1(k2_funct_1('#skF_7')) | ~v1_relat_1(k2_funct_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_6004, c_8251])).
% 8.46/2.78  tff(c_8438, plain, (![A_385]: (k1_funct_1(k5_relat_1(k2_funct_1('#skF_7'), '#skF_7'), A_385)=k1_funct_1('#skF_7', k1_funct_1(k2_funct_1('#skF_7'), A_385)) | ~r2_hidden(A_385, k2_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_5928, c_6153, c_8337])).
% 8.46/2.78  tff(c_5850, plain, (k1_funct_1(k5_relat_1(k2_funct_1('#skF_7'), '#skF_7'), '#skF_6')!='#skF_6'), inference(splitRight, [status(thm)], [c_52])).
% 8.46/2.78  tff(c_8464, plain, (k1_funct_1('#skF_7', k1_funct_1(k2_funct_1('#skF_7'), '#skF_6'))!='#skF_6' | ~r2_hidden('#skF_6', k2_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_8438, c_5850])).
% 8.46/2.78  tff(c_8483, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_5851, c_8464])).
% 8.46/2.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.46/2.78  
% 8.46/2.78  Inference rules
% 8.46/2.78  ----------------------
% 8.46/2.78  #Ref     : 1
% 8.46/2.78  #Sup     : 2011
% 8.46/2.78  #Fact    : 0
% 8.46/2.78  #Define  : 0
% 8.46/2.78  #Split   : 17
% 8.46/2.78  #Chain   : 0
% 8.46/2.78  #Close   : 0
% 8.46/2.78  
% 8.46/2.78  Ordering : KBO
% 8.46/2.78  
% 8.46/2.78  Simplification rules
% 8.46/2.78  ----------------------
% 8.46/2.78  #Subsume      : 454
% 8.46/2.78  #Demod        : 1727
% 8.46/2.78  #Tautology    : 427
% 8.46/2.78  #SimpNegUnit  : 10
% 8.46/2.78  #BackRed      : 6
% 8.46/2.78  
% 8.46/2.78  #Partial instantiations: 0
% 8.46/2.78  #Strategies tried      : 1
% 8.46/2.78  
% 8.46/2.78  Timing (in seconds)
% 8.46/2.78  ----------------------
% 8.46/2.78  Preprocessing        : 0.36
% 8.46/2.78  Parsing              : 0.18
% 8.46/2.78  CNF conversion       : 0.03
% 8.46/2.78  Main loop            : 1.63
% 8.46/2.78  Inferencing          : 0.59
% 8.46/2.78  Reduction            : 0.53
% 8.46/2.78  Demodulation         : 0.38
% 8.46/2.78  BG Simplification    : 0.09
% 8.46/2.78  Subsumption          : 0.31
% 8.46/2.78  Abstraction          : 0.12
% 8.46/2.78  MUC search           : 0.00
% 8.46/2.78  Cooper               : 0.00
% 8.46/2.78  Total                : 2.04
% 8.46/2.78  Index Insertion      : 0.00
% 8.46/2.78  Index Deletion       : 0.00
% 8.46/2.78  Index Matching       : 0.00
% 8.46/2.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
