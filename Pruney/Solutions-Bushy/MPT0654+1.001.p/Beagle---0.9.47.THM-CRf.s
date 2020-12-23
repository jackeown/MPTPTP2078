%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0654+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:39 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 166 expanded)
%              Number of leaves         :   24 (  65 expanded)
%              Depth                    :   10
%              Number of atoms          :  229 ( 532 expanded)
%              Number of equality atoms :   44 ( 128 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
            & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_32,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v1_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_97,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k1_relat_1(B)) )
       => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
          & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

tff(f_107,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
          & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k2_relat_1(B)) )
       => ( A = k1_funct_1(B,k1_funct_1(k2_funct_1(B),A))
          & A = k1_funct_1(k5_relat_1(k2_funct_1(B),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_40,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_38,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_funct_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_relat_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( v1_funct_1(k5_relat_1(A_4,B_5))
      | ~ v1_funct_1(B_5)
      | ~ v1_relat_1(B_5)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( v1_relat_1(k5_relat_1(A_2,B_3))
      | ~ v1_relat_1(B_3)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_30,plain,(
    ! [A_15] :
      ( k1_relat_1(k5_relat_1(A_15,k2_funct_1(A_15))) = k1_relat_1(A_15)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_86,plain,(
    ! [B_30] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_30),B_30),k1_relat_1(B_30))
      | k6_relat_1(k1_relat_1(B_30)) = B_30
      | ~ v1_funct_1(B_30)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_244,plain,(
    ! [A_46] :
      ( r2_hidden('#skF_1'(k1_relat_1(k5_relat_1(A_46,k2_funct_1(A_46))),k5_relat_1(A_46,k2_funct_1(A_46))),k1_relat_1(A_46))
      | k6_relat_1(k1_relat_1(k5_relat_1(A_46,k2_funct_1(A_46)))) = k5_relat_1(A_46,k2_funct_1(A_46))
      | ~ v1_funct_1(k5_relat_1(A_46,k2_funct_1(A_46)))
      | ~ v1_relat_1(k5_relat_1(A_46,k2_funct_1(A_46)))
      | ~ v2_funct_1(A_46)
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_86])).

tff(c_20,plain,(
    ! [B_12,A_11] :
      ( k1_funct_1(k5_relat_1(B_12,k2_funct_1(B_12)),A_11) = A_11
      | ~ r2_hidden(A_11,k1_relat_1(B_12))
      | ~ v2_funct_1(B_12)
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_179,plain,(
    ! [B_39] :
      ( k1_funct_1(B_39,'#skF_1'(k1_relat_1(B_39),B_39)) != '#skF_1'(k1_relat_1(B_39),B_39)
      | k6_relat_1(k1_relat_1(B_39)) = B_39
      | ~ v1_funct_1(B_39)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_194,plain,(
    ! [B_12] :
      ( k6_relat_1(k1_relat_1(k5_relat_1(B_12,k2_funct_1(B_12)))) = k5_relat_1(B_12,k2_funct_1(B_12))
      | ~ v1_funct_1(k5_relat_1(B_12,k2_funct_1(B_12)))
      | ~ v1_relat_1(k5_relat_1(B_12,k2_funct_1(B_12)))
      | ~ r2_hidden('#skF_1'(k1_relat_1(k5_relat_1(B_12,k2_funct_1(B_12))),k5_relat_1(B_12,k2_funct_1(B_12))),k1_relat_1(B_12))
      | ~ v2_funct_1(B_12)
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_179])).

tff(c_258,plain,(
    ! [A_47] :
      ( k6_relat_1(k1_relat_1(k5_relat_1(A_47,k2_funct_1(A_47)))) = k5_relat_1(A_47,k2_funct_1(A_47))
      | ~ v1_funct_1(k5_relat_1(A_47,k2_funct_1(A_47)))
      | ~ v1_relat_1(k5_relat_1(A_47,k2_funct_1(A_47)))
      | ~ v2_funct_1(A_47)
      | ~ v1_funct_1(A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(resolution,[status(thm)],[c_244,c_194])).

tff(c_275,plain,(
    ! [A_48] :
      ( k5_relat_1(A_48,k2_funct_1(A_48)) = k6_relat_1(k1_relat_1(A_48))
      | ~ v1_funct_1(k5_relat_1(A_48,k2_funct_1(A_48)))
      | ~ v1_relat_1(k5_relat_1(A_48,k2_funct_1(A_48)))
      | ~ v2_funct_1(A_48)
      | ~ v1_funct_1(A_48)
      | ~ v1_relat_1(A_48)
      | ~ v2_funct_1(A_48)
      | ~ v1_funct_1(A_48)
      | ~ v1_relat_1(A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_258])).

tff(c_281,plain,(
    ! [A_49] :
      ( k5_relat_1(A_49,k2_funct_1(A_49)) = k6_relat_1(k1_relat_1(A_49))
      | ~ v1_funct_1(k5_relat_1(A_49,k2_funct_1(A_49)))
      | ~ v2_funct_1(A_49)
      | ~ v1_funct_1(A_49)
      | ~ v1_relat_1(k2_funct_1(A_49))
      | ~ v1_relat_1(A_49) ) ),
    inference(resolution,[status(thm)],[c_6,c_275])).

tff(c_287,plain,(
    ! [A_50] :
      ( k5_relat_1(A_50,k2_funct_1(A_50)) = k6_relat_1(k1_relat_1(A_50))
      | ~ v2_funct_1(A_50)
      | ~ v1_funct_1(k2_funct_1(A_50))
      | ~ v1_relat_1(k2_funct_1(A_50))
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(resolution,[status(thm)],[c_8,c_281])).

tff(c_291,plain,(
    ! [A_51] :
      ( k5_relat_1(A_51,k2_funct_1(A_51)) = k6_relat_1(k1_relat_1(A_51))
      | ~ v2_funct_1(A_51)
      | ~ v1_funct_1(k2_funct_1(A_51))
      | ~ v1_funct_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(resolution,[status(thm)],[c_4,c_287])).

tff(c_295,plain,(
    ! [A_52] :
      ( k5_relat_1(A_52,k2_funct_1(A_52)) = k6_relat_1(k1_relat_1(A_52))
      | ~ v2_funct_1(A_52)
      | ~ v1_funct_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(resolution,[status(thm)],[c_2,c_291])).

tff(c_36,plain,
    ( k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') != k6_relat_1(k2_relat_1('#skF_2'))
    | k5_relat_1('#skF_2',k2_funct_1('#skF_2')) != k6_relat_1(k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_57,plain,(
    k5_relat_1('#skF_2',k2_funct_1('#skF_2')) != k6_relat_1(k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_313,plain,
    ( ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_57])).

tff(c_327,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_313])).

tff(c_328,plain,(
    k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') != k6_relat_1(k2_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_329,plain,(
    k5_relat_1('#skF_2',k2_funct_1('#skF_2')) = k6_relat_1(k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_336,plain,
    ( v1_relat_1(k6_relat_1(k1_relat_1('#skF_2')))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_329,c_6])).

tff(c_342,plain,
    ( v1_relat_1(k6_relat_1(k1_relat_1('#skF_2')))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_336])).

tff(c_344,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_342])).

tff(c_347,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_344])).

tff(c_351,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_347])).

tff(c_353,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_342])).

tff(c_333,plain,
    ( v1_funct_1(k6_relat_1(k1_relat_1('#skF_2')))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_329,c_8])).

tff(c_340,plain,
    ( v1_funct_1(k6_relat_1(k1_relat_1('#skF_2')))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_333])).

tff(c_355,plain,
    ( v1_funct_1(k6_relat_1(k1_relat_1('#skF_2')))
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_340])).

tff(c_356,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_355])).

tff(c_359,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_356])).

tff(c_363,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_359])).

tff(c_365,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_355])).

tff(c_34,plain,(
    ! [A_16] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(A_16),A_16)) = k2_relat_1(A_16)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_432,plain,(
    ! [B_59] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_59),B_59),k1_relat_1(B_59))
      | k6_relat_1(k1_relat_1(B_59)) = B_59
      | ~ v1_funct_1(B_59)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_709,plain,(
    ! [A_77] :
      ( r2_hidden('#skF_1'(k1_relat_1(k5_relat_1(k2_funct_1(A_77),A_77)),k5_relat_1(k2_funct_1(A_77),A_77)),k2_relat_1(A_77))
      | k6_relat_1(k1_relat_1(k5_relat_1(k2_funct_1(A_77),A_77))) = k5_relat_1(k2_funct_1(A_77),A_77)
      | ~ v1_funct_1(k5_relat_1(k2_funct_1(A_77),A_77))
      | ~ v1_relat_1(k5_relat_1(k2_funct_1(A_77),A_77))
      | ~ v2_funct_1(A_77)
      | ~ v1_funct_1(A_77)
      | ~ v1_relat_1(A_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_432])).

tff(c_24,plain,(
    ! [B_14,A_13] :
      ( k1_funct_1(k5_relat_1(k2_funct_1(B_14),B_14),A_13) = A_13
      | ~ r2_hidden(A_13,k2_relat_1(B_14))
      | ~ v2_funct_1(B_14)
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_558,plain,(
    ! [B_68] :
      ( k1_funct_1(B_68,'#skF_1'(k1_relat_1(B_68),B_68)) != '#skF_1'(k1_relat_1(B_68),B_68)
      | k6_relat_1(k1_relat_1(B_68)) = B_68
      | ~ v1_funct_1(B_68)
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_580,plain,(
    ! [B_14] :
      ( k6_relat_1(k1_relat_1(k5_relat_1(k2_funct_1(B_14),B_14))) = k5_relat_1(k2_funct_1(B_14),B_14)
      | ~ v1_funct_1(k5_relat_1(k2_funct_1(B_14),B_14))
      | ~ v1_relat_1(k5_relat_1(k2_funct_1(B_14),B_14))
      | ~ r2_hidden('#skF_1'(k1_relat_1(k5_relat_1(k2_funct_1(B_14),B_14)),k5_relat_1(k2_funct_1(B_14),B_14)),k2_relat_1(B_14))
      | ~ v2_funct_1(B_14)
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_558])).

tff(c_750,plain,(
    ! [A_79] :
      ( k6_relat_1(k1_relat_1(k5_relat_1(k2_funct_1(A_79),A_79))) = k5_relat_1(k2_funct_1(A_79),A_79)
      | ~ v1_funct_1(k5_relat_1(k2_funct_1(A_79),A_79))
      | ~ v1_relat_1(k5_relat_1(k2_funct_1(A_79),A_79))
      | ~ v2_funct_1(A_79)
      | ~ v1_funct_1(A_79)
      | ~ v1_relat_1(A_79) ) ),
    inference(resolution,[status(thm)],[c_709,c_580])).

tff(c_1120,plain,(
    ! [A_96] :
      ( k5_relat_1(k2_funct_1(A_96),A_96) = k6_relat_1(k2_relat_1(A_96))
      | ~ v1_funct_1(k5_relat_1(k2_funct_1(A_96),A_96))
      | ~ v1_relat_1(k5_relat_1(k2_funct_1(A_96),A_96))
      | ~ v2_funct_1(A_96)
      | ~ v1_funct_1(A_96)
      | ~ v1_relat_1(A_96)
      | ~ v2_funct_1(A_96)
      | ~ v1_funct_1(A_96)
      | ~ v1_relat_1(A_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_750])).

tff(c_1126,plain,(
    ! [B_97] :
      ( k5_relat_1(k2_funct_1(B_97),B_97) = k6_relat_1(k2_relat_1(B_97))
      | ~ v1_funct_1(k5_relat_1(k2_funct_1(B_97),B_97))
      | ~ v2_funct_1(B_97)
      | ~ v1_funct_1(B_97)
      | ~ v1_relat_1(B_97)
      | ~ v1_relat_1(k2_funct_1(B_97)) ) ),
    inference(resolution,[status(thm)],[c_6,c_1120])).

tff(c_1132,plain,(
    ! [B_98] :
      ( k5_relat_1(k2_funct_1(B_98),B_98) = k6_relat_1(k2_relat_1(B_98))
      | ~ v2_funct_1(B_98)
      | ~ v1_funct_1(B_98)
      | ~ v1_relat_1(B_98)
      | ~ v1_funct_1(k2_funct_1(B_98))
      | ~ v1_relat_1(k2_funct_1(B_98)) ) ),
    inference(resolution,[status(thm)],[c_8,c_1126])).

tff(c_1134,plain,
    ( k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') = k6_relat_1(k2_relat_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_353,c_1132])).

tff(c_1139,plain,(
    k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') = k6_relat_1(k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_42,c_40,c_38,c_1134])).

tff(c_1141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_328,c_1139])).

%------------------------------------------------------------------------------
