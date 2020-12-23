%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:50 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 224 expanded)
%              Number of leaves         :   20 (  90 expanded)
%              Depth                    :   11
%              Number of atoms          :  256 ( 917 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_wellord1 > r4_wellord1 > v8_relat_2 > v6_relat_2 > v4_relat_2 > v2_wellord1 > v1_wellord1 > v1_relat_2 > v1_relat_1 > v1_funct_1 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(r4_wellord1,type,(
    r4_wellord1: ( $i * $i ) > $o )).

tff(r3_wellord1,type,(
    r3_wellord1: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(v6_relat_2,type,(
    v6_relat_2: $i > $o )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_wellord1,type,(
    v1_wellord1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( ( r4_wellord1(A,B)
                & v2_wellord1(A) )
             => v2_wellord1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_wellord1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
      <=> ( v1_relat_2(A)
          & v8_relat_2(A)
          & v4_relat_2(A)
          & v6_relat_2(A)
          & v1_wellord1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
          <=> ? [C] :
                ( v1_relat_1(C)
                & v1_funct_1(C)
                & r3_wellord1(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_wellord1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ( r3_wellord1(A,B,C)
               => ( ( v1_relat_2(A)
                   => v1_relat_2(B) )
                  & ( v8_relat_2(A)
                   => v8_relat_2(B) )
                  & ( v6_relat_2(A)
                   => v6_relat_2(B) )
                  & ( v4_relat_2(A)
                   => v4_relat_2(B) )
                  & ( v1_wellord1(A)
                   => v1_wellord1(B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_wellord1)).

tff(c_32,plain,(
    ~ v2_wellord1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_38,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_40,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_34,plain,(
    v2_wellord1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_42,plain,(
    ! [A_21] :
      ( v1_relat_2(A_21)
      | ~ v2_wellord1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_45,plain,
    ( v1_relat_2('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_42])).

tff(c_48,plain,(
    v1_relat_2('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_45])).

tff(c_36,plain,(
    r4_wellord1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_18,plain,(
    ! [A_2,B_8] :
      ( v1_funct_1('#skF_1'(A_2,B_8))
      | ~ r4_wellord1(A_2,B_8)
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_20,plain,(
    ! [A_2,B_8] :
      ( v1_relat_1('#skF_1'(A_2,B_8))
      | ~ r4_wellord1(A_2,B_8)
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_16,plain,(
    ! [A_2,B_8] :
      ( r3_wellord1(A_2,B_8,'#skF_1'(A_2,B_8))
      | ~ r4_wellord1(A_2,B_8)
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_86,plain,(
    ! [B_44,A_45,C_46] :
      ( v1_relat_2(B_44)
      | ~ v1_relat_2(A_45)
      | ~ r3_wellord1(A_45,B_44,C_46)
      | ~ v1_funct_1(C_46)
      | ~ v1_relat_1(C_46)
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_96,plain,(
    ! [B_50,A_51] :
      ( v1_relat_2(B_50)
      | ~ v1_relat_2(A_51)
      | ~ v1_funct_1('#skF_1'(A_51,B_50))
      | ~ v1_relat_1('#skF_1'(A_51,B_50))
      | ~ r4_wellord1(A_51,B_50)
      | ~ v1_relat_1(B_50)
      | ~ v1_relat_1(A_51) ) ),
    inference(resolution,[status(thm)],[c_16,c_86])).

tff(c_101,plain,(
    ! [B_52,A_53] :
      ( v1_relat_2(B_52)
      | ~ v1_relat_2(A_53)
      | ~ v1_funct_1('#skF_1'(A_53,B_52))
      | ~ r4_wellord1(A_53,B_52)
      | ~ v1_relat_1(B_52)
      | ~ v1_relat_1(A_53) ) ),
    inference(resolution,[status(thm)],[c_20,c_96])).

tff(c_106,plain,(
    ! [B_54,A_55] :
      ( v1_relat_2(B_54)
      | ~ v1_relat_2(A_55)
      | ~ r4_wellord1(A_55,B_54)
      | ~ v1_relat_1(B_54)
      | ~ v1_relat_1(A_55) ) ),
    inference(resolution,[status(thm)],[c_18,c_101])).

tff(c_109,plain,
    ( v1_relat_2('#skF_3')
    | ~ v1_relat_2('#skF_2')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_106])).

tff(c_112,plain,(
    v1_relat_2('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_48,c_109])).

tff(c_8,plain,(
    ! [A_1] :
      ( v4_relat_2(A_1)
      | ~ v2_wellord1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_71,plain,(
    ! [B_35,A_36,C_37] :
      ( v4_relat_2(B_35)
      | ~ v4_relat_2(A_36)
      | ~ r3_wellord1(A_36,B_35,C_37)
      | ~ v1_funct_1(C_37)
      | ~ v1_relat_1(C_37)
      | ~ v1_relat_1(B_35)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_140,plain,(
    ! [B_62,A_63] :
      ( v4_relat_2(B_62)
      | ~ v4_relat_2(A_63)
      | ~ v1_funct_1('#skF_1'(A_63,B_62))
      | ~ v1_relat_1('#skF_1'(A_63,B_62))
      | ~ r4_wellord1(A_63,B_62)
      | ~ v1_relat_1(B_62)
      | ~ v1_relat_1(A_63) ) ),
    inference(resolution,[status(thm)],[c_16,c_71])).

tff(c_145,plain,(
    ! [B_64,A_65] :
      ( v4_relat_2(B_64)
      | ~ v4_relat_2(A_65)
      | ~ v1_funct_1('#skF_1'(A_65,B_64))
      | ~ r4_wellord1(A_65,B_64)
      | ~ v1_relat_1(B_64)
      | ~ v1_relat_1(A_65) ) ),
    inference(resolution,[status(thm)],[c_20,c_140])).

tff(c_155,plain,(
    ! [B_68,A_69] :
      ( v4_relat_2(B_68)
      | ~ v4_relat_2(A_69)
      | ~ r4_wellord1(A_69,B_68)
      | ~ v1_relat_1(B_68)
      | ~ v1_relat_1(A_69) ) ),
    inference(resolution,[status(thm)],[c_18,c_145])).

tff(c_158,plain,
    ( v4_relat_2('#skF_3')
    | ~ v4_relat_2('#skF_2')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_155])).

tff(c_161,plain,
    ( v4_relat_2('#skF_3')
    | ~ v4_relat_2('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_158])).

tff(c_162,plain,(
    ~ v4_relat_2('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_161])).

tff(c_165,plain,
    ( ~ v2_wellord1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_162])).

tff(c_169,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34,c_165])).

tff(c_170,plain,(
    v4_relat_2('#skF_3') ),
    inference(splitRight,[status(thm)],[c_161])).

tff(c_6,plain,(
    ! [A_1] :
      ( v6_relat_2(A_1)
      | ~ v2_wellord1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_81,plain,(
    ! [B_41,A_42,C_43] :
      ( v6_relat_2(B_41)
      | ~ v6_relat_2(A_42)
      | ~ r3_wellord1(A_42,B_41,C_43)
      | ~ v1_funct_1(C_43)
      | ~ v1_relat_1(C_43)
      | ~ v1_relat_1(B_41)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_113,plain,(
    ! [B_56,A_57] :
      ( v6_relat_2(B_56)
      | ~ v6_relat_2(A_57)
      | ~ v1_funct_1('#skF_1'(A_57,B_56))
      | ~ v1_relat_1('#skF_1'(A_57,B_56))
      | ~ r4_wellord1(A_57,B_56)
      | ~ v1_relat_1(B_56)
      | ~ v1_relat_1(A_57) ) ),
    inference(resolution,[status(thm)],[c_16,c_81])).

tff(c_118,plain,(
    ! [B_58,A_59] :
      ( v6_relat_2(B_58)
      | ~ v6_relat_2(A_59)
      | ~ v1_funct_1('#skF_1'(A_59,B_58))
      | ~ r4_wellord1(A_59,B_58)
      | ~ v1_relat_1(B_58)
      | ~ v1_relat_1(A_59) ) ),
    inference(resolution,[status(thm)],[c_20,c_113])).

tff(c_123,plain,(
    ! [B_60,A_61] :
      ( v6_relat_2(B_60)
      | ~ v6_relat_2(A_61)
      | ~ r4_wellord1(A_61,B_60)
      | ~ v1_relat_1(B_60)
      | ~ v1_relat_1(A_61) ) ),
    inference(resolution,[status(thm)],[c_18,c_118])).

tff(c_126,plain,
    ( v6_relat_2('#skF_3')
    | ~ v6_relat_2('#skF_2')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_123])).

tff(c_129,plain,
    ( v6_relat_2('#skF_3')
    | ~ v6_relat_2('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_126])).

tff(c_130,plain,(
    ~ v6_relat_2('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_129])).

tff(c_133,plain,
    ( ~ v2_wellord1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_130])).

tff(c_137,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34,c_133])).

tff(c_138,plain,(
    v6_relat_2('#skF_3') ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_10,plain,(
    ! [A_1] :
      ( v8_relat_2(A_1)
      | ~ v2_wellord1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_76,plain,(
    ! [B_38,A_39,C_40] :
      ( v8_relat_2(B_38)
      | ~ v8_relat_2(A_39)
      | ~ r3_wellord1(A_39,B_38,C_40)
      | ~ v1_funct_1(C_40)
      | ~ v1_relat_1(C_40)
      | ~ v1_relat_1(B_38)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_150,plain,(
    ! [B_66,A_67] :
      ( v8_relat_2(B_66)
      | ~ v8_relat_2(A_67)
      | ~ v1_funct_1('#skF_1'(A_67,B_66))
      | ~ v1_relat_1('#skF_1'(A_67,B_66))
      | ~ r4_wellord1(A_67,B_66)
      | ~ v1_relat_1(B_66)
      | ~ v1_relat_1(A_67) ) ),
    inference(resolution,[status(thm)],[c_16,c_76])).

tff(c_172,plain,(
    ! [B_70,A_71] :
      ( v8_relat_2(B_70)
      | ~ v8_relat_2(A_71)
      | ~ v1_funct_1('#skF_1'(A_71,B_70))
      | ~ r4_wellord1(A_71,B_70)
      | ~ v1_relat_1(B_70)
      | ~ v1_relat_1(A_71) ) ),
    inference(resolution,[status(thm)],[c_20,c_150])).

tff(c_177,plain,(
    ! [B_72,A_73] :
      ( v8_relat_2(B_72)
      | ~ v8_relat_2(A_73)
      | ~ r4_wellord1(A_73,B_72)
      | ~ v1_relat_1(B_72)
      | ~ v1_relat_1(A_73) ) ),
    inference(resolution,[status(thm)],[c_18,c_172])).

tff(c_180,plain,
    ( v8_relat_2('#skF_3')
    | ~ v8_relat_2('#skF_2')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_177])).

tff(c_183,plain,
    ( v8_relat_2('#skF_3')
    | ~ v8_relat_2('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_180])).

tff(c_184,plain,(
    ~ v8_relat_2('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_183])).

tff(c_187,plain,
    ( ~ v2_wellord1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_184])).

tff(c_191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34,c_187])).

tff(c_192,plain,(
    v8_relat_2('#skF_3') ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_2,plain,(
    ! [A_1] :
      ( v2_wellord1(A_1)
      | ~ v1_wellord1(A_1)
      | ~ v6_relat_2(A_1)
      | ~ v4_relat_2(A_1)
      | ~ v8_relat_2(A_1)
      | ~ v1_relat_2(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_201,plain,
    ( v2_wellord1('#skF_3')
    | ~ v1_wellord1('#skF_3')
    | ~ v6_relat_2('#skF_3')
    | ~ v4_relat_2('#skF_3')
    | ~ v1_relat_2('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_192,c_2])).

tff(c_204,plain,
    ( v2_wellord1('#skF_3')
    | ~ v1_wellord1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_112,c_170,c_138,c_201])).

tff(c_205,plain,(
    ~ v1_wellord1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_204])).

tff(c_50,plain,(
    ! [A_23] :
      ( v1_wellord1(A_23)
      | ~ v2_wellord1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_53,plain,
    ( v1_wellord1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_50])).

tff(c_56,plain,(
    v1_wellord1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_53])).

tff(c_91,plain,(
    ! [B_47,A_48,C_49] :
      ( v1_wellord1(B_47)
      | ~ v1_wellord1(A_48)
      | ~ r3_wellord1(A_48,B_47,C_49)
      | ~ v1_funct_1(C_49)
      | ~ v1_relat_1(C_49)
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_194,plain,(
    ! [B_74,A_75] :
      ( v1_wellord1(B_74)
      | ~ v1_wellord1(A_75)
      | ~ v1_funct_1('#skF_1'(A_75,B_74))
      | ~ v1_relat_1('#skF_1'(A_75,B_74))
      | ~ r4_wellord1(A_75,B_74)
      | ~ v1_relat_1(B_74)
      | ~ v1_relat_1(A_75) ) ),
    inference(resolution,[status(thm)],[c_16,c_91])).

tff(c_212,plain,(
    ! [B_76,A_77] :
      ( v1_wellord1(B_76)
      | ~ v1_wellord1(A_77)
      | ~ v1_funct_1('#skF_1'(A_77,B_76))
      | ~ r4_wellord1(A_77,B_76)
      | ~ v1_relat_1(B_76)
      | ~ v1_relat_1(A_77) ) ),
    inference(resolution,[status(thm)],[c_20,c_194])).

tff(c_217,plain,(
    ! [B_78,A_79] :
      ( v1_wellord1(B_78)
      | ~ v1_wellord1(A_79)
      | ~ r4_wellord1(A_79,B_78)
      | ~ v1_relat_1(B_78)
      | ~ v1_relat_1(A_79) ) ),
    inference(resolution,[status(thm)],[c_18,c_212])).

tff(c_220,plain,
    ( v1_wellord1('#skF_3')
    | ~ v1_wellord1('#skF_2')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_217])).

tff(c_223,plain,(
    v1_wellord1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_56,c_220])).

tff(c_225,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_205,c_223])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:29:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.28  
% 2.14/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.28  %$ r3_wellord1 > r4_wellord1 > v8_relat_2 > v6_relat_2 > v4_relat_2 > v2_wellord1 > v1_wellord1 > v1_relat_2 > v1_relat_1 > v1_funct_1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.14/1.28  
% 2.14/1.28  %Foreground sorts:
% 2.14/1.28  
% 2.14/1.28  
% 2.14/1.28  %Background operators:
% 2.14/1.28  
% 2.14/1.28  
% 2.14/1.28  %Foreground operators:
% 2.14/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.14/1.28  tff(r4_wellord1, type, r4_wellord1: ($i * $i) > $o).
% 2.14/1.28  tff(r3_wellord1, type, r3_wellord1: ($i * $i * $i) > $o).
% 2.14/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.28  tff(v1_relat_2, type, v1_relat_2: $i > $o).
% 2.14/1.28  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 2.14/1.28  tff(v6_relat_2, type, v6_relat_2: $i > $o).
% 2.14/1.28  tff(v4_relat_2, type, v4_relat_2: $i > $o).
% 2.14/1.28  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 2.14/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.14/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.28  tff(v1_wellord1, type, v1_wellord1: $i > $o).
% 2.14/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.14/1.28  
% 2.14/1.30  tff(f_97, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => ((r4_wellord1(A, B) & v2_wellord1(A)) => v2_wellord1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_wellord1)).
% 2.14/1.30  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) <=> ((((v1_relat_2(A) & v8_relat_2(A)) & v4_relat_2(A)) & v6_relat_2(A)) & v1_wellord1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_wellord1)).
% 2.14/1.30  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r4_wellord1(A, B) <=> (?[C]: ((v1_relat_1(C) & v1_funct_1(C)) & r3_wellord1(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_wellord1)).
% 2.14/1.30  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r3_wellord1(A, B, C) => (((((v1_relat_2(A) => v1_relat_2(B)) & (v8_relat_2(A) => v8_relat_2(B))) & (v6_relat_2(A) => v6_relat_2(B))) & (v4_relat_2(A) => v4_relat_2(B))) & (v1_wellord1(A) => v1_wellord1(B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_wellord1)).
% 2.14/1.30  tff(c_32, plain, (~v2_wellord1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.14/1.30  tff(c_38, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.14/1.30  tff(c_40, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.14/1.30  tff(c_34, plain, (v2_wellord1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.14/1.30  tff(c_42, plain, (![A_21]: (v1_relat_2(A_21) | ~v2_wellord1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.14/1.30  tff(c_45, plain, (v1_relat_2('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_34, c_42])).
% 2.14/1.30  tff(c_48, plain, (v1_relat_2('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_45])).
% 2.14/1.30  tff(c_36, plain, (r4_wellord1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.14/1.30  tff(c_18, plain, (![A_2, B_8]: (v1_funct_1('#skF_1'(A_2, B_8)) | ~r4_wellord1(A_2, B_8) | ~v1_relat_1(B_8) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.14/1.30  tff(c_20, plain, (![A_2, B_8]: (v1_relat_1('#skF_1'(A_2, B_8)) | ~r4_wellord1(A_2, B_8) | ~v1_relat_1(B_8) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.14/1.30  tff(c_16, plain, (![A_2, B_8]: (r3_wellord1(A_2, B_8, '#skF_1'(A_2, B_8)) | ~r4_wellord1(A_2, B_8) | ~v1_relat_1(B_8) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.14/1.30  tff(c_86, plain, (![B_44, A_45, C_46]: (v1_relat_2(B_44) | ~v1_relat_2(A_45) | ~r3_wellord1(A_45, B_44, C_46) | ~v1_funct_1(C_46) | ~v1_relat_1(C_46) | ~v1_relat_1(B_44) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.14/1.30  tff(c_96, plain, (![B_50, A_51]: (v1_relat_2(B_50) | ~v1_relat_2(A_51) | ~v1_funct_1('#skF_1'(A_51, B_50)) | ~v1_relat_1('#skF_1'(A_51, B_50)) | ~r4_wellord1(A_51, B_50) | ~v1_relat_1(B_50) | ~v1_relat_1(A_51))), inference(resolution, [status(thm)], [c_16, c_86])).
% 2.14/1.30  tff(c_101, plain, (![B_52, A_53]: (v1_relat_2(B_52) | ~v1_relat_2(A_53) | ~v1_funct_1('#skF_1'(A_53, B_52)) | ~r4_wellord1(A_53, B_52) | ~v1_relat_1(B_52) | ~v1_relat_1(A_53))), inference(resolution, [status(thm)], [c_20, c_96])).
% 2.14/1.30  tff(c_106, plain, (![B_54, A_55]: (v1_relat_2(B_54) | ~v1_relat_2(A_55) | ~r4_wellord1(A_55, B_54) | ~v1_relat_1(B_54) | ~v1_relat_1(A_55))), inference(resolution, [status(thm)], [c_18, c_101])).
% 2.14/1.30  tff(c_109, plain, (v1_relat_2('#skF_3') | ~v1_relat_2('#skF_2') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_36, c_106])).
% 2.14/1.30  tff(c_112, plain, (v1_relat_2('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_48, c_109])).
% 2.14/1.30  tff(c_8, plain, (![A_1]: (v4_relat_2(A_1) | ~v2_wellord1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.14/1.30  tff(c_71, plain, (![B_35, A_36, C_37]: (v4_relat_2(B_35) | ~v4_relat_2(A_36) | ~r3_wellord1(A_36, B_35, C_37) | ~v1_funct_1(C_37) | ~v1_relat_1(C_37) | ~v1_relat_1(B_35) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.14/1.30  tff(c_140, plain, (![B_62, A_63]: (v4_relat_2(B_62) | ~v4_relat_2(A_63) | ~v1_funct_1('#skF_1'(A_63, B_62)) | ~v1_relat_1('#skF_1'(A_63, B_62)) | ~r4_wellord1(A_63, B_62) | ~v1_relat_1(B_62) | ~v1_relat_1(A_63))), inference(resolution, [status(thm)], [c_16, c_71])).
% 2.14/1.30  tff(c_145, plain, (![B_64, A_65]: (v4_relat_2(B_64) | ~v4_relat_2(A_65) | ~v1_funct_1('#skF_1'(A_65, B_64)) | ~r4_wellord1(A_65, B_64) | ~v1_relat_1(B_64) | ~v1_relat_1(A_65))), inference(resolution, [status(thm)], [c_20, c_140])).
% 2.14/1.30  tff(c_155, plain, (![B_68, A_69]: (v4_relat_2(B_68) | ~v4_relat_2(A_69) | ~r4_wellord1(A_69, B_68) | ~v1_relat_1(B_68) | ~v1_relat_1(A_69))), inference(resolution, [status(thm)], [c_18, c_145])).
% 2.14/1.30  tff(c_158, plain, (v4_relat_2('#skF_3') | ~v4_relat_2('#skF_2') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_36, c_155])).
% 2.14/1.30  tff(c_161, plain, (v4_relat_2('#skF_3') | ~v4_relat_2('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_158])).
% 2.14/1.30  tff(c_162, plain, (~v4_relat_2('#skF_2')), inference(splitLeft, [status(thm)], [c_161])).
% 2.14/1.30  tff(c_165, plain, (~v2_wellord1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_162])).
% 2.14/1.30  tff(c_169, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_34, c_165])).
% 2.14/1.30  tff(c_170, plain, (v4_relat_2('#skF_3')), inference(splitRight, [status(thm)], [c_161])).
% 2.14/1.30  tff(c_6, plain, (![A_1]: (v6_relat_2(A_1) | ~v2_wellord1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.14/1.30  tff(c_81, plain, (![B_41, A_42, C_43]: (v6_relat_2(B_41) | ~v6_relat_2(A_42) | ~r3_wellord1(A_42, B_41, C_43) | ~v1_funct_1(C_43) | ~v1_relat_1(C_43) | ~v1_relat_1(B_41) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.14/1.30  tff(c_113, plain, (![B_56, A_57]: (v6_relat_2(B_56) | ~v6_relat_2(A_57) | ~v1_funct_1('#skF_1'(A_57, B_56)) | ~v1_relat_1('#skF_1'(A_57, B_56)) | ~r4_wellord1(A_57, B_56) | ~v1_relat_1(B_56) | ~v1_relat_1(A_57))), inference(resolution, [status(thm)], [c_16, c_81])).
% 2.14/1.30  tff(c_118, plain, (![B_58, A_59]: (v6_relat_2(B_58) | ~v6_relat_2(A_59) | ~v1_funct_1('#skF_1'(A_59, B_58)) | ~r4_wellord1(A_59, B_58) | ~v1_relat_1(B_58) | ~v1_relat_1(A_59))), inference(resolution, [status(thm)], [c_20, c_113])).
% 2.14/1.30  tff(c_123, plain, (![B_60, A_61]: (v6_relat_2(B_60) | ~v6_relat_2(A_61) | ~r4_wellord1(A_61, B_60) | ~v1_relat_1(B_60) | ~v1_relat_1(A_61))), inference(resolution, [status(thm)], [c_18, c_118])).
% 2.14/1.30  tff(c_126, plain, (v6_relat_2('#skF_3') | ~v6_relat_2('#skF_2') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_36, c_123])).
% 2.14/1.30  tff(c_129, plain, (v6_relat_2('#skF_3') | ~v6_relat_2('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_126])).
% 2.14/1.30  tff(c_130, plain, (~v6_relat_2('#skF_2')), inference(splitLeft, [status(thm)], [c_129])).
% 2.14/1.30  tff(c_133, plain, (~v2_wellord1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_6, c_130])).
% 2.14/1.30  tff(c_137, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_34, c_133])).
% 2.14/1.30  tff(c_138, plain, (v6_relat_2('#skF_3')), inference(splitRight, [status(thm)], [c_129])).
% 2.14/1.30  tff(c_10, plain, (![A_1]: (v8_relat_2(A_1) | ~v2_wellord1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.14/1.30  tff(c_76, plain, (![B_38, A_39, C_40]: (v8_relat_2(B_38) | ~v8_relat_2(A_39) | ~r3_wellord1(A_39, B_38, C_40) | ~v1_funct_1(C_40) | ~v1_relat_1(C_40) | ~v1_relat_1(B_38) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.14/1.30  tff(c_150, plain, (![B_66, A_67]: (v8_relat_2(B_66) | ~v8_relat_2(A_67) | ~v1_funct_1('#skF_1'(A_67, B_66)) | ~v1_relat_1('#skF_1'(A_67, B_66)) | ~r4_wellord1(A_67, B_66) | ~v1_relat_1(B_66) | ~v1_relat_1(A_67))), inference(resolution, [status(thm)], [c_16, c_76])).
% 2.14/1.30  tff(c_172, plain, (![B_70, A_71]: (v8_relat_2(B_70) | ~v8_relat_2(A_71) | ~v1_funct_1('#skF_1'(A_71, B_70)) | ~r4_wellord1(A_71, B_70) | ~v1_relat_1(B_70) | ~v1_relat_1(A_71))), inference(resolution, [status(thm)], [c_20, c_150])).
% 2.14/1.30  tff(c_177, plain, (![B_72, A_73]: (v8_relat_2(B_72) | ~v8_relat_2(A_73) | ~r4_wellord1(A_73, B_72) | ~v1_relat_1(B_72) | ~v1_relat_1(A_73))), inference(resolution, [status(thm)], [c_18, c_172])).
% 2.14/1.30  tff(c_180, plain, (v8_relat_2('#skF_3') | ~v8_relat_2('#skF_2') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_36, c_177])).
% 2.14/1.30  tff(c_183, plain, (v8_relat_2('#skF_3') | ~v8_relat_2('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_180])).
% 2.14/1.30  tff(c_184, plain, (~v8_relat_2('#skF_2')), inference(splitLeft, [status(thm)], [c_183])).
% 2.14/1.30  tff(c_187, plain, (~v2_wellord1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10, c_184])).
% 2.14/1.30  tff(c_191, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_34, c_187])).
% 2.14/1.30  tff(c_192, plain, (v8_relat_2('#skF_3')), inference(splitRight, [status(thm)], [c_183])).
% 2.14/1.30  tff(c_2, plain, (![A_1]: (v2_wellord1(A_1) | ~v1_wellord1(A_1) | ~v6_relat_2(A_1) | ~v4_relat_2(A_1) | ~v8_relat_2(A_1) | ~v1_relat_2(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.14/1.30  tff(c_201, plain, (v2_wellord1('#skF_3') | ~v1_wellord1('#skF_3') | ~v6_relat_2('#skF_3') | ~v4_relat_2('#skF_3') | ~v1_relat_2('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_192, c_2])).
% 2.14/1.30  tff(c_204, plain, (v2_wellord1('#skF_3') | ~v1_wellord1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_112, c_170, c_138, c_201])).
% 2.14/1.30  tff(c_205, plain, (~v1_wellord1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_32, c_204])).
% 2.14/1.30  tff(c_50, plain, (![A_23]: (v1_wellord1(A_23) | ~v2_wellord1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.14/1.30  tff(c_53, plain, (v1_wellord1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_34, c_50])).
% 2.14/1.30  tff(c_56, plain, (v1_wellord1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_53])).
% 2.14/1.30  tff(c_91, plain, (![B_47, A_48, C_49]: (v1_wellord1(B_47) | ~v1_wellord1(A_48) | ~r3_wellord1(A_48, B_47, C_49) | ~v1_funct_1(C_49) | ~v1_relat_1(C_49) | ~v1_relat_1(B_47) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.14/1.30  tff(c_194, plain, (![B_74, A_75]: (v1_wellord1(B_74) | ~v1_wellord1(A_75) | ~v1_funct_1('#skF_1'(A_75, B_74)) | ~v1_relat_1('#skF_1'(A_75, B_74)) | ~r4_wellord1(A_75, B_74) | ~v1_relat_1(B_74) | ~v1_relat_1(A_75))), inference(resolution, [status(thm)], [c_16, c_91])).
% 2.14/1.30  tff(c_212, plain, (![B_76, A_77]: (v1_wellord1(B_76) | ~v1_wellord1(A_77) | ~v1_funct_1('#skF_1'(A_77, B_76)) | ~r4_wellord1(A_77, B_76) | ~v1_relat_1(B_76) | ~v1_relat_1(A_77))), inference(resolution, [status(thm)], [c_20, c_194])).
% 2.14/1.30  tff(c_217, plain, (![B_78, A_79]: (v1_wellord1(B_78) | ~v1_wellord1(A_79) | ~r4_wellord1(A_79, B_78) | ~v1_relat_1(B_78) | ~v1_relat_1(A_79))), inference(resolution, [status(thm)], [c_18, c_212])).
% 2.14/1.30  tff(c_220, plain, (v1_wellord1('#skF_3') | ~v1_wellord1('#skF_2') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_36, c_217])).
% 2.14/1.30  tff(c_223, plain, (v1_wellord1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_56, c_220])).
% 2.14/1.30  tff(c_225, plain, $false, inference(negUnitSimplification, [status(thm)], [c_205, c_223])).
% 2.14/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.30  
% 2.14/1.30  Inference rules
% 2.14/1.30  ----------------------
% 2.14/1.30  #Ref     : 0
% 2.14/1.30  #Sup     : 29
% 2.14/1.30  #Fact    : 0
% 2.14/1.30  #Define  : 0
% 2.14/1.30  #Split   : 3
% 2.14/1.30  #Chain   : 0
% 2.14/1.30  #Close   : 0
% 2.14/1.30  
% 2.14/1.30  Ordering : KBO
% 2.14/1.30  
% 2.14/1.30  Simplification rules
% 2.14/1.30  ----------------------
% 2.14/1.30  #Subsume      : 10
% 2.14/1.30  #Demod        : 30
% 2.14/1.30  #Tautology    : 3
% 2.14/1.30  #SimpNegUnit  : 2
% 2.14/1.30  #BackRed      : 0
% 2.14/1.30  
% 2.14/1.30  #Partial instantiations: 0
% 2.14/1.30  #Strategies tried      : 1
% 2.14/1.30  
% 2.14/1.30  Timing (in seconds)
% 2.14/1.30  ----------------------
% 2.14/1.31  Preprocessing        : 0.28
% 2.14/1.31  Parsing              : 0.15
% 2.14/1.31  CNF conversion       : 0.02
% 2.14/1.31  Main loop            : 0.24
% 2.14/1.31  Inferencing          : 0.11
% 2.14/1.31  Reduction            : 0.06
% 2.14/1.31  Demodulation         : 0.04
% 2.14/1.31  BG Simplification    : 0.02
% 2.14/1.31  Subsumption          : 0.04
% 2.14/1.31  Abstraction          : 0.01
% 2.14/1.31  MUC search           : 0.00
% 2.14/1.31  Cooper               : 0.00
% 2.14/1.31  Total                : 0.56
% 2.14/1.31  Index Insertion      : 0.00
% 2.14/1.31  Index Deletion       : 0.00
% 2.14/1.31  Index Matching       : 0.00
% 2.14/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
