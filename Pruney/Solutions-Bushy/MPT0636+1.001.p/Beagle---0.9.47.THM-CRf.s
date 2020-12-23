%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0636+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:37 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 108 expanded)
%              Number of leaves         :   18 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :  106 ( 264 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,k6_relat_1(B))))
        <=> ( r2_hidden(A,k1_relat_1(C))
            & r2_hidden(k1_funct_1(C,A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_45,axiom,(
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

tff(c_32,plain,
    ( r2_hidden('#skF_2',k1_relat_1(k5_relat_1('#skF_4',k6_relat_1('#skF_3'))))
    | r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_67,plain,(
    r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_24,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_36,plain,
    ( r2_hidden('#skF_2',k1_relat_1(k5_relat_1('#skF_4',k6_relat_1('#skF_3'))))
    | r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_66,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_4,plain,(
    ! [A_2] : v1_relat_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_6,plain,(
    ! [A_2] : v1_funct_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_20,plain,(
    ! [A_7] :
      ( k1_relat_1(k6_relat_1(A_7)) = A_7
      | ~ v1_funct_1(k6_relat_1(A_7))
      | ~ v1_relat_1(k6_relat_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_38,plain,(
    ! [A_7] :
      ( k1_relat_1(k6_relat_1(A_7)) = A_7
      | ~ v1_relat_1(k6_relat_1(A_7)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_20])).

tff(c_42,plain,(
    ! [A_7] : k1_relat_1(k6_relat_1(A_7)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_38])).

tff(c_139,plain,(
    ! [A_31,C_32,B_33] :
      ( r2_hidden(A_31,k1_relat_1(k5_relat_1(C_32,B_33)))
      | ~ r2_hidden(k1_funct_1(C_32,A_31),k1_relat_1(B_33))
      | ~ r2_hidden(A_31,k1_relat_1(C_32))
      | ~ v1_funct_1(C_32)
      | ~ v1_relat_1(C_32)
      | ~ v1_funct_1(B_33)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_148,plain,(
    ! [A_31,C_32,A_7] :
      ( r2_hidden(A_31,k1_relat_1(k5_relat_1(C_32,k6_relat_1(A_7))))
      | ~ r2_hidden(k1_funct_1(C_32,A_31),A_7)
      | ~ r2_hidden(A_31,k1_relat_1(C_32))
      | ~ v1_funct_1(C_32)
      | ~ v1_relat_1(C_32)
      | ~ v1_funct_1(k6_relat_1(A_7))
      | ~ v1_relat_1(k6_relat_1(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_139])).

tff(c_226,plain,(
    ! [A_44,C_45,A_46] :
      ( r2_hidden(A_44,k1_relat_1(k5_relat_1(C_45,k6_relat_1(A_46))))
      | ~ r2_hidden(k1_funct_1(C_45,A_44),A_46)
      | ~ r2_hidden(A_44,k1_relat_1(C_45))
      | ~ v1_funct_1(C_45)
      | ~ v1_relat_1(C_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6,c_148])).

tff(c_26,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3')
    | ~ r2_hidden('#skF_2',k1_relat_1('#skF_4'))
    | ~ r2_hidden('#skF_2',k1_relat_1(k5_relat_1('#skF_4',k6_relat_1('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_69,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3')
    | ~ r2_hidden('#skF_2',k1_relat_1(k5_relat_1('#skF_4',k6_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_26])).

tff(c_70,plain,(
    ~ r2_hidden('#skF_2',k1_relat_1(k5_relat_1('#skF_4',k6_relat_1('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_69])).

tff(c_243,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3')
    | ~ r2_hidden('#skF_2',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_226,c_70])).

tff(c_255,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_66,c_67,c_243])).

tff(c_256,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_259,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_256])).

tff(c_261,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_260,plain,(
    r2_hidden('#skF_2',k1_relat_1(k5_relat_1('#skF_4',k6_relat_1('#skF_3')))) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_300,plain,(
    ! [C_52,A_53,B_54] :
      ( r2_hidden(k1_funct_1(C_52,A_53),k1_relat_1(B_54))
      | ~ r2_hidden(A_53,k1_relat_1(k5_relat_1(C_52,B_54)))
      | ~ v1_funct_1(C_52)
      | ~ v1_relat_1(C_52)
      | ~ v1_funct_1(B_54)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_310,plain,(
    ! [C_52,A_53,A_7] :
      ( r2_hidden(k1_funct_1(C_52,A_53),A_7)
      | ~ r2_hidden(A_53,k1_relat_1(k5_relat_1(C_52,k6_relat_1(A_7))))
      | ~ v1_funct_1(C_52)
      | ~ v1_relat_1(C_52)
      | ~ v1_funct_1(k6_relat_1(A_7))
      | ~ v1_relat_1(k6_relat_1(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_300])).

tff(c_316,plain,(
    ! [C_55,A_56,A_57] :
      ( r2_hidden(k1_funct_1(C_55,A_56),A_57)
      | ~ r2_hidden(A_56,k1_relat_1(k5_relat_1(C_55,k6_relat_1(A_57))))
      | ~ v1_funct_1(C_55)
      | ~ v1_relat_1(C_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6,c_310])).

tff(c_327,plain,
    ( r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_260,c_316])).

tff(c_332,plain,(
    r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_327])).

tff(c_334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_261,c_332])).

tff(c_336,plain,(
    ~ r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_335,plain,(
    r2_hidden('#skF_2',k1_relat_1(k5_relat_1('#skF_4',k6_relat_1('#skF_3')))) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_351,plain,(
    ! [A_59,C_60,B_61] :
      ( r2_hidden(A_59,k1_relat_1(C_60))
      | ~ r2_hidden(A_59,k1_relat_1(k5_relat_1(C_60,B_61)))
      | ~ v1_funct_1(C_60)
      | ~ v1_relat_1(C_60)
      | ~ v1_funct_1(B_61)
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_358,plain,
    ( r2_hidden('#skF_2',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1(k6_relat_1('#skF_3'))
    | ~ v1_relat_1(k6_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_335,c_351])).

tff(c_362,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6,c_24,c_22,c_358])).

tff(c_364,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_336,c_362])).

%------------------------------------------------------------------------------
