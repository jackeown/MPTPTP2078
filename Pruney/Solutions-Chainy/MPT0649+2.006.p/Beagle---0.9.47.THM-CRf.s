%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:44 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 241 expanded)
%              Number of leaves         :   23 (  90 expanded)
%              Depth                    :   12
%              Number of atoms          :  185 ( 902 expanded)
%              Number of equality atoms :   21 ( 179 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_106,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( v2_funct_1(B)
            & r2_hidden(A,k1_relat_1(B)) )
         => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
            & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_93,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( B = k2_funct_1(A)
            <=> ( k1_relat_1(B) = k2_relat_1(A)
                & ! [C,D] :
                    ( ( ( r2_hidden(C,k2_relat_1(A))
                        & D = k1_funct_1(B,C) )
                     => ( r2_hidden(D,k1_relat_1(A))
                        & C = k1_funct_1(A,D) ) )
                    & ( ( r2_hidden(D,k1_relat_1(A))
                        & C = k1_funct_1(A,D) )
                     => ( r2_hidden(C,k2_relat_1(A))
                        & D = k1_funct_1(B,C) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_funct_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
          <=> ( r2_hidden(A,k1_relat_1(C))
              & r2_hidden(k1_funct_1(C,A),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

tff(c_50,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_48,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_funct_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_relat_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_46,plain,(
    v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_44,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_107,plain,(
    ! [A_42,D_43] :
      ( k1_funct_1(k2_funct_1(A_42),k1_funct_1(A_42,D_43)) = D_43
      | ~ r2_hidden(D_43,k1_relat_1(A_42))
      | ~ v1_funct_1(k2_funct_1(A_42))
      | ~ v1_relat_1(k2_funct_1(A_42))
      | ~ v2_funct_1(A_42)
      | ~ v1_funct_1(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_42,plain,
    ( k1_funct_1(k5_relat_1('#skF_6',k2_funct_1('#skF_6')),'#skF_5') != '#skF_5'
    | k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_53,plain,(
    k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_125,plain,
    ( ~ r2_hidden('#skF_5',k1_relat_1('#skF_6'))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_53])).

tff(c_139,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_125])).

tff(c_142,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_145,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_142])).

tff(c_149,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_145])).

tff(c_150,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_154,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2,c_150])).

tff(c_158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_154])).

tff(c_159,plain,(
    k1_funct_1(k5_relat_1('#skF_6',k2_funct_1('#skF_6')),'#skF_5') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_160,plain,(
    k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_185,plain,(
    ! [C_50,A_51,B_52] :
      ( r2_hidden(k1_funct_1(C_50,A_51),k1_relat_1(B_52))
      | ~ r2_hidden(A_51,k1_relat_1(k5_relat_1(C_50,B_52)))
      | ~ v1_funct_1(C_50)
      | ~ v1_relat_1(C_50)
      | ~ v1_funct_1(B_52)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_195,plain,(
    ! [B_52] :
      ( r2_hidden('#skF_5',k1_relat_1(B_52))
      | ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'),B_52)))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6'))
      | ~ v1_funct_1(B_52)
      | ~ v1_relat_1(B_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_185])).

tff(c_230,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_195])).

tff(c_233,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_230])).

tff(c_237,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_233])).

tff(c_239,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_195])).

tff(c_238,plain,(
    ! [B_52] :
      ( ~ v1_funct_1(k2_funct_1('#skF_6'))
      | r2_hidden('#skF_5',k1_relat_1(B_52))
      | ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'),B_52)))
      | ~ v1_funct_1(B_52)
      | ~ v1_relat_1(B_52) ) ),
    inference(splitRight,[status(thm)],[c_195])).

tff(c_240,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_238])).

tff(c_243,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2,c_240])).

tff(c_247,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_243])).

tff(c_249,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_238])).

tff(c_40,plain,(
    ! [A_10,D_26] :
      ( r2_hidden(k1_funct_1(A_10,D_26),k2_relat_1(A_10))
      | ~ r2_hidden(D_26,k1_relat_1(A_10))
      | ~ v1_funct_1(k2_funct_1(A_10))
      | ~ v1_relat_1(k2_funct_1(A_10))
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_165,plain,(
    ! [A_44] :
      ( k1_relat_1(k2_funct_1(A_44)) = k2_relat_1(A_44)
      | ~ v1_funct_1(k2_funct_1(A_44))
      | ~ v1_relat_1(k2_funct_1(A_44))
      | ~ v2_funct_1(A_44)
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_170,plain,(
    ! [A_45] :
      ( k1_relat_1(k2_funct_1(A_45)) = k2_relat_1(A_45)
      | ~ v1_funct_1(k2_funct_1(A_45))
      | ~ v2_funct_1(A_45)
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(resolution,[status(thm)],[c_4,c_165])).

tff(c_174,plain,(
    ! [A_1] :
      ( k1_relat_1(k2_funct_1(A_1)) = k2_relat_1(A_1)
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_170])).

tff(c_338,plain,(
    ! [A_65,C_66,B_67] :
      ( r2_hidden(A_65,k1_relat_1(k5_relat_1(C_66,B_67)))
      | ~ r2_hidden(k1_funct_1(C_66,A_65),k1_relat_1(B_67))
      | ~ r2_hidden(A_65,k1_relat_1(C_66))
      | ~ v1_funct_1(C_66)
      | ~ v1_relat_1(C_66)
      | ~ v1_funct_1(B_67)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_356,plain,(
    ! [B_67] :
      ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'),B_67)))
      | ~ r2_hidden('#skF_5',k1_relat_1(B_67))
      | ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_relat_1(k2_funct_1('#skF_6')))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6'))
      | ~ v1_funct_1(B_67)
      | ~ v1_relat_1(B_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_338])).

tff(c_360,plain,(
    ! [B_67] :
      ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'),B_67)))
      | ~ r2_hidden('#skF_5',k1_relat_1(B_67))
      | ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_relat_1(k2_funct_1('#skF_6')))
      | ~ v1_funct_1(B_67)
      | ~ v1_relat_1(B_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_249,c_356])).

tff(c_361,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_relat_1(k2_funct_1('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_360])).

tff(c_367,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),k2_relat_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_361])).

tff(c_372,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_367])).

tff(c_375,plain,
    ( ~ r2_hidden('#skF_5',k1_relat_1('#skF_6'))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_372])).

tff(c_379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_239,c_249,c_44,c_375])).

tff(c_381,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_relat_1(k2_funct_1('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_360])).

tff(c_6,plain,(
    ! [A_2,C_5,B_3] :
      ( r2_hidden(A_2,k1_relat_1(k5_relat_1(C_5,B_3)))
      | ~ r2_hidden(k1_funct_1(C_5,A_2),k1_relat_1(B_3))
      | ~ r2_hidden(A_2,k1_relat_1(C_5))
      | ~ v1_funct_1(C_5)
      | ~ v1_relat_1(C_5)
      | ~ v1_funct_1(B_3)
      | ~ v1_relat_1(B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_385,plain,
    ( r2_hidden('#skF_5',k1_relat_1(k5_relat_1('#skF_6',k2_funct_1('#skF_6'))))
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_381,c_6])).

tff(c_391,plain,(
    r2_hidden('#skF_5',k1_relat_1(k5_relat_1('#skF_6',k2_funct_1('#skF_6')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_249,c_50,c_48,c_44,c_385])).

tff(c_12,plain,(
    ! [C_9,B_7,A_6] :
      ( k1_funct_1(k5_relat_1(C_9,B_7),A_6) = k1_funct_1(B_7,k1_funct_1(C_9,A_6))
      | ~ r2_hidden(A_6,k1_relat_1(k5_relat_1(C_9,B_7)))
      | ~ v1_funct_1(C_9)
      | ~ v1_relat_1(C_9)
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_396,plain,
    ( k1_funct_1(k5_relat_1('#skF_6',k2_funct_1('#skF_6')),'#skF_5') = k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_391,c_12])).

tff(c_402,plain,(
    k1_funct_1(k5_relat_1('#skF_6',k2_funct_1('#skF_6')),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_249,c_50,c_48,c_160,c_396])).

tff(c_404,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_159,c_402])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:04:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.33  
% 2.73/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.34  %$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 2.73/1.34  
% 2.73/1.34  %Foreground sorts:
% 2.73/1.34  
% 2.73/1.34  
% 2.73/1.34  %Background operators:
% 2.73/1.34  
% 2.73/1.34  
% 2.73/1.34  %Foreground operators:
% 2.73/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.73/1.34  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.73/1.34  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.73/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.73/1.34  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.73/1.34  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.73/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.73/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.73/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.73/1.34  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.73/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.73/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.73/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.73/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.73/1.34  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.73/1.34  
% 2.73/1.35  tff(f_106, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_funct_1)).
% 2.73/1.35  tff(f_33, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.73/1.35  tff(f_93, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k2_funct_1(A)) <=> ((k1_relat_1(B) = k2_relat_1(A)) & (![C, D]: (((r2_hidden(C, k2_relat_1(A)) & (D = k1_funct_1(B, C))) => (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))) & ((r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D))) => (r2_hidden(C, k2_relat_1(A)) & (D = k1_funct_1(B, C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_funct_1)).
% 2.73/1.35  tff(f_48, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), k1_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_funct_1)).
% 2.73/1.35  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) => (k1_funct_1(k5_relat_1(C, B), A) = k1_funct_1(B, k1_funct_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_funct_1)).
% 2.73/1.35  tff(c_50, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.73/1.35  tff(c_48, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.73/1.35  tff(c_2, plain, (![A_1]: (v1_funct_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.73/1.35  tff(c_4, plain, (![A_1]: (v1_relat_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.73/1.35  tff(c_46, plain, (v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.73/1.35  tff(c_44, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.73/1.35  tff(c_107, plain, (![A_42, D_43]: (k1_funct_1(k2_funct_1(A_42), k1_funct_1(A_42, D_43))=D_43 | ~r2_hidden(D_43, k1_relat_1(A_42)) | ~v1_funct_1(k2_funct_1(A_42)) | ~v1_relat_1(k2_funct_1(A_42)) | ~v2_funct_1(A_42) | ~v1_funct_1(A_42) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.73/1.35  tff(c_42, plain, (k1_funct_1(k5_relat_1('#skF_6', k2_funct_1('#skF_6')), '#skF_5')!='#skF_5' | k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.73/1.35  tff(c_53, plain, (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_42])).
% 2.73/1.35  tff(c_125, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_107, c_53])).
% 2.73/1.35  tff(c_139, plain, (~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_125])).
% 2.73/1.35  tff(c_142, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_139])).
% 2.73/1.35  tff(c_145, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_4, c_142])).
% 2.73/1.35  tff(c_149, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_145])).
% 2.73/1.35  tff(c_150, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_139])).
% 2.73/1.35  tff(c_154, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2, c_150])).
% 2.73/1.35  tff(c_158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_154])).
% 2.73/1.35  tff(c_159, plain, (k1_funct_1(k5_relat_1('#skF_6', k2_funct_1('#skF_6')), '#skF_5')!='#skF_5'), inference(splitRight, [status(thm)], [c_42])).
% 2.73/1.35  tff(c_160, plain, (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_42])).
% 2.73/1.35  tff(c_185, plain, (![C_50, A_51, B_52]: (r2_hidden(k1_funct_1(C_50, A_51), k1_relat_1(B_52)) | ~r2_hidden(A_51, k1_relat_1(k5_relat_1(C_50, B_52))) | ~v1_funct_1(C_50) | ~v1_relat_1(C_50) | ~v1_funct_1(B_52) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.73/1.35  tff(c_195, plain, (![B_52]: (r2_hidden('#skF_5', k1_relat_1(B_52)) | ~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'), B_52))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v1_funct_1(B_52) | ~v1_relat_1(B_52))), inference(superposition, [status(thm), theory('equality')], [c_160, c_185])).
% 2.73/1.35  tff(c_230, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_195])).
% 2.73/1.35  tff(c_233, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_4, c_230])).
% 2.73/1.35  tff(c_237, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_233])).
% 2.73/1.35  tff(c_239, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_195])).
% 2.73/1.35  tff(c_238, plain, (![B_52]: (~v1_funct_1(k2_funct_1('#skF_6')) | r2_hidden('#skF_5', k1_relat_1(B_52)) | ~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'), B_52))) | ~v1_funct_1(B_52) | ~v1_relat_1(B_52))), inference(splitRight, [status(thm)], [c_195])).
% 2.73/1.35  tff(c_240, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_238])).
% 2.73/1.35  tff(c_243, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2, c_240])).
% 2.73/1.35  tff(c_247, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_243])).
% 2.73/1.35  tff(c_249, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_238])).
% 2.73/1.35  tff(c_40, plain, (![A_10, D_26]: (r2_hidden(k1_funct_1(A_10, D_26), k2_relat_1(A_10)) | ~r2_hidden(D_26, k1_relat_1(A_10)) | ~v1_funct_1(k2_funct_1(A_10)) | ~v1_relat_1(k2_funct_1(A_10)) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.73/1.35  tff(c_165, plain, (![A_44]: (k1_relat_1(k2_funct_1(A_44))=k2_relat_1(A_44) | ~v1_funct_1(k2_funct_1(A_44)) | ~v1_relat_1(k2_funct_1(A_44)) | ~v2_funct_1(A_44) | ~v1_funct_1(A_44) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.73/1.35  tff(c_170, plain, (![A_45]: (k1_relat_1(k2_funct_1(A_45))=k2_relat_1(A_45) | ~v1_funct_1(k2_funct_1(A_45)) | ~v2_funct_1(A_45) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45))), inference(resolution, [status(thm)], [c_4, c_165])).
% 2.73/1.35  tff(c_174, plain, (![A_1]: (k1_relat_1(k2_funct_1(A_1))=k2_relat_1(A_1) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(resolution, [status(thm)], [c_2, c_170])).
% 2.73/1.35  tff(c_338, plain, (![A_65, C_66, B_67]: (r2_hidden(A_65, k1_relat_1(k5_relat_1(C_66, B_67))) | ~r2_hidden(k1_funct_1(C_66, A_65), k1_relat_1(B_67)) | ~r2_hidden(A_65, k1_relat_1(C_66)) | ~v1_funct_1(C_66) | ~v1_relat_1(C_66) | ~v1_funct_1(B_67) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.73/1.35  tff(c_356, plain, (![B_67]: (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'), B_67))) | ~r2_hidden('#skF_5', k1_relat_1(B_67)) | ~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v1_funct_1(B_67) | ~v1_relat_1(B_67))), inference(superposition, [status(thm), theory('equality')], [c_160, c_338])).
% 2.73/1.35  tff(c_360, plain, (![B_67]: (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_relat_1(k5_relat_1(k2_funct_1('#skF_6'), B_67))) | ~r2_hidden('#skF_5', k1_relat_1(B_67)) | ~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_relat_1(k2_funct_1('#skF_6'))) | ~v1_funct_1(B_67) | ~v1_relat_1(B_67))), inference(demodulation, [status(thm), theory('equality')], [c_239, c_249, c_356])).
% 2.73/1.35  tff(c_361, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_relat_1(k2_funct_1('#skF_6')))), inference(splitLeft, [status(thm)], [c_360])).
% 2.73/1.35  tff(c_367, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k2_relat_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_174, c_361])).
% 2.73/1.35  tff(c_372, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_367])).
% 2.73/1.35  tff(c_375, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_40, c_372])).
% 2.73/1.35  tff(c_379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_239, c_249, c_44, c_375])).
% 2.73/1.35  tff(c_381, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_relat_1(k2_funct_1('#skF_6')))), inference(splitRight, [status(thm)], [c_360])).
% 2.73/1.35  tff(c_6, plain, (![A_2, C_5, B_3]: (r2_hidden(A_2, k1_relat_1(k5_relat_1(C_5, B_3))) | ~r2_hidden(k1_funct_1(C_5, A_2), k1_relat_1(B_3)) | ~r2_hidden(A_2, k1_relat_1(C_5)) | ~v1_funct_1(C_5) | ~v1_relat_1(C_5) | ~v1_funct_1(B_3) | ~v1_relat_1(B_3))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.73/1.35  tff(c_385, plain, (r2_hidden('#skF_5', k1_relat_1(k5_relat_1('#skF_6', k2_funct_1('#skF_6')))) | ~r2_hidden('#skF_5', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_381, c_6])).
% 2.73/1.35  tff(c_391, plain, (r2_hidden('#skF_5', k1_relat_1(k5_relat_1('#skF_6', k2_funct_1('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_239, c_249, c_50, c_48, c_44, c_385])).
% 2.73/1.35  tff(c_12, plain, (![C_9, B_7, A_6]: (k1_funct_1(k5_relat_1(C_9, B_7), A_6)=k1_funct_1(B_7, k1_funct_1(C_9, A_6)) | ~r2_hidden(A_6, k1_relat_1(k5_relat_1(C_9, B_7))) | ~v1_funct_1(C_9) | ~v1_relat_1(C_9) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.73/1.35  tff(c_396, plain, (k1_funct_1(k5_relat_1('#skF_6', k2_funct_1('#skF_6')), '#skF_5')=k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_5')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_391, c_12])).
% 2.73/1.35  tff(c_402, plain, (k1_funct_1(k5_relat_1('#skF_6', k2_funct_1('#skF_6')), '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_239, c_249, c_50, c_48, c_160, c_396])).
% 2.73/1.35  tff(c_404, plain, $false, inference(negUnitSimplification, [status(thm)], [c_159, c_402])).
% 2.73/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.35  
% 2.73/1.35  Inference rules
% 2.73/1.35  ----------------------
% 2.73/1.35  #Ref     : 0
% 2.73/1.35  #Sup     : 74
% 2.73/1.35  #Fact    : 0
% 2.73/1.35  #Define  : 0
% 2.73/1.35  #Split   : 6
% 2.73/1.35  #Chain   : 0
% 2.73/1.35  #Close   : 0
% 2.73/1.35  
% 2.73/1.35  Ordering : KBO
% 2.73/1.35  
% 2.73/1.35  Simplification rules
% 2.73/1.35  ----------------------
% 2.73/1.35  #Subsume      : 4
% 2.73/1.35  #Demod        : 67
% 2.73/1.35  #Tautology    : 26
% 2.73/1.35  #SimpNegUnit  : 1
% 2.73/1.35  #BackRed      : 0
% 2.73/1.35  
% 2.73/1.35  #Partial instantiations: 0
% 2.73/1.35  #Strategies tried      : 1
% 2.73/1.35  
% 2.73/1.35  Timing (in seconds)
% 2.73/1.35  ----------------------
% 2.73/1.36  Preprocessing        : 0.31
% 2.73/1.36  Parsing              : 0.16
% 2.73/1.36  CNF conversion       : 0.02
% 2.73/1.36  Main loop            : 0.28
% 2.73/1.36  Inferencing          : 0.10
% 2.73/1.36  Reduction            : 0.08
% 2.73/1.36  Demodulation         : 0.06
% 2.73/1.36  BG Simplification    : 0.03
% 2.73/1.36  Subsumption          : 0.06
% 2.73/1.36  Abstraction          : 0.01
% 2.73/1.36  MUC search           : 0.00
% 2.73/1.36  Cooper               : 0.00
% 2.73/1.36  Total                : 0.62
% 2.73/1.36  Index Insertion      : 0.00
% 2.73/1.36  Index Deletion       : 0.00
% 2.73/1.36  Index Matching       : 0.00
% 2.73/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
