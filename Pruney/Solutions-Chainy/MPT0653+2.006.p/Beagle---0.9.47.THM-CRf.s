%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:58 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 188 expanded)
%              Number of leaves         :   25 (  83 expanded)
%              Depth                    :   17
%              Number of atoms          :  174 (1040 expanded)
%              Number of equality atoms :   45 ( 344 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_132,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( v2_funct_1(A)
                & k1_relat_1(A) = k2_relat_1(B)
                & k2_relat_1(A) = k1_relat_1(B)
                & ! [C,D] :
                    ( ( r2_hidden(C,k1_relat_1(A))
                      & r2_hidden(D,k1_relat_1(B)) )
                   => ( k1_funct_1(A,C) = D
                    <=> k1_funct_1(B,D) = C ) ) )
             => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_33,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_funct_1)).

tff(f_105,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k2_relat_1(B)) )
       => ( A = k1_funct_1(B,k1_funct_1(k2_funct_1(B),A))
          & A = k1_funct_1(k5_relat_1(k2_funct_1(B),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).

tff(c_60,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_58,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_52,plain,(
    v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_48,plain,(
    k2_relat_1('#skF_6') = k1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_36,plain,(
    ! [A_19] :
      ( k1_relat_1(k2_funct_1(A_19)) = k2_relat_1(A_19)
      | ~ v2_funct_1(A_19)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_46,plain,(
    k2_funct_1('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_relat_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_145,plain,(
    ! [A_49,D_50] :
      ( r2_hidden(k1_funct_1(A_49,D_50),k2_relat_1(A_49))
      | ~ r2_hidden(D_50,k1_relat_1(A_49))
      | ~ v1_funct_1(k2_funct_1(A_49))
      | ~ v1_relat_1(k2_funct_1(A_49))
      | ~ v2_funct_1(A_49)
      | ~ v1_funct_1(A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_160,plain,(
    ! [D_50] :
      ( r2_hidden(k1_funct_1('#skF_6',D_50),k1_relat_1('#skF_7'))
      | ~ r2_hidden(D_50,k1_relat_1('#skF_6'))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6'))
      | ~ v2_funct_1('#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_145])).

tff(c_164,plain,(
    ! [D_50] :
      ( r2_hidden(k1_funct_1('#skF_6',D_50),k1_relat_1('#skF_7'))
      | ~ r2_hidden(D_50,k1_relat_1('#skF_6'))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_52,c_160])).

tff(c_165,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_164])).

tff(c_169,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_165])).

tff(c_173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_169])).

tff(c_175,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_funct_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_174,plain,(
    ! [D_50] :
      ( ~ v1_funct_1(k2_funct_1('#skF_6'))
      | r2_hidden(k1_funct_1('#skF_6',D_50),k1_relat_1('#skF_7'))
      | ~ r2_hidden(D_50,k1_relat_1('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_176,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_174])).

tff(c_179,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2,c_176])).

tff(c_183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_179])).

tff(c_185,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_56,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_54,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_44,plain,(
    ! [A_22,B_26] :
      ( r2_hidden('#skF_5'(A_22,B_26),k1_relat_1(A_22))
      | B_26 = A_22
      | k1_relat_1(B_26) != k1_relat_1(A_22)
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_40,plain,(
    ! [B_21,A_20] :
      ( k1_funct_1(B_21,k1_funct_1(k2_funct_1(B_21),A_20)) = A_20
      | ~ r2_hidden(A_20,k2_relat_1(B_21))
      | ~ v2_funct_1(B_21)
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_28,plain,(
    ! [A_2,C_17] :
      ( r2_hidden(k1_funct_1(k2_funct_1(A_2),C_17),k1_relat_1(A_2))
      | ~ r2_hidden(C_17,k2_relat_1(A_2))
      | ~ v1_funct_1(k2_funct_1(A_2))
      | ~ v1_relat_1(k2_funct_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_194,plain,(
    ! [D_53] :
      ( r2_hidden(k1_funct_1('#skF_6',D_53),k1_relat_1('#skF_7'))
      | ~ r2_hidden(D_53,k1_relat_1('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_64,plain,(
    ! [C_35] :
      ( k1_funct_1('#skF_7',k1_funct_1('#skF_6',C_35)) = C_35
      | ~ r2_hidden(k1_funct_1('#skF_6',C_35),k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_35,k1_relat_1('#skF_6')) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_205,plain,(
    ! [D_54] :
      ( k1_funct_1('#skF_7',k1_funct_1('#skF_6',D_54)) = D_54
      | ~ r2_hidden(D_54,k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_194,c_64])).

tff(c_209,plain,(
    ! [C_17] :
      ( k1_funct_1('#skF_7',k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),C_17))) = k1_funct_1(k2_funct_1('#skF_6'),C_17)
      | ~ r2_hidden(C_17,k2_relat_1('#skF_6'))
      | ~ v1_funct_1(k2_funct_1('#skF_6'))
      | ~ v1_relat_1(k2_funct_1('#skF_6'))
      | ~ v2_funct_1('#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_28,c_205])).

tff(c_221,plain,(
    ! [C_55] :
      ( k1_funct_1('#skF_7',k1_funct_1('#skF_6',k1_funct_1(k2_funct_1('#skF_6'),C_55))) = k1_funct_1(k2_funct_1('#skF_6'),C_55)
      | ~ r2_hidden(C_55,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_52,c_175,c_185,c_48,c_209])).

tff(c_241,plain,(
    ! [A_20] :
      ( k1_funct_1(k2_funct_1('#skF_6'),A_20) = k1_funct_1('#skF_7',A_20)
      | ~ r2_hidden(A_20,k1_relat_1('#skF_7'))
      | ~ r2_hidden(A_20,k2_relat_1('#skF_6'))
      | ~ v2_funct_1('#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_221])).

tff(c_250,plain,(
    ! [A_56] :
      ( k1_funct_1(k2_funct_1('#skF_6'),A_56) = k1_funct_1('#skF_7',A_56)
      | ~ r2_hidden(A_56,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_52,c_48,c_241])).

tff(c_261,plain,(
    ! [B_26] :
      ( k1_funct_1(k2_funct_1('#skF_6'),'#skF_5'('#skF_7',B_26)) = k1_funct_1('#skF_7','#skF_5'('#skF_7',B_26))
      | B_26 = '#skF_7'
      | k1_relat_1(B_26) != k1_relat_1('#skF_7')
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26)
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_44,c_250])).

tff(c_268,plain,(
    ! [B_26] :
      ( k1_funct_1(k2_funct_1('#skF_6'),'#skF_5'('#skF_7',B_26)) = k1_funct_1('#skF_7','#skF_5'('#skF_7',B_26))
      | B_26 = '#skF_7'
      | k1_relat_1(B_26) != k1_relat_1('#skF_7')
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_261])).

tff(c_612,plain,(
    ! [B_68,A_69] :
      ( k1_funct_1(B_68,'#skF_5'(A_69,B_68)) != k1_funct_1(A_69,'#skF_5'(A_69,B_68))
      | B_68 = A_69
      | k1_relat_1(B_68) != k1_relat_1(A_69)
      | ~ v1_funct_1(B_68)
      | ~ v1_relat_1(B_68)
      | ~ v1_funct_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_616,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | k2_funct_1('#skF_6') = '#skF_7'
    | k1_relat_1(k2_funct_1('#skF_6')) != k1_relat_1('#skF_7')
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_612])).

tff(c_627,plain,
    ( k2_funct_1('#skF_6') = '#skF_7'
    | k1_relat_1(k2_funct_1('#skF_6')) != k1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_185,c_56,c_54,c_616])).

tff(c_628,plain,(
    k1_relat_1(k2_funct_1('#skF_6')) != k1_relat_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_627])).

tff(c_631,plain,
    ( k2_relat_1('#skF_6') != k1_relat_1('#skF_7')
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_628])).

tff(c_634,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_52,c_48,c_631])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:10:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.41  
% 2.74/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.42  %$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 2.74/1.42  
% 2.74/1.42  %Foreground sorts:
% 2.74/1.42  
% 2.74/1.42  
% 2.74/1.42  %Background operators:
% 2.74/1.42  
% 2.74/1.42  
% 2.74/1.42  %Foreground operators:
% 2.74/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.74/1.42  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.74/1.42  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.74/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.74/1.42  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.74/1.42  tff('#skF_7', type, '#skF_7': $i).
% 2.74/1.42  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.74/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.74/1.42  tff('#skF_6', type, '#skF_6': $i).
% 2.74/1.42  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.74/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.74/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.74/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.74/1.42  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.74/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.74/1.42  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.74/1.42  
% 2.74/1.43  tff(f_132, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((((v2_funct_1(A) & (k1_relat_1(A) = k2_relat_1(B))) & (k2_relat_1(A) = k1_relat_1(B))) & (![C, D]: ((r2_hidden(C, k1_relat_1(A)) & r2_hidden(D, k1_relat_1(B))) => ((k1_funct_1(A, C) = D) <=> (k1_funct_1(B, D) = C))))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_funct_1)).
% 2.74/1.43  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 2.74/1.43  tff(f_33, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.74/1.43  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k2_funct_1(A)) <=> ((k1_relat_1(B) = k2_relat_1(A)) & (![C, D]: (((r2_hidden(C, k2_relat_1(A)) & (D = k1_funct_1(B, C))) => (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))) & ((r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D))) => (r2_hidden(C, k2_relat_1(A)) & (D = k1_funct_1(B, C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_funct_1)).
% 2.74/1.43  tff(f_105, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 2.74/1.43  tff(f_87, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k2_relat_1(B))) => ((A = k1_funct_1(B, k1_funct_1(k2_funct_1(B), A))) & (A = k1_funct_1(k5_relat_1(k2_funct_1(B), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_funct_1)).
% 2.74/1.43  tff(c_60, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.74/1.43  tff(c_58, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.74/1.43  tff(c_52, plain, (v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.74/1.43  tff(c_48, plain, (k2_relat_1('#skF_6')=k1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.74/1.43  tff(c_36, plain, (![A_19]: (k1_relat_1(k2_funct_1(A_19))=k2_relat_1(A_19) | ~v2_funct_1(A_19) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.74/1.43  tff(c_46, plain, (k2_funct_1('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.74/1.43  tff(c_4, plain, (![A_1]: (v1_relat_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.74/1.43  tff(c_145, plain, (![A_49, D_50]: (r2_hidden(k1_funct_1(A_49, D_50), k2_relat_1(A_49)) | ~r2_hidden(D_50, k1_relat_1(A_49)) | ~v1_funct_1(k2_funct_1(A_49)) | ~v1_relat_1(k2_funct_1(A_49)) | ~v2_funct_1(A_49) | ~v1_funct_1(A_49) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.74/1.43  tff(c_160, plain, (![D_50]: (r2_hidden(k1_funct_1('#skF_6', D_50), k1_relat_1('#skF_7')) | ~r2_hidden(D_50, k1_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_145])).
% 2.74/1.43  tff(c_164, plain, (![D_50]: (r2_hidden(k1_funct_1('#skF_6', D_50), k1_relat_1('#skF_7')) | ~r2_hidden(D_50, k1_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_52, c_160])).
% 2.74/1.43  tff(c_165, plain, (~v1_relat_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_164])).
% 2.74/1.43  tff(c_169, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_4, c_165])).
% 2.74/1.43  tff(c_173, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_169])).
% 2.74/1.43  tff(c_175, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_164])).
% 2.74/1.43  tff(c_2, plain, (![A_1]: (v1_funct_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.74/1.43  tff(c_174, plain, (![D_50]: (~v1_funct_1(k2_funct_1('#skF_6')) | r2_hidden(k1_funct_1('#skF_6', D_50), k1_relat_1('#skF_7')) | ~r2_hidden(D_50, k1_relat_1('#skF_6')))), inference(splitRight, [status(thm)], [c_164])).
% 2.74/1.43  tff(c_176, plain, (~v1_funct_1(k2_funct_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_174])).
% 2.74/1.43  tff(c_179, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2, c_176])).
% 2.74/1.43  tff(c_183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_179])).
% 2.74/1.43  tff(c_185, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(splitRight, [status(thm)], [c_174])).
% 2.74/1.43  tff(c_56, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.74/1.43  tff(c_54, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.74/1.43  tff(c_44, plain, (![A_22, B_26]: (r2_hidden('#skF_5'(A_22, B_26), k1_relat_1(A_22)) | B_26=A_22 | k1_relat_1(B_26)!=k1_relat_1(A_22) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.74/1.43  tff(c_40, plain, (![B_21, A_20]: (k1_funct_1(B_21, k1_funct_1(k2_funct_1(B_21), A_20))=A_20 | ~r2_hidden(A_20, k2_relat_1(B_21)) | ~v2_funct_1(B_21) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.74/1.43  tff(c_28, plain, (![A_2, C_17]: (r2_hidden(k1_funct_1(k2_funct_1(A_2), C_17), k1_relat_1(A_2)) | ~r2_hidden(C_17, k2_relat_1(A_2)) | ~v1_funct_1(k2_funct_1(A_2)) | ~v1_relat_1(k2_funct_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.74/1.43  tff(c_194, plain, (![D_53]: (r2_hidden(k1_funct_1('#skF_6', D_53), k1_relat_1('#skF_7')) | ~r2_hidden(D_53, k1_relat_1('#skF_6')))), inference(splitRight, [status(thm)], [c_174])).
% 2.74/1.43  tff(c_64, plain, (![C_35]: (k1_funct_1('#skF_7', k1_funct_1('#skF_6', C_35))=C_35 | ~r2_hidden(k1_funct_1('#skF_6', C_35), k1_relat_1('#skF_7')) | ~r2_hidden(C_35, k1_relat_1('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.74/1.43  tff(c_205, plain, (![D_54]: (k1_funct_1('#skF_7', k1_funct_1('#skF_6', D_54))=D_54 | ~r2_hidden(D_54, k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_194, c_64])).
% 2.74/1.43  tff(c_209, plain, (![C_17]: (k1_funct_1('#skF_7', k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), C_17)))=k1_funct_1(k2_funct_1('#skF_6'), C_17) | ~r2_hidden(C_17, k2_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_28, c_205])).
% 2.74/1.43  tff(c_221, plain, (![C_55]: (k1_funct_1('#skF_7', k1_funct_1('#skF_6', k1_funct_1(k2_funct_1('#skF_6'), C_55)))=k1_funct_1(k2_funct_1('#skF_6'), C_55) | ~r2_hidden(C_55, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_52, c_175, c_185, c_48, c_209])).
% 2.74/1.43  tff(c_241, plain, (![A_20]: (k1_funct_1(k2_funct_1('#skF_6'), A_20)=k1_funct_1('#skF_7', A_20) | ~r2_hidden(A_20, k1_relat_1('#skF_7')) | ~r2_hidden(A_20, k2_relat_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_221])).
% 2.74/1.43  tff(c_250, plain, (![A_56]: (k1_funct_1(k2_funct_1('#skF_6'), A_56)=k1_funct_1('#skF_7', A_56) | ~r2_hidden(A_56, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_52, c_48, c_241])).
% 2.74/1.43  tff(c_261, plain, (![B_26]: (k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'('#skF_7', B_26))=k1_funct_1('#skF_7', '#skF_5'('#skF_7', B_26)) | B_26='#skF_7' | k1_relat_1(B_26)!=k1_relat_1('#skF_7') | ~v1_funct_1(B_26) | ~v1_relat_1(B_26) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_44, c_250])).
% 2.74/1.43  tff(c_268, plain, (![B_26]: (k1_funct_1(k2_funct_1('#skF_6'), '#skF_5'('#skF_7', B_26))=k1_funct_1('#skF_7', '#skF_5'('#skF_7', B_26)) | B_26='#skF_7' | k1_relat_1(B_26)!=k1_relat_1('#skF_7') | ~v1_funct_1(B_26) | ~v1_relat_1(B_26))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_261])).
% 2.74/1.43  tff(c_612, plain, (![B_68, A_69]: (k1_funct_1(B_68, '#skF_5'(A_69, B_68))!=k1_funct_1(A_69, '#skF_5'(A_69, B_68)) | B_68=A_69 | k1_relat_1(B_68)!=k1_relat_1(A_69) | ~v1_funct_1(B_68) | ~v1_relat_1(B_68) | ~v1_funct_1(A_69) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.74/1.43  tff(c_616, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | k2_funct_1('#skF_6')='#skF_7' | k1_relat_1(k2_funct_1('#skF_6'))!=k1_relat_1('#skF_7') | ~v1_funct_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_268, c_612])).
% 2.74/1.43  tff(c_627, plain, (k2_funct_1('#skF_6')='#skF_7' | k1_relat_1(k2_funct_1('#skF_6'))!=k1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_175, c_185, c_56, c_54, c_616])).
% 2.74/1.43  tff(c_628, plain, (k1_relat_1(k2_funct_1('#skF_6'))!=k1_relat_1('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_46, c_627])).
% 2.74/1.43  tff(c_631, plain, (k2_relat_1('#skF_6')!=k1_relat_1('#skF_7') | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_36, c_628])).
% 2.74/1.43  tff(c_634, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_52, c_48, c_631])).
% 2.74/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.43  
% 2.74/1.43  Inference rules
% 2.74/1.43  ----------------------
% 2.74/1.43  #Ref     : 1
% 2.74/1.43  #Sup     : 120
% 2.74/1.43  #Fact    : 0
% 2.74/1.43  #Define  : 0
% 2.74/1.43  #Split   : 4
% 2.74/1.43  #Chain   : 0
% 2.74/1.43  #Close   : 0
% 2.74/1.43  
% 2.74/1.43  Ordering : KBO
% 2.74/1.43  
% 2.74/1.43  Simplification rules
% 2.74/1.43  ----------------------
% 2.74/1.43  #Subsume      : 23
% 2.74/1.43  #Demod        : 171
% 2.74/1.43  #Tautology    : 41
% 2.74/1.43  #SimpNegUnit  : 1
% 2.74/1.43  #BackRed      : 0
% 2.74/1.43  
% 2.74/1.43  #Partial instantiations: 0
% 2.74/1.43  #Strategies tried      : 1
% 2.74/1.43  
% 2.74/1.43  Timing (in seconds)
% 2.74/1.43  ----------------------
% 2.74/1.43  Preprocessing        : 0.33
% 2.74/1.43  Parsing              : 0.16
% 2.74/1.43  CNF conversion       : 0.03
% 2.74/1.43  Main loop            : 0.32
% 2.74/1.43  Inferencing          : 0.11
% 2.74/1.43  Reduction            : 0.10
% 2.74/1.43  Demodulation         : 0.07
% 2.74/1.43  BG Simplification    : 0.03
% 2.74/1.43  Subsumption          : 0.07
% 2.74/1.43  Abstraction          : 0.02
% 2.74/1.43  MUC search           : 0.00
% 2.74/1.43  Cooper               : 0.00
% 2.74/1.43  Total                : 0.67
% 2.74/1.44  Index Insertion      : 0.00
% 2.74/1.44  Index Deletion       : 0.00
% 2.74/1.44  Index Matching       : 0.00
% 2.74/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
