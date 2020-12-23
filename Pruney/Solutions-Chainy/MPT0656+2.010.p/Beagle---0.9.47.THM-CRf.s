%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:02 EST 2020

% Result     : Theorem 5.09s
% Output     : CNFRefutation 5.09s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 128 expanded)
%              Number of leaves         :   26 (  58 expanded)
%              Depth                    :    9
%              Number of atoms          :  135 ( 364 expanded)
%              Number of equality atoms :   44 ( 124 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_112,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( v2_funct_1(A)
                & k2_relat_1(A) = k1_relat_1(B)
                & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
             => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

tff(f_67,axiom,(
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

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_94,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_49,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
           => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(c_30,plain,(
    k2_funct_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_40,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_44,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_42,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_36,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_158,plain,(
    ! [A_30] :
      ( k4_relat_1(A_30) = k2_funct_1(A_30)
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_161,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_158])).

tff(c_164,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_161])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_relat_1(k4_relat_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_174,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_2])).

tff(c_182,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_174])).

tff(c_32,plain,(
    k6_relat_1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_4,plain,(
    ! [A_2] :
      ( k2_relat_1(k4_relat_1(A_2)) = k1_relat_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_168,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_4])).

tff(c_178,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_168])).

tff(c_16,plain,(
    ! [A_13] :
      ( k5_relat_1(A_13,k6_relat_1(k2_relat_1(A_13))) = A_13
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_210,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k6_relat_1(k1_relat_1('#skF_1'))) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_16])).

tff(c_214,plain,(
    k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_32,c_210])).

tff(c_34,plain,(
    k2_relat_1('#skF_1') = k1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_26,plain,(
    ! [A_19] :
      ( k5_relat_1(k2_funct_1(A_19),A_19) = k6_relat_1(k2_relat_1(A_19))
      | ~ v2_funct_1(A_19)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_396,plain,(
    ! [A_42,B_43,C_44] :
      ( k5_relat_1(k5_relat_1(A_42,B_43),C_44) = k5_relat_1(A_42,k5_relat_1(B_43,C_44))
      | ~ v1_relat_1(C_44)
      | ~ v1_relat_1(B_43)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3048,plain,(
    ! [A_87,C_88] :
      ( k5_relat_1(k6_relat_1(k2_relat_1(A_87)),C_88) = k5_relat_1(k2_funct_1(A_87),k5_relat_1(A_87,C_88))
      | ~ v1_relat_1(C_88)
      | ~ v1_relat_1(A_87)
      | ~ v1_relat_1(k2_funct_1(A_87))
      | ~ v2_funct_1(A_87)
      | ~ v1_funct_1(A_87)
      | ~ v1_relat_1(A_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_396])).

tff(c_3341,plain,(
    ! [C_88] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_88) = k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_88))
      | ~ v1_relat_1(C_88)
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v2_funct_1('#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_3048])).

tff(c_3530,plain,(
    ! [C_89] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_89) = k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_89))
      | ~ v1_relat_1(C_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_36,c_182,c_44,c_3341])).

tff(c_20,plain,(
    ! [A_15] : v1_relat_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22,plain,(
    ! [A_15] : v1_funct_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_10,plain,(
    ! [A_10] : k1_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    ! [A_10] : k2_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_110,plain,(
    ! [A_28] :
      ( k5_relat_1(A_28,k6_relat_1(k2_relat_1(A_28))) = A_28
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_128,plain,(
    ! [A_10] :
      ( k5_relat_1(k6_relat_1(A_10),k6_relat_1(A_10)) = k6_relat_1(A_10)
      | ~ v1_relat_1(k6_relat_1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_110])).

tff(c_136,plain,(
    ! [A_10] : k5_relat_1(k6_relat_1(A_10),k6_relat_1(A_10)) = k6_relat_1(A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_128])).

tff(c_603,plain,(
    ! [B_46,A_47] :
      ( r1_tarski(k2_relat_1(B_46),k1_relat_1(A_47))
      | k1_relat_1(k5_relat_1(B_46,A_47)) != k1_relat_1(B_46)
      | ~ v1_funct_1(B_46)
      | ~ v1_relat_1(B_46)
      | ~ v1_funct_1(A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_630,plain,(
    ! [A_10,A_47] :
      ( r1_tarski(A_10,k1_relat_1(A_47))
      | k1_relat_1(k5_relat_1(k6_relat_1(A_10),A_47)) != k1_relat_1(k6_relat_1(A_10))
      | ~ v1_funct_1(k6_relat_1(A_10))
      | ~ v1_relat_1(k6_relat_1(A_10))
      | ~ v1_funct_1(A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_603])).

tff(c_990,plain,(
    ! [A_55,A_56] :
      ( r1_tarski(A_55,k1_relat_1(A_56))
      | k1_relat_1(k5_relat_1(k6_relat_1(A_55),A_56)) != A_55
      | ~ v1_funct_1(A_56)
      | ~ v1_relat_1(A_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22,c_10,c_630])).

tff(c_1016,plain,(
    ! [A_10] :
      ( r1_tarski(A_10,k1_relat_1(k6_relat_1(A_10)))
      | k1_relat_1(k6_relat_1(A_10)) != A_10
      | ~ v1_funct_1(k6_relat_1(A_10))
      | ~ v1_relat_1(k6_relat_1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_990])).

tff(c_1042,plain,(
    ! [A_57] : r1_tarski(A_57,A_57) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22,c_10,c_10,c_1016])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( k5_relat_1(k6_relat_1(A_11),B_12) = B_12
      | ~ r1_tarski(k1_relat_1(B_12),A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1047,plain,(
    ! [B_12] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(B_12)),B_12) = B_12
      | ~ v1_relat_1(B_12) ) ),
    inference(resolution,[status(thm)],[c_1042,c_14])).

tff(c_3577,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3530,c_1047])).

tff(c_3698,plain,(
    k2_funct_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_214,c_3577])).

tff(c_3700,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_3698])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:22:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.09/1.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.09/1.95  
% 5.09/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.09/1.95  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 5.09/1.95  
% 5.09/1.95  %Foreground sorts:
% 5.09/1.95  
% 5.09/1.95  
% 5.09/1.95  %Background operators:
% 5.09/1.95  
% 5.09/1.95  
% 5.09/1.95  %Foreground operators:
% 5.09/1.95  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.09/1.95  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.09/1.95  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.09/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.09/1.95  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.09/1.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.09/1.95  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.09/1.95  tff('#skF_2', type, '#skF_2': $i).
% 5.09/1.95  tff('#skF_1', type, '#skF_1': $i).
% 5.09/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.09/1.95  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.09/1.95  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.09/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.09/1.95  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.09/1.95  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 5.09/1.95  
% 5.09/1.97  tff(f_112, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 5.09/1.97  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 5.09/1.97  tff(f_29, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 5.09/1.97  tff(f_35, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 5.09/1.97  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 5.09/1.97  tff(f_94, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 5.09/1.97  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 5.09/1.97  tff(f_71, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 5.09/1.97  tff(f_49, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 5.09/1.97  tff(f_84, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(k5_relat_1(B, A)) = k1_relat_1(B)) => r1_tarski(k2_relat_1(B), k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_funct_1)).
% 5.09/1.97  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 5.09/1.97  tff(c_30, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.09/1.97  tff(c_40, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.09/1.97  tff(c_44, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.09/1.97  tff(c_42, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.09/1.97  tff(c_36, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.09/1.97  tff(c_158, plain, (![A_30]: (k4_relat_1(A_30)=k2_funct_1(A_30) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.09/1.97  tff(c_161, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_36, c_158])).
% 5.09/1.97  tff(c_164, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_161])).
% 5.09/1.97  tff(c_2, plain, (![A_1]: (v1_relat_1(k4_relat_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.09/1.97  tff(c_174, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_164, c_2])).
% 5.09/1.97  tff(c_182, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_174])).
% 5.09/1.97  tff(c_32, plain, (k6_relat_1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.09/1.97  tff(c_4, plain, (![A_2]: (k2_relat_1(k4_relat_1(A_2))=k1_relat_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.09/1.97  tff(c_168, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_164, c_4])).
% 5.09/1.97  tff(c_178, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_168])).
% 5.09/1.97  tff(c_16, plain, (![A_13]: (k5_relat_1(A_13, k6_relat_1(k2_relat_1(A_13)))=A_13 | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.09/1.97  tff(c_210, plain, (k5_relat_1(k2_funct_1('#skF_1'), k6_relat_1(k1_relat_1('#skF_1')))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_178, c_16])).
% 5.09/1.97  tff(c_214, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_182, c_32, c_210])).
% 5.09/1.97  tff(c_34, plain, (k2_relat_1('#skF_1')=k1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.09/1.97  tff(c_26, plain, (![A_19]: (k5_relat_1(k2_funct_1(A_19), A_19)=k6_relat_1(k2_relat_1(A_19)) | ~v2_funct_1(A_19) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.09/1.97  tff(c_396, plain, (![A_42, B_43, C_44]: (k5_relat_1(k5_relat_1(A_42, B_43), C_44)=k5_relat_1(A_42, k5_relat_1(B_43, C_44)) | ~v1_relat_1(C_44) | ~v1_relat_1(B_43) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.09/1.97  tff(c_3048, plain, (![A_87, C_88]: (k5_relat_1(k6_relat_1(k2_relat_1(A_87)), C_88)=k5_relat_1(k2_funct_1(A_87), k5_relat_1(A_87, C_88)) | ~v1_relat_1(C_88) | ~v1_relat_1(A_87) | ~v1_relat_1(k2_funct_1(A_87)) | ~v2_funct_1(A_87) | ~v1_funct_1(A_87) | ~v1_relat_1(A_87))), inference(superposition, [status(thm), theory('equality')], [c_26, c_396])).
% 5.09/1.97  tff(c_3341, plain, (![C_88]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_88)=k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_88)) | ~v1_relat_1(C_88) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_3048])).
% 5.09/1.97  tff(c_3530, plain, (![C_89]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_89)=k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_89)) | ~v1_relat_1(C_89))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_36, c_182, c_44, c_3341])).
% 5.09/1.97  tff(c_20, plain, (![A_15]: (v1_relat_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.09/1.97  tff(c_22, plain, (![A_15]: (v1_funct_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.09/1.97  tff(c_10, plain, (![A_10]: (k1_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.09/1.97  tff(c_12, plain, (![A_10]: (k2_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.09/1.97  tff(c_110, plain, (![A_28]: (k5_relat_1(A_28, k6_relat_1(k2_relat_1(A_28)))=A_28 | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.09/1.97  tff(c_128, plain, (![A_10]: (k5_relat_1(k6_relat_1(A_10), k6_relat_1(A_10))=k6_relat_1(A_10) | ~v1_relat_1(k6_relat_1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_110])).
% 5.09/1.97  tff(c_136, plain, (![A_10]: (k5_relat_1(k6_relat_1(A_10), k6_relat_1(A_10))=k6_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_128])).
% 5.09/1.97  tff(c_603, plain, (![B_46, A_47]: (r1_tarski(k2_relat_1(B_46), k1_relat_1(A_47)) | k1_relat_1(k5_relat_1(B_46, A_47))!=k1_relat_1(B_46) | ~v1_funct_1(B_46) | ~v1_relat_1(B_46) | ~v1_funct_1(A_47) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.09/1.97  tff(c_630, plain, (![A_10, A_47]: (r1_tarski(A_10, k1_relat_1(A_47)) | k1_relat_1(k5_relat_1(k6_relat_1(A_10), A_47))!=k1_relat_1(k6_relat_1(A_10)) | ~v1_funct_1(k6_relat_1(A_10)) | ~v1_relat_1(k6_relat_1(A_10)) | ~v1_funct_1(A_47) | ~v1_relat_1(A_47))), inference(superposition, [status(thm), theory('equality')], [c_12, c_603])).
% 5.09/1.97  tff(c_990, plain, (![A_55, A_56]: (r1_tarski(A_55, k1_relat_1(A_56)) | k1_relat_1(k5_relat_1(k6_relat_1(A_55), A_56))!=A_55 | ~v1_funct_1(A_56) | ~v1_relat_1(A_56))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22, c_10, c_630])).
% 5.09/1.97  tff(c_1016, plain, (![A_10]: (r1_tarski(A_10, k1_relat_1(k6_relat_1(A_10))) | k1_relat_1(k6_relat_1(A_10))!=A_10 | ~v1_funct_1(k6_relat_1(A_10)) | ~v1_relat_1(k6_relat_1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_136, c_990])).
% 5.09/1.97  tff(c_1042, plain, (![A_57]: (r1_tarski(A_57, A_57))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22, c_10, c_10, c_1016])).
% 5.09/1.97  tff(c_14, plain, (![A_11, B_12]: (k5_relat_1(k6_relat_1(A_11), B_12)=B_12 | ~r1_tarski(k1_relat_1(B_12), A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.09/1.97  tff(c_1047, plain, (![B_12]: (k5_relat_1(k6_relat_1(k1_relat_1(B_12)), B_12)=B_12 | ~v1_relat_1(B_12))), inference(resolution, [status(thm)], [c_1042, c_14])).
% 5.09/1.97  tff(c_3577, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))='#skF_2' | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3530, c_1047])).
% 5.09/1.97  tff(c_3698, plain, (k2_funct_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_214, c_3577])).
% 5.09/1.97  tff(c_3700, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_3698])).
% 5.09/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.09/1.97  
% 5.09/1.97  Inference rules
% 5.09/1.97  ----------------------
% 5.09/1.97  #Ref     : 0
% 5.09/1.97  #Sup     : 759
% 5.09/1.97  #Fact    : 0
% 5.09/1.97  #Define  : 0
% 5.09/1.97  #Split   : 8
% 5.09/1.97  #Chain   : 0
% 5.09/1.97  #Close   : 0
% 5.09/1.97  
% 5.09/1.97  Ordering : KBO
% 5.09/1.97  
% 5.09/1.97  Simplification rules
% 5.09/1.97  ----------------------
% 5.09/1.97  #Subsume      : 45
% 5.09/1.97  #Demod        : 1494
% 5.09/1.97  #Tautology    : 355
% 5.09/1.97  #SimpNegUnit  : 10
% 5.09/1.97  #BackRed      : 0
% 5.09/1.97  
% 5.09/1.97  #Partial instantiations: 0
% 5.09/1.97  #Strategies tried      : 1
% 5.09/1.97  
% 5.09/1.97  Timing (in seconds)
% 5.09/1.97  ----------------------
% 5.09/1.97  Preprocessing        : 0.32
% 5.09/1.97  Parsing              : 0.17
% 5.09/1.97  CNF conversion       : 0.02
% 5.09/1.97  Main loop            : 0.89
% 5.09/1.97  Inferencing          : 0.31
% 5.09/1.97  Reduction            : 0.35
% 5.09/1.97  Demodulation         : 0.27
% 5.09/1.97  BG Simplification    : 0.04
% 5.09/1.97  Subsumption          : 0.14
% 5.09/1.97  Abstraction          : 0.05
% 5.09/1.97  MUC search           : 0.00
% 5.09/1.97  Cooper               : 0.00
% 5.09/1.97  Total                : 1.24
% 5.09/1.97  Index Insertion      : 0.00
% 5.09/1.97  Index Deletion       : 0.00
% 5.09/1.97  Index Matching       : 0.00
% 5.09/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
