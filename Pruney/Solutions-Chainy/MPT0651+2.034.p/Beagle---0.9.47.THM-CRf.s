%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:52 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 131 expanded)
%              Number of leaves         :   20 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :  143 ( 372 expanded)
%              Number of equality atoms :   28 ( 106 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
            & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_22,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_20,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_14,plain,(
    ! [A_12] :
      ( k2_relat_1(k2_funct_1(A_12)) = k1_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_12,plain,(
    ! [A_11] :
      ( v1_relat_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [A_1] :
      ( k10_relat_1(A_1,k2_relat_1(A_1)) = k1_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [A_12] :
      ( k1_relat_1(k2_funct_1(A_12)) = k2_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_62,plain,(
    ! [A_20,B_21] :
      ( k10_relat_1(A_20,k1_relat_1(B_21)) = k1_relat_1(k5_relat_1(A_20,B_21))
      | ~ v1_relat_1(B_21)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_108,plain,(
    ! [A_27,A_28] :
      ( k1_relat_1(k5_relat_1(A_27,k2_funct_1(A_28))) = k10_relat_1(A_27,k2_relat_1(A_28))
      | ~ v1_relat_1(k2_funct_1(A_28))
      | ~ v1_relat_1(A_27)
      | ~ v2_funct_1(A_28)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_62])).

tff(c_18,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_61,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_127,plain,
    ( k10_relat_1('#skF_1',k2_relat_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_61])).

tff(c_139,plain,
    ( k10_relat_1('#skF_1',k2_relat_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_24,c_127])).

tff(c_141,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_144,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_141])).

tff(c_148,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_144])).

tff(c_149,plain,(
    k10_relat_1('#skF_1',k2_relat_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_153,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_149])).

tff(c_157,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_153])).

tff(c_159,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_6,plain,(
    ! [A_5,B_7] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_5,B_7)),k1_relat_1(A_5))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_163,plain,
    ( r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_6])).

tff(c_170,plain,
    ( r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_163])).

tff(c_172,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_170])).

tff(c_175,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_172])).

tff(c_179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_175])).

tff(c_181,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_170])).

tff(c_45,plain,(
    ! [A_17] :
      ( k2_relat_1(k2_funct_1(A_17)) = k1_relat_1(A_17)
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_207,plain,(
    ! [A_33] :
      ( k10_relat_1(k2_funct_1(A_33),k1_relat_1(A_33)) = k1_relat_1(k2_funct_1(A_33))
      | ~ v1_relat_1(k2_funct_1(A_33))
      | ~ v2_funct_1(A_33)
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_2])).

tff(c_4,plain,(
    ! [A_2,B_4] :
      ( k10_relat_1(A_2,k1_relat_1(B_4)) = k1_relat_1(k5_relat_1(A_2,B_4))
      | ~ v1_relat_1(B_4)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_336,plain,(
    ! [A_40] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(A_40),A_40)) = k1_relat_1(k2_funct_1(A_40))
      | ~ v1_relat_1(A_40)
      | ~ v1_relat_1(k2_funct_1(A_40))
      | ~ v1_relat_1(k2_funct_1(A_40))
      | ~ v2_funct_1(A_40)
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_4])).

tff(c_57,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_18,B_19)),k1_relat_1(A_18))
      | ~ v1_relat_1(B_19)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_60,plain,(
    ! [A_12,B_19] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k2_funct_1(A_12),B_19)),k2_relat_1(A_12))
      | ~ v1_relat_1(B_19)
      | ~ v1_relat_1(k2_funct_1(A_12))
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_57])).

tff(c_801,plain,(
    ! [A_66] :
      ( r1_tarski(k1_relat_1(k2_funct_1(A_66)),k2_relat_1(A_66))
      | ~ v1_relat_1(A_66)
      | ~ v1_relat_1(k2_funct_1(A_66))
      | ~ v2_funct_1(A_66)
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66)
      | ~ v1_relat_1(A_66)
      | ~ v1_relat_1(k2_funct_1(A_66))
      | ~ v1_relat_1(k2_funct_1(A_66))
      | ~ v2_funct_1(A_66)
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_60])).

tff(c_8,plain,(
    ! [B_10,A_8] :
      ( k2_relat_1(k5_relat_1(B_10,A_8)) = k2_relat_1(A_8)
      | ~ r1_tarski(k1_relat_1(A_8),k2_relat_1(B_10))
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_827,plain,(
    ! [A_67] :
      ( k2_relat_1(k5_relat_1(A_67,k2_funct_1(A_67))) = k2_relat_1(k2_funct_1(A_67))
      | ~ v1_relat_1(k2_funct_1(A_67))
      | ~ v2_funct_1(A_67)
      | ~ v1_funct_1(A_67)
      | ~ v1_relat_1(A_67) ) ),
    inference(resolution,[status(thm)],[c_801,c_8])).

tff(c_158,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_864,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_827,c_158])).

tff(c_878,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_181,c_864])).

tff(c_883,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_878])).

tff(c_887,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_883])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:03:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.27/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.51  
% 3.27/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.51  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 3.27/1.51  
% 3.27/1.51  %Foreground sorts:
% 3.27/1.51  
% 3.27/1.51  
% 3.27/1.51  %Background operators:
% 3.27/1.51  
% 3.27/1.51  
% 3.27/1.51  %Foreground operators:
% 3.27/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.27/1.51  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.27/1.51  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.27/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.27/1.51  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.27/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.27/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.27/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.27/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.27/1.51  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.27/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.27/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.27/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.27/1.51  
% 3.27/1.53  tff(f_81, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 3.27/1.53  tff(f_70, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 3.27/1.53  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.27/1.53  tff(f_29, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 3.27/1.53  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 3.27/1.53  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 3.27/1.53  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 3.27/1.53  tff(c_24, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.27/1.53  tff(c_22, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.27/1.53  tff(c_20, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.27/1.53  tff(c_14, plain, (![A_12]: (k2_relat_1(k2_funct_1(A_12))=k1_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.27/1.53  tff(c_12, plain, (![A_11]: (v1_relat_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.27/1.53  tff(c_2, plain, (![A_1]: (k10_relat_1(A_1, k2_relat_1(A_1))=k1_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.27/1.53  tff(c_16, plain, (![A_12]: (k1_relat_1(k2_funct_1(A_12))=k2_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.27/1.53  tff(c_62, plain, (![A_20, B_21]: (k10_relat_1(A_20, k1_relat_1(B_21))=k1_relat_1(k5_relat_1(A_20, B_21)) | ~v1_relat_1(B_21) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.27/1.53  tff(c_108, plain, (![A_27, A_28]: (k1_relat_1(k5_relat_1(A_27, k2_funct_1(A_28)))=k10_relat_1(A_27, k2_relat_1(A_28)) | ~v1_relat_1(k2_funct_1(A_28)) | ~v1_relat_1(A_27) | ~v2_funct_1(A_28) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(superposition, [status(thm), theory('equality')], [c_16, c_62])).
% 3.27/1.53  tff(c_18, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.27/1.53  tff(c_61, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_18])).
% 3.27/1.53  tff(c_127, plain, (k10_relat_1('#skF_1', k2_relat_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_108, c_61])).
% 3.27/1.53  tff(c_139, plain, (k10_relat_1('#skF_1', k2_relat_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_24, c_127])).
% 3.27/1.53  tff(c_141, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_139])).
% 3.27/1.53  tff(c_144, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_12, c_141])).
% 3.27/1.53  tff(c_148, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_144])).
% 3.27/1.53  tff(c_149, plain, (k10_relat_1('#skF_1', k2_relat_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_139])).
% 3.27/1.53  tff(c_153, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2, c_149])).
% 3.27/1.53  tff(c_157, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_153])).
% 3.27/1.53  tff(c_159, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_18])).
% 3.27/1.53  tff(c_6, plain, (![A_5, B_7]: (r1_tarski(k1_relat_1(k5_relat_1(A_5, B_7)), k1_relat_1(A_5)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.27/1.53  tff(c_163, plain, (r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_159, c_6])).
% 3.27/1.53  tff(c_170, plain, (r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_163])).
% 3.27/1.53  tff(c_172, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_170])).
% 3.27/1.53  tff(c_175, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_12, c_172])).
% 3.27/1.53  tff(c_179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_175])).
% 3.27/1.53  tff(c_181, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_170])).
% 3.27/1.53  tff(c_45, plain, (![A_17]: (k2_relat_1(k2_funct_1(A_17))=k1_relat_1(A_17) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.27/1.53  tff(c_207, plain, (![A_33]: (k10_relat_1(k2_funct_1(A_33), k1_relat_1(A_33))=k1_relat_1(k2_funct_1(A_33)) | ~v1_relat_1(k2_funct_1(A_33)) | ~v2_funct_1(A_33) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(superposition, [status(thm), theory('equality')], [c_45, c_2])).
% 3.27/1.53  tff(c_4, plain, (![A_2, B_4]: (k10_relat_1(A_2, k1_relat_1(B_4))=k1_relat_1(k5_relat_1(A_2, B_4)) | ~v1_relat_1(B_4) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.27/1.53  tff(c_336, plain, (![A_40]: (k1_relat_1(k5_relat_1(k2_funct_1(A_40), A_40))=k1_relat_1(k2_funct_1(A_40)) | ~v1_relat_1(A_40) | ~v1_relat_1(k2_funct_1(A_40)) | ~v1_relat_1(k2_funct_1(A_40)) | ~v2_funct_1(A_40) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(superposition, [status(thm), theory('equality')], [c_207, c_4])).
% 3.27/1.53  tff(c_57, plain, (![A_18, B_19]: (r1_tarski(k1_relat_1(k5_relat_1(A_18, B_19)), k1_relat_1(A_18)) | ~v1_relat_1(B_19) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.27/1.53  tff(c_60, plain, (![A_12, B_19]: (r1_tarski(k1_relat_1(k5_relat_1(k2_funct_1(A_12), B_19)), k2_relat_1(A_12)) | ~v1_relat_1(B_19) | ~v1_relat_1(k2_funct_1(A_12)) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(superposition, [status(thm), theory('equality')], [c_16, c_57])).
% 3.27/1.53  tff(c_801, plain, (![A_66]: (r1_tarski(k1_relat_1(k2_funct_1(A_66)), k2_relat_1(A_66)) | ~v1_relat_1(A_66) | ~v1_relat_1(k2_funct_1(A_66)) | ~v2_funct_1(A_66) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66) | ~v1_relat_1(A_66) | ~v1_relat_1(k2_funct_1(A_66)) | ~v1_relat_1(k2_funct_1(A_66)) | ~v2_funct_1(A_66) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(superposition, [status(thm), theory('equality')], [c_336, c_60])).
% 3.27/1.53  tff(c_8, plain, (![B_10, A_8]: (k2_relat_1(k5_relat_1(B_10, A_8))=k2_relat_1(A_8) | ~r1_tarski(k1_relat_1(A_8), k2_relat_1(B_10)) | ~v1_relat_1(B_10) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.27/1.53  tff(c_827, plain, (![A_67]: (k2_relat_1(k5_relat_1(A_67, k2_funct_1(A_67)))=k2_relat_1(k2_funct_1(A_67)) | ~v1_relat_1(k2_funct_1(A_67)) | ~v2_funct_1(A_67) | ~v1_funct_1(A_67) | ~v1_relat_1(A_67))), inference(resolution, [status(thm)], [c_801, c_8])).
% 3.27/1.53  tff(c_158, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_18])).
% 3.27/1.53  tff(c_864, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_827, c_158])).
% 3.27/1.53  tff(c_878, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_181, c_864])).
% 3.27/1.53  tff(c_883, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14, c_878])).
% 3.27/1.53  tff(c_887, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_883])).
% 3.27/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.53  
% 3.27/1.53  Inference rules
% 3.27/1.53  ----------------------
% 3.27/1.53  #Ref     : 0
% 3.27/1.53  #Sup     : 236
% 3.27/1.53  #Fact    : 0
% 3.27/1.53  #Define  : 0
% 3.27/1.53  #Split   : 5
% 3.27/1.53  #Chain   : 0
% 3.27/1.53  #Close   : 0
% 3.27/1.53  
% 3.27/1.53  Ordering : KBO
% 3.27/1.53  
% 3.27/1.53  Simplification rules
% 3.27/1.53  ----------------------
% 3.27/1.53  #Subsume      : 25
% 3.27/1.53  #Demod        : 59
% 3.27/1.53  #Tautology    : 52
% 3.27/1.53  #SimpNegUnit  : 0
% 3.27/1.53  #BackRed      : 0
% 3.27/1.53  
% 3.27/1.53  #Partial instantiations: 0
% 3.27/1.53  #Strategies tried      : 1
% 3.27/1.53  
% 3.27/1.53  Timing (in seconds)
% 3.27/1.53  ----------------------
% 3.27/1.53  Preprocessing        : 0.30
% 3.27/1.53  Parsing              : 0.16
% 3.27/1.53  CNF conversion       : 0.02
% 3.27/1.53  Main loop            : 0.47
% 3.27/1.53  Inferencing          : 0.18
% 3.27/1.53  Reduction            : 0.13
% 3.27/1.53  Demodulation         : 0.09
% 3.47/1.53  BG Simplification    : 0.03
% 3.47/1.53  Subsumption          : 0.10
% 3.47/1.53  Abstraction          : 0.03
% 3.47/1.53  MUC search           : 0.00
% 3.47/1.53  Cooper               : 0.00
% 3.47/1.53  Total                : 0.80
% 3.47/1.53  Index Insertion      : 0.00
% 3.47/1.53  Index Deletion       : 0.00
% 3.47/1.53  Index Matching       : 0.00
% 3.47/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
