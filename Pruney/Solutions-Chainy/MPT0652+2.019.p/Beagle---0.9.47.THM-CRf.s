%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:55 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 146 expanded)
%              Number of leaves         :   20 (  62 expanded)
%              Depth                    :    8
%              Number of atoms          :  136 ( 431 expanded)
%              Number of equality atoms :   31 ( 133 expanded)
%              Maximal formula depth    :   10 (   4 average)
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

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
            & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_26,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_24,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_16,plain,(
    ! [A_10] :
      ( v1_relat_1(k2_funct_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_181,plain,(
    ! [A_28] :
      ( k2_relat_1(k2_funct_1(A_28)) = k1_relat_1(A_28)
      | ~ v2_funct_1(A_28)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_8,plain,(
    ! [A_3] :
      ( k10_relat_1(A_3,k2_relat_1(A_3)) = k1_relat_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_218,plain,(
    ! [A_33] :
      ( k10_relat_1(k2_funct_1(A_33),k1_relat_1(A_33)) = k1_relat_1(k2_funct_1(A_33))
      | ~ v1_relat_1(k2_funct_1(A_33))
      | ~ v2_funct_1(A_33)
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_8])).

tff(c_10,plain,(
    ! [A_4,B_6] :
      ( k10_relat_1(A_4,k1_relat_1(B_6)) = k1_relat_1(k5_relat_1(A_4,B_6))
      | ~ v1_relat_1(B_6)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_259,plain,(
    ! [A_36] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(A_36),A_36)) = k1_relat_1(k2_funct_1(A_36))
      | ~ v1_relat_1(A_36)
      | ~ v1_relat_1(k2_funct_1(A_36))
      | ~ v1_relat_1(k2_funct_1(A_36))
      | ~ v2_funct_1(A_36)
      | ~ v1_funct_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_10])).

tff(c_20,plain,(
    ! [A_11] :
      ( k1_relat_1(k2_funct_1(A_11)) = k2_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_59,plain,(
    ! [A_19] :
      ( k2_relat_1(k2_funct_1(A_19)) = k1_relat_1(A_19)
      | ~ v2_funct_1(A_19)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_90,plain,(
    ! [A_24] :
      ( k10_relat_1(k2_funct_1(A_24),k1_relat_1(A_24)) = k1_relat_1(k2_funct_1(A_24))
      | ~ v1_relat_1(k2_funct_1(A_24))
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_8])).

tff(c_127,plain,(
    ! [B_27] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(B_27),B_27)) = k1_relat_1(k2_funct_1(B_27))
      | ~ v1_relat_1(k2_funct_1(B_27))
      | ~ v2_funct_1(B_27)
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27)
      | ~ v1_relat_1(B_27)
      | ~ v1_relat_1(k2_funct_1(B_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_90])).

tff(c_22,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_58,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_146,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_58])).

tff(c_156,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_26,c_24,c_146])).

tff(c_158,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_161,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_158])).

tff(c_165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_161])).

tff(c_166,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_170,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_166])).

tff(c_174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_170])).

tff(c_176,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) = k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_278,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_176])).

tff(c_291,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_28,c_278])).

tff(c_295,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_291])).

tff(c_298,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_295])).

tff(c_302,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_298])).

tff(c_304,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_291])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_11] :
      ( k2_relat_1(k2_funct_1(A_11)) = k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_208,plain,(
    ! [B_31,A_32] :
      ( k2_relat_1(k5_relat_1(B_31,A_32)) = k2_relat_1(A_32)
      | ~ r1_tarski(k1_relat_1(A_32),k2_relat_1(B_31))
      | ~ v1_relat_1(B_31)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_305,plain,(
    ! [A_37,A_38] :
      ( k2_relat_1(k5_relat_1(k2_funct_1(A_37),A_38)) = k2_relat_1(A_38)
      | ~ r1_tarski(k1_relat_1(A_38),k1_relat_1(A_37))
      | ~ v1_relat_1(k2_funct_1(A_37))
      | ~ v1_relat_1(A_38)
      | ~ v2_funct_1(A_37)
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_208])).

tff(c_451,plain,(
    ! [A_41] :
      ( k2_relat_1(k5_relat_1(k2_funct_1(A_41),A_41)) = k2_relat_1(A_41)
      | ~ v1_relat_1(k2_funct_1(A_41))
      | ~ v2_funct_1(A_41)
      | ~ v1_funct_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(resolution,[status(thm)],[c_6,c_305])).

tff(c_175,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_463,plain,
    ( ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_451,c_175])).

tff(c_474,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_304,c_463])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:18:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.31  
% 2.13/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.31  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 2.13/1.31  
% 2.13/1.31  %Foreground sorts:
% 2.13/1.31  
% 2.13/1.31  
% 2.13/1.31  %Background operators:
% 2.13/1.31  
% 2.13/1.31  
% 2.13/1.31  %Foreground operators:
% 2.13/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.13/1.31  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.13/1.31  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.13/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.31  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.13/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.13/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.13/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.31  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.13/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.13/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.13/1.31  
% 2.57/1.33  tff(f_80, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_funct_1)).
% 2.57/1.33  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.57/1.33  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 2.57/1.33  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.57/1.33  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 2.57/1.33  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.57/1.33  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 2.57/1.33  tff(c_28, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.57/1.33  tff(c_26, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.57/1.33  tff(c_24, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.57/1.33  tff(c_16, plain, (![A_10]: (v1_relat_1(k2_funct_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.57/1.33  tff(c_181, plain, (![A_28]: (k2_relat_1(k2_funct_1(A_28))=k1_relat_1(A_28) | ~v2_funct_1(A_28) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.57/1.33  tff(c_8, plain, (![A_3]: (k10_relat_1(A_3, k2_relat_1(A_3))=k1_relat_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.57/1.33  tff(c_218, plain, (![A_33]: (k10_relat_1(k2_funct_1(A_33), k1_relat_1(A_33))=k1_relat_1(k2_funct_1(A_33)) | ~v1_relat_1(k2_funct_1(A_33)) | ~v2_funct_1(A_33) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(superposition, [status(thm), theory('equality')], [c_181, c_8])).
% 2.57/1.33  tff(c_10, plain, (![A_4, B_6]: (k10_relat_1(A_4, k1_relat_1(B_6))=k1_relat_1(k5_relat_1(A_4, B_6)) | ~v1_relat_1(B_6) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.57/1.33  tff(c_259, plain, (![A_36]: (k1_relat_1(k5_relat_1(k2_funct_1(A_36), A_36))=k1_relat_1(k2_funct_1(A_36)) | ~v1_relat_1(A_36) | ~v1_relat_1(k2_funct_1(A_36)) | ~v1_relat_1(k2_funct_1(A_36)) | ~v2_funct_1(A_36) | ~v1_funct_1(A_36) | ~v1_relat_1(A_36))), inference(superposition, [status(thm), theory('equality')], [c_218, c_10])).
% 2.57/1.33  tff(c_20, plain, (![A_11]: (k1_relat_1(k2_funct_1(A_11))=k2_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.57/1.33  tff(c_59, plain, (![A_19]: (k2_relat_1(k2_funct_1(A_19))=k1_relat_1(A_19) | ~v2_funct_1(A_19) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.57/1.33  tff(c_90, plain, (![A_24]: (k10_relat_1(k2_funct_1(A_24), k1_relat_1(A_24))=k1_relat_1(k2_funct_1(A_24)) | ~v1_relat_1(k2_funct_1(A_24)) | ~v2_funct_1(A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(superposition, [status(thm), theory('equality')], [c_59, c_8])).
% 2.57/1.33  tff(c_127, plain, (![B_27]: (k1_relat_1(k5_relat_1(k2_funct_1(B_27), B_27))=k1_relat_1(k2_funct_1(B_27)) | ~v1_relat_1(k2_funct_1(B_27)) | ~v2_funct_1(B_27) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27) | ~v1_relat_1(B_27) | ~v1_relat_1(k2_funct_1(B_27)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_90])).
% 2.57/1.33  tff(c_22, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1') | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.57/1.33  tff(c_58, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_22])).
% 2.57/1.33  tff(c_146, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_127, c_58])).
% 2.57/1.33  tff(c_156, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_26, c_24, c_146])).
% 2.57/1.33  tff(c_158, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_156])).
% 2.57/1.33  tff(c_161, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_16, c_158])).
% 2.57/1.33  tff(c_165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_161])).
% 2.57/1.33  tff(c_166, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_156])).
% 2.57/1.33  tff(c_170, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_20, c_166])).
% 2.57/1.33  tff(c_174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_170])).
% 2.57/1.33  tff(c_176, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_22])).
% 2.57/1.33  tff(c_278, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_259, c_176])).
% 2.57/1.33  tff(c_291, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_28, c_278])).
% 2.57/1.33  tff(c_295, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_291])).
% 2.57/1.33  tff(c_298, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_16, c_295])).
% 2.57/1.33  tff(c_302, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_298])).
% 2.57/1.33  tff(c_304, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_291])).
% 2.57/1.33  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.57/1.33  tff(c_18, plain, (![A_11]: (k2_relat_1(k2_funct_1(A_11))=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.57/1.33  tff(c_208, plain, (![B_31, A_32]: (k2_relat_1(k5_relat_1(B_31, A_32))=k2_relat_1(A_32) | ~r1_tarski(k1_relat_1(A_32), k2_relat_1(B_31)) | ~v1_relat_1(B_31) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.57/1.33  tff(c_305, plain, (![A_37, A_38]: (k2_relat_1(k5_relat_1(k2_funct_1(A_37), A_38))=k2_relat_1(A_38) | ~r1_tarski(k1_relat_1(A_38), k1_relat_1(A_37)) | ~v1_relat_1(k2_funct_1(A_37)) | ~v1_relat_1(A_38) | ~v2_funct_1(A_37) | ~v1_funct_1(A_37) | ~v1_relat_1(A_37))), inference(superposition, [status(thm), theory('equality')], [c_18, c_208])).
% 2.57/1.33  tff(c_451, plain, (![A_41]: (k2_relat_1(k5_relat_1(k2_funct_1(A_41), A_41))=k2_relat_1(A_41) | ~v1_relat_1(k2_funct_1(A_41)) | ~v2_funct_1(A_41) | ~v1_funct_1(A_41) | ~v1_relat_1(A_41))), inference(resolution, [status(thm)], [c_6, c_305])).
% 2.57/1.33  tff(c_175, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_22])).
% 2.57/1.33  tff(c_463, plain, (~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_451, c_175])).
% 2.57/1.33  tff(c_474, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_304, c_463])).
% 2.57/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.33  
% 2.57/1.33  Inference rules
% 2.57/1.33  ----------------------
% 2.57/1.33  #Ref     : 0
% 2.57/1.33  #Sup     : 108
% 2.57/1.33  #Fact    : 0
% 2.57/1.33  #Define  : 0
% 2.57/1.33  #Split   : 4
% 2.57/1.33  #Chain   : 0
% 2.57/1.33  #Close   : 0
% 2.57/1.33  
% 2.57/1.33  Ordering : KBO
% 2.57/1.33  
% 2.57/1.33  Simplification rules
% 2.57/1.33  ----------------------
% 2.57/1.33  #Subsume      : 4
% 2.57/1.33  #Demod        : 51
% 2.57/1.33  #Tautology    : 40
% 2.57/1.33  #SimpNegUnit  : 0
% 2.57/1.33  #BackRed      : 0
% 2.57/1.33  
% 2.57/1.33  #Partial instantiations: 0
% 2.57/1.33  #Strategies tried      : 1
% 2.57/1.33  
% 2.57/1.33  Timing (in seconds)
% 2.57/1.33  ----------------------
% 2.57/1.33  Preprocessing        : 0.29
% 2.57/1.33  Parsing              : 0.15
% 2.57/1.33  CNF conversion       : 0.02
% 2.57/1.33  Main loop            : 0.28
% 2.57/1.33  Inferencing          : 0.10
% 2.57/1.33  Reduction            : 0.08
% 2.57/1.33  Demodulation         : 0.06
% 2.57/1.33  BG Simplification    : 0.02
% 2.57/1.33  Subsumption          : 0.06
% 2.57/1.33  Abstraction          : 0.02
% 2.57/1.33  MUC search           : 0.00
% 2.57/1.33  Cooper               : 0.00
% 2.57/1.33  Total                : 0.60
% 2.57/1.33  Index Insertion      : 0.00
% 2.57/1.33  Index Deletion       : 0.00
% 2.57/1.33  Index Matching       : 0.00
% 2.57/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
