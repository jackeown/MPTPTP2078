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
% DateTime   : Thu Dec  3 10:04:04 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 180 expanded)
%              Number of leaves         :   23 (  74 expanded)
%              Depth                    :   16
%              Number of atoms          :  132 ( 606 expanded)
%              Number of equality atoms :   49 ( 222 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_125,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( v2_funct_1(A)
                & k2_relat_1(B) = k1_relat_1(A)
                & k5_relat_1(B,A) = k6_relat_1(k2_relat_1(A)) )
             => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_48,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_90,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( ? [B] :
            ( v1_relat_1(B)
            & v1_funct_1(B)
            & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
       => v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).

tff(f_107,axiom,(
    ! [A] :
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

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(c_30,plain,(
    k2_funct_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_40,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_44,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_42,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_36,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_117,plain,(
    ! [A_28] :
      ( k4_relat_1(A_28) = k2_funct_1(A_28)
      | ~ v2_funct_1(A_28)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_126,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_117])).

tff(c_135,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_126])).

tff(c_38,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_32,plain,(
    k6_relat_1(k2_relat_1('#skF_1')) = k5_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_12,plain,(
    ! [A_7] : k1_relat_1(k6_relat_1(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_77,plain,(
    k1_relat_1(k5_relat_1('#skF_2','#skF_1')) = k2_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_12])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    k2_relat_1('#skF_2') = k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_159,plain,(
    ! [A_30,B_31] :
      ( k1_relat_1(k5_relat_1(A_30,B_31)) = k1_relat_1(A_30)
      | ~ r1_tarski(k2_relat_1(A_30),k1_relat_1(B_31))
      | ~ v1_relat_1(B_31)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_174,plain,(
    ! [B_31] :
      ( k1_relat_1(k5_relat_1('#skF_2',B_31)) = k1_relat_1('#skF_2')
      | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1(B_31))
      | ~ v1_relat_1(B_31)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_159])).

tff(c_256,plain,(
    ! [B_37] :
      ( k1_relat_1(k5_relat_1('#skF_2',B_37)) = k1_relat_1('#skF_2')
      | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1(B_37))
      | ~ v1_relat_1(B_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_174])).

tff(c_275,plain,
    ( k1_relat_1(k5_relat_1('#skF_2','#skF_1')) = k1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_256])).

tff(c_282,plain,(
    k2_relat_1('#skF_1') = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_77,c_275])).

tff(c_287,plain,(
    k6_relat_1(k1_relat_1('#skF_2')) = k5_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_32])).

tff(c_26,plain,(
    ! [A_13,B_15] :
      ( v2_funct_1(A_13)
      | k6_relat_1(k1_relat_1(A_13)) != k5_relat_1(A_13,B_15)
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_335,plain,(
    ! [B_15] :
      ( v2_funct_1('#skF_2')
      | k5_relat_1('#skF_2',B_15) != k5_relat_1('#skF_2','#skF_1')
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_26])).

tff(c_358,plain,(
    ! [B_15] :
      ( v2_funct_1('#skF_2')
      | k5_relat_1('#skF_2',B_15) != k5_relat_1('#skF_2','#skF_1')
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_335])).

tff(c_449,plain,(
    ! [B_42] :
      ( k5_relat_1('#skF_2',B_42) != k5_relat_1('#skF_2','#skF_1')
      | ~ v1_funct_1(B_42)
      | ~ v1_relat_1(B_42) ) ),
    inference(splitLeft,[status(thm)],[c_358])).

tff(c_461,plain,(
    ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_449])).

tff(c_470,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_461])).

tff(c_471,plain,(
    v2_funct_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_358])).

tff(c_761,plain,(
    ! [A_52,B_53] :
      ( k2_funct_1(A_52) = B_53
      | k6_relat_1(k1_relat_1(A_52)) != k5_relat_1(A_52,B_53)
      | k2_relat_1(A_52) != k1_relat_1(B_53)
      | ~ v2_funct_1(A_52)
      | ~ v1_funct_1(B_53)
      | ~ v1_relat_1(B_53)
      | ~ v1_funct_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_779,plain,(
    ! [B_53] :
      ( k2_funct_1('#skF_2') = B_53
      | k5_relat_1('#skF_2',B_53) != k5_relat_1('#skF_2','#skF_1')
      | k2_relat_1('#skF_2') != k1_relat_1(B_53)
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1(B_53)
      | ~ v1_relat_1(B_53)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_761])).

tff(c_842,plain,(
    ! [B_58] :
      ( k2_funct_1('#skF_2') = B_58
      | k5_relat_1('#skF_2',B_58) != k5_relat_1('#skF_2','#skF_1')
      | k1_relat_1(B_58) != k1_relat_1('#skF_1')
      | ~ v1_funct_1(B_58)
      | ~ v1_relat_1(B_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_471,c_34,c_779])).

tff(c_854,plain,
    ( k2_funct_1('#skF_2') = '#skF_1'
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_842])).

tff(c_864,plain,(
    k2_funct_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_854])).

tff(c_16,plain,(
    ! [A_8] :
      ( k4_relat_1(A_8) = k2_funct_1(A_8)
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_474,plain,
    ( k4_relat_1('#skF_2') = k2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_471,c_16])).

tff(c_477,plain,(
    k4_relat_1('#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_474])).

tff(c_867,plain,(
    k4_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_864,c_477])).

tff(c_8,plain,(
    ! [A_3] :
      ( k4_relat_1(k4_relat_1(A_3)) = A_3
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_875,plain,
    ( k4_relat_1('#skF_1') = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_867,c_8])).

tff(c_879,plain,(
    k2_funct_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_135,c_875])).

tff(c_881,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_879])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:41:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.48  
% 3.22/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.48  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.22/1.48  
% 3.22/1.48  %Foreground sorts:
% 3.22/1.48  
% 3.22/1.48  
% 3.22/1.48  %Background operators:
% 3.22/1.48  
% 3.22/1.48  
% 3.22/1.48  %Foreground operators:
% 3.22/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.22/1.48  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.22/1.48  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.22/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.48  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.22/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.22/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.22/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.22/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.22/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.22/1.48  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.22/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.22/1.48  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.22/1.48  
% 3.22/1.49  tff(f_125, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 3.22/1.49  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 3.22/1.49  tff(f_48, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.22/1.49  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.22/1.49  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 3.22/1.49  tff(f_90, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((?[B]: ((v1_relat_1(B) & v1_funct_1(B)) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A))))) => v2_funct_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_funct_1)).
% 3.22/1.49  tff(f_107, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 3.22/1.49  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 3.22/1.49  tff(c_30, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.22/1.49  tff(c_40, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.22/1.49  tff(c_44, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.22/1.49  tff(c_42, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.22/1.49  tff(c_36, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.22/1.49  tff(c_117, plain, (![A_28]: (k4_relat_1(A_28)=k2_funct_1(A_28) | ~v2_funct_1(A_28) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.22/1.49  tff(c_126, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_36, c_117])).
% 3.22/1.49  tff(c_135, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_126])).
% 3.22/1.49  tff(c_38, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.22/1.49  tff(c_32, plain, (k6_relat_1(k2_relat_1('#skF_1'))=k5_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.22/1.49  tff(c_12, plain, (![A_7]: (k1_relat_1(k6_relat_1(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.22/1.49  tff(c_77, plain, (k1_relat_1(k5_relat_1('#skF_2', '#skF_1'))=k2_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_32, c_12])).
% 3.22/1.49  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.22/1.49  tff(c_34, plain, (k2_relat_1('#skF_2')=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.22/1.49  tff(c_159, plain, (![A_30, B_31]: (k1_relat_1(k5_relat_1(A_30, B_31))=k1_relat_1(A_30) | ~r1_tarski(k2_relat_1(A_30), k1_relat_1(B_31)) | ~v1_relat_1(B_31) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.22/1.49  tff(c_174, plain, (![B_31]: (k1_relat_1(k5_relat_1('#skF_2', B_31))=k1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1(B_31)) | ~v1_relat_1(B_31) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_159])).
% 3.22/1.49  tff(c_256, plain, (![B_37]: (k1_relat_1(k5_relat_1('#skF_2', B_37))=k1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1(B_37)) | ~v1_relat_1(B_37))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_174])).
% 3.22/1.49  tff(c_275, plain, (k1_relat_1(k5_relat_1('#skF_2', '#skF_1'))=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6, c_256])).
% 3.22/1.49  tff(c_282, plain, (k2_relat_1('#skF_1')=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_77, c_275])).
% 3.22/1.49  tff(c_287, plain, (k6_relat_1(k1_relat_1('#skF_2'))=k5_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_282, c_32])).
% 3.22/1.49  tff(c_26, plain, (![A_13, B_15]: (v2_funct_1(A_13) | k6_relat_1(k1_relat_1(A_13))!=k5_relat_1(A_13, B_15) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.22/1.49  tff(c_335, plain, (![B_15]: (v2_funct_1('#skF_2') | k5_relat_1('#skF_2', B_15)!=k5_relat_1('#skF_2', '#skF_1') | ~v1_funct_1(B_15) | ~v1_relat_1(B_15) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_287, c_26])).
% 3.22/1.49  tff(c_358, plain, (![B_15]: (v2_funct_1('#skF_2') | k5_relat_1('#skF_2', B_15)!=k5_relat_1('#skF_2', '#skF_1') | ~v1_funct_1(B_15) | ~v1_relat_1(B_15))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_335])).
% 3.22/1.49  tff(c_449, plain, (![B_42]: (k5_relat_1('#skF_2', B_42)!=k5_relat_1('#skF_2', '#skF_1') | ~v1_funct_1(B_42) | ~v1_relat_1(B_42))), inference(splitLeft, [status(thm)], [c_358])).
% 3.22/1.49  tff(c_461, plain, (~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_44, c_449])).
% 3.22/1.49  tff(c_470, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_461])).
% 3.22/1.49  tff(c_471, plain, (v2_funct_1('#skF_2')), inference(splitRight, [status(thm)], [c_358])).
% 3.22/1.49  tff(c_761, plain, (![A_52, B_53]: (k2_funct_1(A_52)=B_53 | k6_relat_1(k1_relat_1(A_52))!=k5_relat_1(A_52, B_53) | k2_relat_1(A_52)!=k1_relat_1(B_53) | ~v2_funct_1(A_52) | ~v1_funct_1(B_53) | ~v1_relat_1(B_53) | ~v1_funct_1(A_52) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.22/1.49  tff(c_779, plain, (![B_53]: (k2_funct_1('#skF_2')=B_53 | k5_relat_1('#skF_2', B_53)!=k5_relat_1('#skF_2', '#skF_1') | k2_relat_1('#skF_2')!=k1_relat_1(B_53) | ~v2_funct_1('#skF_2') | ~v1_funct_1(B_53) | ~v1_relat_1(B_53) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_287, c_761])).
% 3.22/1.49  tff(c_842, plain, (![B_58]: (k2_funct_1('#skF_2')=B_58 | k5_relat_1('#skF_2', B_58)!=k5_relat_1('#skF_2', '#skF_1') | k1_relat_1(B_58)!=k1_relat_1('#skF_1') | ~v1_funct_1(B_58) | ~v1_relat_1(B_58))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_471, c_34, c_779])).
% 3.22/1.49  tff(c_854, plain, (k2_funct_1('#skF_2')='#skF_1' | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_44, c_842])).
% 3.22/1.49  tff(c_864, plain, (k2_funct_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_854])).
% 3.22/1.49  tff(c_16, plain, (![A_8]: (k4_relat_1(A_8)=k2_funct_1(A_8) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.22/1.49  tff(c_474, plain, (k4_relat_1('#skF_2')=k2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_471, c_16])).
% 3.22/1.49  tff(c_477, plain, (k4_relat_1('#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_474])).
% 3.22/1.49  tff(c_867, plain, (k4_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_864, c_477])).
% 3.22/1.49  tff(c_8, plain, (![A_3]: (k4_relat_1(k4_relat_1(A_3))=A_3 | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.22/1.49  tff(c_875, plain, (k4_relat_1('#skF_1')='#skF_2' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_867, c_8])).
% 3.22/1.49  tff(c_879, plain, (k2_funct_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_135, c_875])).
% 3.22/1.49  tff(c_881, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_879])).
% 3.22/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.49  
% 3.22/1.49  Inference rules
% 3.22/1.49  ----------------------
% 3.22/1.49  #Ref     : 0
% 3.22/1.49  #Sup     : 211
% 3.22/1.49  #Fact    : 0
% 3.22/1.49  #Define  : 0
% 3.22/1.49  #Split   : 7
% 3.22/1.49  #Chain   : 0
% 3.22/1.49  #Close   : 0
% 3.22/1.49  
% 3.22/1.49  Ordering : KBO
% 3.22/1.49  
% 3.22/1.49  Simplification rules
% 3.22/1.49  ----------------------
% 3.22/1.49  #Subsume      : 21
% 3.22/1.49  #Demod        : 176
% 3.22/1.49  #Tautology    : 86
% 3.22/1.49  #SimpNegUnit  : 1
% 3.22/1.49  #BackRed      : 8
% 3.22/1.49  
% 3.22/1.49  #Partial instantiations: 0
% 3.22/1.49  #Strategies tried      : 1
% 3.22/1.49  
% 3.22/1.49  Timing (in seconds)
% 3.22/1.49  ----------------------
% 3.22/1.50  Preprocessing        : 0.31
% 3.22/1.50  Parsing              : 0.17
% 3.22/1.50  CNF conversion       : 0.02
% 3.22/1.50  Main loop            : 0.40
% 3.22/1.50  Inferencing          : 0.13
% 3.22/1.50  Reduction            : 0.14
% 3.22/1.50  Demodulation         : 0.10
% 3.22/1.50  BG Simplification    : 0.02
% 3.22/1.50  Subsumption          : 0.09
% 3.22/1.50  Abstraction          : 0.02
% 3.22/1.50  MUC search           : 0.00
% 3.22/1.50  Cooper               : 0.00
% 3.22/1.50  Total                : 0.74
% 3.22/1.50  Index Insertion      : 0.00
% 3.22/1.50  Index Deletion       : 0.00
% 3.22/1.50  Index Matching       : 0.00
% 3.22/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
