%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:53 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 173 expanded)
%              Number of leaves         :   25 (  68 expanded)
%              Depth                    :   10
%              Number of atoms          :  141 ( 467 expanded)
%              Number of equality atoms :   54 ( 192 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
            & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_93,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( k2_relat_1(A) = k2_relat_1(B)
               => k2_relat_1(k5_relat_1(A,C)) = k2_relat_1(k5_relat_1(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t199_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( k1_relat_1(A) = k1_relat_1(B)
               => k1_relat_1(k5_relat_1(C,A)) = k1_relat_1(k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t198_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_36,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_34,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_28,plain,(
    ! [A_25] :
      ( k2_relat_1(k2_funct_1(A_25)) = k1_relat_1(A_25)
      | ~ v2_funct_1(A_25)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_624,plain,(
    ! [B_65,A_66] :
      ( k7_relat_1(B_65,A_66) = B_65
      | ~ r1_tarski(k1_relat_1(B_65),A_66)
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_637,plain,(
    ! [B_65] :
      ( k7_relat_1(B_65,k1_relat_1(B_65)) = B_65
      | ~ v1_relat_1(B_65) ) ),
    inference(resolution,[status(thm)],[c_6,c_624])).

tff(c_26,plain,(
    ! [A_24] :
      ( v1_relat_1(k2_funct_1(A_24))
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_8,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [A_18] : k2_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_20,plain,(
    ! [A_20,B_21] :
      ( k5_relat_1(k6_relat_1(A_20),B_21) = k7_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_722,plain,(
    ! [B_72,C_73,A_74] :
      ( k2_relat_1(k5_relat_1(B_72,C_73)) = k2_relat_1(k5_relat_1(A_74,C_73))
      | k2_relat_1(B_72) != k2_relat_1(A_74)
      | ~ v1_relat_1(C_73)
      | ~ v1_relat_1(B_72)
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_764,plain,(
    ! [B_21,A_20,B_72] :
      ( k2_relat_1(k7_relat_1(B_21,A_20)) = k2_relat_1(k5_relat_1(B_72,B_21))
      | k2_relat_1(k6_relat_1(A_20)) != k2_relat_1(B_72)
      | ~ v1_relat_1(B_21)
      | ~ v1_relat_1(B_72)
      | ~ v1_relat_1(k6_relat_1(A_20))
      | ~ v1_relat_1(B_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_722])).

tff(c_846,plain,(
    ! [B_77,A_78,B_79] :
      ( k2_relat_1(k7_relat_1(B_77,A_78)) = k2_relat_1(k5_relat_1(B_79,B_77))
      | k2_relat_1(B_79) != A_78
      | ~ v1_relat_1(B_79)
      | ~ v1_relat_1(B_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_16,c_764])).

tff(c_30,plain,(
    ! [A_25] :
      ( k1_relat_1(k2_funct_1(A_25)) = k2_relat_1(A_25)
      | ~ v2_funct_1(A_25)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_242,plain,(
    ! [C_47,B_48,A_49] :
      ( k1_relat_1(k5_relat_1(C_47,B_48)) = k1_relat_1(k5_relat_1(C_47,A_49))
      | k1_relat_1(B_48) != k1_relat_1(A_49)
      | ~ v1_relat_1(C_47)
      | ~ v1_relat_1(B_48)
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_32,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_62,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_269,plain,(
    ! [B_48] :
      ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),B_48)) != k2_relat_1('#skF_1')
      | k1_relat_1(B_48) != k1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(B_48)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_62])).

tff(c_304,plain,(
    ! [B_48] :
      ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),B_48)) != k2_relat_1('#skF_1')
      | k1_relat_1(B_48) != k1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(B_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_269])).

tff(c_408,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_304])).

tff(c_411,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_408])).

tff(c_415,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_411])).

tff(c_417,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_304])).

tff(c_14,plain,(
    ! [A_18] : k1_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    ! [A_19] :
      ( k5_relat_1(A_19,k6_relat_1(k2_relat_1(A_19))) = A_19
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_418,plain,(
    ! [B_54] :
      ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),B_54)) != k2_relat_1('#skF_1')
      | k1_relat_1(B_54) != k1_relat_1('#skF_1')
      | ~ v1_relat_1(B_54) ) ),
    inference(splitRight,[status(thm)],[c_304])).

tff(c_430,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | k1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1('#skF_1')))) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1('#skF_1'))))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_418])).

tff(c_436,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_417,c_8,c_14,c_430])).

tff(c_437,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_436])).

tff(c_440,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_437])).

tff(c_444,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_440])).

tff(c_445,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_436])).

tff(c_542,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_445])).

tff(c_546,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_542])).

tff(c_547,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_871,plain,(
    ! [A_78] :
      ( k2_relat_1(k7_relat_1('#skF_1',A_78)) != k2_relat_1('#skF_1')
      | k2_relat_1(k2_funct_1('#skF_1')) != A_78
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_846,c_547])).

tff(c_908,plain,(
    ! [A_78] :
      ( k2_relat_1(k7_relat_1('#skF_1',A_78)) != k2_relat_1('#skF_1')
      | k2_relat_1(k2_funct_1('#skF_1')) != A_78
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_871])).

tff(c_923,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_908])).

tff(c_926,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_923])).

tff(c_930,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_926])).

tff(c_934,plain,(
    ! [A_80] :
      ( k2_relat_1(k7_relat_1('#skF_1',A_80)) != k2_relat_1('#skF_1')
      | k2_relat_1(k2_funct_1('#skF_1')) != A_80 ) ),
    inference(splitRight,[status(thm)],[c_908])).

tff(c_942,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_637,c_934])).

tff(c_947,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_942])).

tff(c_950,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_947])).

tff(c_954,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_950])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:51:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.43  
% 2.80/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.43  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 2.80/1.43  
% 2.80/1.43  %Foreground sorts:
% 2.80/1.43  
% 2.80/1.43  
% 2.80/1.43  %Background operators:
% 2.80/1.43  
% 2.80/1.43  
% 2.80/1.43  %Foreground operators:
% 2.80/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.80/1.43  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.80/1.43  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.80/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.43  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.80/1.43  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.80/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.80/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.80/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.80/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.80/1.43  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.80/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.80/1.43  
% 2.80/1.45  tff(f_104, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_funct_1)).
% 2.80/1.45  tff(f_93, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 2.80/1.45  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.80/1.45  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 2.80/1.45  tff(f_83, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.80/1.45  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.80/1.45  tff(f_61, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.80/1.45  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.80/1.45  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k2_relat_1(A) = k2_relat_1(B)) => (k2_relat_1(k5_relat_1(A, C)) = k2_relat_1(k5_relat_1(B, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t199_relat_1)).
% 2.80/1.45  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k1_relat_1(A) = k1_relat_1(B)) => (k1_relat_1(k5_relat_1(C, A)) = k1_relat_1(k5_relat_1(C, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t198_relat_1)).
% 2.80/1.45  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 2.80/1.45  tff(c_38, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.80/1.45  tff(c_36, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.80/1.45  tff(c_34, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.80/1.45  tff(c_28, plain, (![A_25]: (k2_relat_1(k2_funct_1(A_25))=k1_relat_1(A_25) | ~v2_funct_1(A_25) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.80/1.45  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.80/1.45  tff(c_624, plain, (![B_65, A_66]: (k7_relat_1(B_65, A_66)=B_65 | ~r1_tarski(k1_relat_1(B_65), A_66) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.80/1.45  tff(c_637, plain, (![B_65]: (k7_relat_1(B_65, k1_relat_1(B_65))=B_65 | ~v1_relat_1(B_65))), inference(resolution, [status(thm)], [c_6, c_624])).
% 2.80/1.45  tff(c_26, plain, (![A_24]: (v1_relat_1(k2_funct_1(A_24)) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.80/1.45  tff(c_8, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.80/1.45  tff(c_16, plain, (![A_18]: (k2_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.80/1.45  tff(c_20, plain, (![A_20, B_21]: (k5_relat_1(k6_relat_1(A_20), B_21)=k7_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.80/1.45  tff(c_722, plain, (![B_72, C_73, A_74]: (k2_relat_1(k5_relat_1(B_72, C_73))=k2_relat_1(k5_relat_1(A_74, C_73)) | k2_relat_1(B_72)!=k2_relat_1(A_74) | ~v1_relat_1(C_73) | ~v1_relat_1(B_72) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.80/1.45  tff(c_764, plain, (![B_21, A_20, B_72]: (k2_relat_1(k7_relat_1(B_21, A_20))=k2_relat_1(k5_relat_1(B_72, B_21)) | k2_relat_1(k6_relat_1(A_20))!=k2_relat_1(B_72) | ~v1_relat_1(B_21) | ~v1_relat_1(B_72) | ~v1_relat_1(k6_relat_1(A_20)) | ~v1_relat_1(B_21))), inference(superposition, [status(thm), theory('equality')], [c_20, c_722])).
% 2.80/1.45  tff(c_846, plain, (![B_77, A_78, B_79]: (k2_relat_1(k7_relat_1(B_77, A_78))=k2_relat_1(k5_relat_1(B_79, B_77)) | k2_relat_1(B_79)!=A_78 | ~v1_relat_1(B_79) | ~v1_relat_1(B_77))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_16, c_764])).
% 2.80/1.45  tff(c_30, plain, (![A_25]: (k1_relat_1(k2_funct_1(A_25))=k2_relat_1(A_25) | ~v2_funct_1(A_25) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.80/1.45  tff(c_242, plain, (![C_47, B_48, A_49]: (k1_relat_1(k5_relat_1(C_47, B_48))=k1_relat_1(k5_relat_1(C_47, A_49)) | k1_relat_1(B_48)!=k1_relat_1(A_49) | ~v1_relat_1(C_47) | ~v1_relat_1(B_48) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.80/1.45  tff(c_32, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1') | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.80/1.45  tff(c_62, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_32])).
% 2.80/1.45  tff(c_269, plain, (![B_48]: (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), B_48))!=k2_relat_1('#skF_1') | k1_relat_1(B_48)!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(B_48) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_242, c_62])).
% 2.80/1.45  tff(c_304, plain, (![B_48]: (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), B_48))!=k2_relat_1('#skF_1') | k1_relat_1(B_48)!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(B_48))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_269])).
% 2.80/1.45  tff(c_408, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_304])).
% 2.80/1.45  tff(c_411, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_408])).
% 2.80/1.45  tff(c_415, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_411])).
% 2.80/1.45  tff(c_417, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_304])).
% 2.80/1.45  tff(c_14, plain, (![A_18]: (k1_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.80/1.45  tff(c_18, plain, (![A_19]: (k5_relat_1(A_19, k6_relat_1(k2_relat_1(A_19)))=A_19 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.80/1.45  tff(c_418, plain, (![B_54]: (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), B_54))!=k2_relat_1('#skF_1') | k1_relat_1(B_54)!=k1_relat_1('#skF_1') | ~v1_relat_1(B_54))), inference(splitRight, [status(thm)], [c_304])).
% 2.80/1.45  tff(c_430, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | k1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1('#skF_1'))))!=k1_relat_1('#skF_1') | ~v1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1('#skF_1')))) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_418])).
% 2.80/1.45  tff(c_436, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_417, c_8, c_14, c_430])).
% 2.80/1.45  tff(c_437, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_436])).
% 2.80/1.45  tff(c_440, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_28, c_437])).
% 2.80/1.45  tff(c_444, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_440])).
% 2.80/1.45  tff(c_445, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_436])).
% 2.80/1.45  tff(c_542, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_30, c_445])).
% 2.80/1.45  tff(c_546, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_542])).
% 2.80/1.45  tff(c_547, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_32])).
% 2.80/1.45  tff(c_871, plain, (![A_78]: (k2_relat_1(k7_relat_1('#skF_1', A_78))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=A_78 | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_846, c_547])).
% 2.80/1.45  tff(c_908, plain, (![A_78]: (k2_relat_1(k7_relat_1('#skF_1', A_78))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=A_78 | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_871])).
% 2.80/1.45  tff(c_923, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_908])).
% 2.80/1.45  tff(c_926, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_923])).
% 2.80/1.45  tff(c_930, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_926])).
% 2.80/1.45  tff(c_934, plain, (![A_80]: (k2_relat_1(k7_relat_1('#skF_1', A_80))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=A_80)), inference(splitRight, [status(thm)], [c_908])).
% 2.80/1.45  tff(c_942, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_637, c_934])).
% 2.80/1.45  tff(c_947, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_942])).
% 2.80/1.45  tff(c_950, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_28, c_947])).
% 2.80/1.45  tff(c_954, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_950])).
% 2.80/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.45  
% 2.80/1.45  Inference rules
% 2.80/1.45  ----------------------
% 2.80/1.45  #Ref     : 0
% 2.80/1.45  #Sup     : 196
% 2.80/1.45  #Fact    : 0
% 2.80/1.45  #Define  : 0
% 2.80/1.45  #Split   : 5
% 2.80/1.45  #Chain   : 0
% 2.80/1.45  #Close   : 0
% 2.80/1.45  
% 2.80/1.45  Ordering : KBO
% 2.80/1.45  
% 2.80/1.45  Simplification rules
% 2.80/1.45  ----------------------
% 2.80/1.45  #Subsume      : 5
% 2.80/1.45  #Demod        : 175
% 2.80/1.45  #Tautology    : 79
% 2.80/1.45  #SimpNegUnit  : 0
% 2.80/1.45  #BackRed      : 0
% 2.80/1.45  
% 2.80/1.45  #Partial instantiations: 0
% 2.80/1.45  #Strategies tried      : 1
% 2.80/1.45  
% 2.80/1.45  Timing (in seconds)
% 2.80/1.45  ----------------------
% 3.07/1.45  Preprocessing        : 0.31
% 3.07/1.45  Parsing              : 0.17
% 3.07/1.45  CNF conversion       : 0.02
% 3.07/1.45  Main loop            : 0.37
% 3.07/1.45  Inferencing          : 0.14
% 3.07/1.45  Reduction            : 0.12
% 3.07/1.45  Demodulation         : 0.09
% 3.07/1.45  BG Simplification    : 0.03
% 3.07/1.45  Subsumption          : 0.06
% 3.07/1.45  Abstraction          : 0.02
% 3.07/1.45  MUC search           : 0.00
% 3.07/1.45  Cooper               : 0.00
% 3.07/1.45  Total                : 0.71
% 3.07/1.45  Index Insertion      : 0.00
% 3.07/1.45  Index Deletion       : 0.00
% 3.07/1.45  Index Matching       : 0.00
% 3.07/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
