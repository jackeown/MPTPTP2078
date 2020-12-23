%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:49 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 176 expanded)
%              Number of leaves         :   25 (  73 expanded)
%              Depth                    :   10
%              Number of atoms          :  140 ( 427 expanded)
%              Number of equality atoms :   34 ( 123 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
            & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_32,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_61,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_38,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_36,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_34,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_134,plain,(
    ! [A_33] :
      ( k4_relat_1(A_33) = k2_funct_1(A_33)
      | ~ v2_funct_1(A_33)
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_137,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_134])).

tff(c_140,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_137])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_relat_1(k4_relat_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_150,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_6])).

tff(c_158,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_150])).

tff(c_24,plain,(
    ! [A_13] : v4_relat_1(k6_relat_1(A_13),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_22,plain,(
    ! [A_13] : v1_relat_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_16,plain,(
    ! [A_11] : k1_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_90,plain,(
    ! [B_27,A_28] :
      ( r1_tarski(k1_relat_1(B_27),A_28)
      | ~ v4_relat_1(B_27,A_28)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_99,plain,(
    ! [A_11,A_28] :
      ( r1_tarski(A_11,A_28)
      | ~ v4_relat_1(k6_relat_1(A_11),A_28)
      | ~ v1_relat_1(k6_relat_1(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_90])).

tff(c_103,plain,(
    ! [A_29,A_30] :
      ( r1_tarski(A_29,A_30)
      | ~ v4_relat_1(k6_relat_1(A_29),A_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_99])).

tff(c_112,plain,(
    ! [A_31] : r1_tarski(A_31,A_31) ),
    inference(resolution,[status(thm)],[c_24,c_103])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( v4_relat_1(B_2,A_1)
      | ~ r1_tarski(k1_relat_1(B_2),A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_117,plain,(
    ! [B_2] :
      ( v4_relat_1(B_2,k1_relat_1(B_2))
      | ~ v1_relat_1(B_2) ) ),
    inference(resolution,[status(thm)],[c_112,c_2])).

tff(c_10,plain,(
    ! [A_4] :
      ( k1_relat_1(k4_relat_1(A_4)) = k2_relat_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_338,plain,(
    ! [A_44,A_45] :
      ( r1_tarski(k2_relat_1(A_44),A_45)
      | ~ v4_relat_1(k4_relat_1(A_44),A_45)
      | ~ v1_relat_1(k4_relat_1(A_44))
      | ~ v1_relat_1(A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_90])).

tff(c_365,plain,(
    ! [A_44] :
      ( r1_tarski(k2_relat_1(A_44),k1_relat_1(k4_relat_1(A_44)))
      | ~ v1_relat_1(A_44)
      | ~ v1_relat_1(k4_relat_1(A_44)) ) ),
    inference(resolution,[status(thm)],[c_117,c_338])).

tff(c_462,plain,(
    ! [A_52,B_53] :
      ( k1_relat_1(k5_relat_1(A_52,B_53)) = k1_relat_1(A_52)
      | ~ r1_tarski(k2_relat_1(A_52),k1_relat_1(B_53))
      | ~ v1_relat_1(B_53)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_534,plain,(
    ! [A_56] :
      ( k1_relat_1(k5_relat_1(A_56,k4_relat_1(A_56))) = k1_relat_1(A_56)
      | ~ v1_relat_1(A_56)
      | ~ v1_relat_1(k4_relat_1(A_56)) ) ),
    inference(resolution,[status(thm)],[c_365,c_462])).

tff(c_566,plain,
    ( k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k4_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_534])).

tff(c_574,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_140,c_38,c_566])).

tff(c_576,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_574])).

tff(c_577,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_664,plain,(
    ! [A_69] :
      ( k4_relat_1(A_69) = k2_funct_1(A_69)
      | ~ v2_funct_1(A_69)
      | ~ v1_funct_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_667,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_664])).

tff(c_670,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_667])).

tff(c_680,plain,
    ( v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_670,c_6])).

tff(c_688,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_680])).

tff(c_8,plain,(
    ! [A_4] :
      ( k2_relat_1(k4_relat_1(A_4)) = k1_relat_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_677,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_670,c_8])).

tff(c_686,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_677])).

tff(c_674,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_670,c_10])).

tff(c_684,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_674])).

tff(c_601,plain,(
    ! [B_59,A_60] :
      ( r1_tarski(k1_relat_1(B_59),A_60)
      | ~ v4_relat_1(B_59,A_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_610,plain,(
    ! [A_11,A_60] :
      ( r1_tarski(A_11,A_60)
      | ~ v4_relat_1(k6_relat_1(A_11),A_60)
      | ~ v1_relat_1(k6_relat_1(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_601])).

tff(c_613,plain,(
    ! [A_61,A_62] :
      ( r1_tarski(A_61,A_62)
      | ~ v4_relat_1(k6_relat_1(A_61),A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_610])).

tff(c_617,plain,(
    ! [A_13] : r1_tarski(A_13,A_13) ),
    inference(resolution,[status(thm)],[c_24,c_613])).

tff(c_619,plain,(
    ! [B_64,A_65] :
      ( v4_relat_1(B_64,A_65)
      | ~ r1_tarski(k1_relat_1(B_64),A_65)
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_636,plain,(
    ! [B_64] :
      ( v4_relat_1(B_64,k1_relat_1(B_64))
      | ~ v1_relat_1(B_64) ) ),
    inference(resolution,[status(thm)],[c_617,c_619])).

tff(c_693,plain,
    ( v4_relat_1(k2_funct_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_684,c_636])).

tff(c_703,plain,(
    v4_relat_1(k2_funct_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_688,c_693])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k1_relat_1(B_2),A_1)
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_931,plain,(
    ! [B_83,A_84] :
      ( k2_relat_1(k5_relat_1(B_83,A_84)) = k2_relat_1(A_84)
      | ~ r1_tarski(k1_relat_1(A_84),k2_relat_1(B_83))
      | ~ v1_relat_1(B_83)
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1026,plain,(
    ! [B_89,B_90] :
      ( k2_relat_1(k5_relat_1(B_89,B_90)) = k2_relat_1(B_90)
      | ~ v1_relat_1(B_89)
      | ~ v4_relat_1(B_90,k2_relat_1(B_89))
      | ~ v1_relat_1(B_90) ) ),
    inference(resolution,[status(thm)],[c_4,c_931])).

tff(c_1056,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k2_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_703,c_1026])).

tff(c_1083,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_688,c_38,c_686,c_1056])).

tff(c_1085,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_577,c_1083])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:35:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.01/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.01/1.60  
% 3.01/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.01/1.60  %$ v5_relat_1 > v4_relat_1 > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 3.01/1.60  
% 3.01/1.60  %Foreground sorts:
% 3.01/1.60  
% 3.01/1.60  
% 3.01/1.60  %Background operators:
% 3.01/1.60  
% 3.01/1.60  
% 3.01/1.60  %Foreground operators:
% 3.01/1.60  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.01/1.60  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.01/1.60  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.01/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.01/1.60  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.01/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.01/1.60  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.01/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.01/1.60  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.01/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.01/1.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.01/1.60  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.01/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.01/1.60  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.01/1.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.01/1.60  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.01/1.60  
% 3.33/1.62  tff(f_98, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 3.33/1.62  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 3.33/1.62  tff(f_35, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 3.33/1.62  tff(f_77, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc24_relat_1)).
% 3.33/1.62  tff(f_63, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.33/1.62  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.33/1.62  tff(f_41, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 3.33/1.62  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 3.33/1.62  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 3.33/1.62  tff(c_32, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.33/1.62  tff(c_61, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_32])).
% 3.33/1.62  tff(c_38, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.33/1.62  tff(c_36, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.33/1.62  tff(c_34, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.33/1.62  tff(c_134, plain, (![A_33]: (k4_relat_1(A_33)=k2_funct_1(A_33) | ~v2_funct_1(A_33) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.33/1.62  tff(c_137, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_34, c_134])).
% 3.33/1.62  tff(c_140, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_137])).
% 3.33/1.62  tff(c_6, plain, (![A_3]: (v1_relat_1(k4_relat_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.33/1.62  tff(c_150, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_140, c_6])).
% 3.33/1.62  tff(c_158, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_150])).
% 3.33/1.62  tff(c_24, plain, (![A_13]: (v4_relat_1(k6_relat_1(A_13), A_13))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.33/1.62  tff(c_22, plain, (![A_13]: (v1_relat_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.33/1.62  tff(c_16, plain, (![A_11]: (k1_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.33/1.62  tff(c_90, plain, (![B_27, A_28]: (r1_tarski(k1_relat_1(B_27), A_28) | ~v4_relat_1(B_27, A_28) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.33/1.62  tff(c_99, plain, (![A_11, A_28]: (r1_tarski(A_11, A_28) | ~v4_relat_1(k6_relat_1(A_11), A_28) | ~v1_relat_1(k6_relat_1(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_90])).
% 3.33/1.62  tff(c_103, plain, (![A_29, A_30]: (r1_tarski(A_29, A_30) | ~v4_relat_1(k6_relat_1(A_29), A_30))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_99])).
% 3.33/1.62  tff(c_112, plain, (![A_31]: (r1_tarski(A_31, A_31))), inference(resolution, [status(thm)], [c_24, c_103])).
% 3.33/1.62  tff(c_2, plain, (![B_2, A_1]: (v4_relat_1(B_2, A_1) | ~r1_tarski(k1_relat_1(B_2), A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.33/1.62  tff(c_117, plain, (![B_2]: (v4_relat_1(B_2, k1_relat_1(B_2)) | ~v1_relat_1(B_2))), inference(resolution, [status(thm)], [c_112, c_2])).
% 3.33/1.62  tff(c_10, plain, (![A_4]: (k1_relat_1(k4_relat_1(A_4))=k2_relat_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.33/1.62  tff(c_338, plain, (![A_44, A_45]: (r1_tarski(k2_relat_1(A_44), A_45) | ~v4_relat_1(k4_relat_1(A_44), A_45) | ~v1_relat_1(k4_relat_1(A_44)) | ~v1_relat_1(A_44))), inference(superposition, [status(thm), theory('equality')], [c_10, c_90])).
% 3.33/1.62  tff(c_365, plain, (![A_44]: (r1_tarski(k2_relat_1(A_44), k1_relat_1(k4_relat_1(A_44))) | ~v1_relat_1(A_44) | ~v1_relat_1(k4_relat_1(A_44)))), inference(resolution, [status(thm)], [c_117, c_338])).
% 3.33/1.62  tff(c_462, plain, (![A_52, B_53]: (k1_relat_1(k5_relat_1(A_52, B_53))=k1_relat_1(A_52) | ~r1_tarski(k2_relat_1(A_52), k1_relat_1(B_53)) | ~v1_relat_1(B_53) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.33/1.62  tff(c_534, plain, (![A_56]: (k1_relat_1(k5_relat_1(A_56, k4_relat_1(A_56)))=k1_relat_1(A_56) | ~v1_relat_1(A_56) | ~v1_relat_1(k4_relat_1(A_56)))), inference(resolution, [status(thm)], [c_365, c_462])).
% 3.33/1.62  tff(c_566, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k4_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_140, c_534])).
% 3.33/1.62  tff(c_574, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_140, c_38, c_566])).
% 3.33/1.62  tff(c_576, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_574])).
% 3.33/1.62  tff(c_577, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_32])).
% 3.33/1.62  tff(c_664, plain, (![A_69]: (k4_relat_1(A_69)=k2_funct_1(A_69) | ~v2_funct_1(A_69) | ~v1_funct_1(A_69) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.33/1.62  tff(c_667, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_34, c_664])).
% 3.33/1.62  tff(c_670, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_667])).
% 3.33/1.62  tff(c_680, plain, (v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_670, c_6])).
% 3.33/1.62  tff(c_688, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_680])).
% 3.33/1.62  tff(c_8, plain, (![A_4]: (k2_relat_1(k4_relat_1(A_4))=k1_relat_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.33/1.62  tff(c_677, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_670, c_8])).
% 3.33/1.62  tff(c_686, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_677])).
% 3.33/1.62  tff(c_674, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_670, c_10])).
% 3.33/1.62  tff(c_684, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_674])).
% 3.33/1.62  tff(c_601, plain, (![B_59, A_60]: (r1_tarski(k1_relat_1(B_59), A_60) | ~v4_relat_1(B_59, A_60) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.33/1.62  tff(c_610, plain, (![A_11, A_60]: (r1_tarski(A_11, A_60) | ~v4_relat_1(k6_relat_1(A_11), A_60) | ~v1_relat_1(k6_relat_1(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_601])).
% 3.33/1.62  tff(c_613, plain, (![A_61, A_62]: (r1_tarski(A_61, A_62) | ~v4_relat_1(k6_relat_1(A_61), A_62))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_610])).
% 3.33/1.62  tff(c_617, plain, (![A_13]: (r1_tarski(A_13, A_13))), inference(resolution, [status(thm)], [c_24, c_613])).
% 3.33/1.62  tff(c_619, plain, (![B_64, A_65]: (v4_relat_1(B_64, A_65) | ~r1_tarski(k1_relat_1(B_64), A_65) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.33/1.62  tff(c_636, plain, (![B_64]: (v4_relat_1(B_64, k1_relat_1(B_64)) | ~v1_relat_1(B_64))), inference(resolution, [status(thm)], [c_617, c_619])).
% 3.33/1.62  tff(c_693, plain, (v4_relat_1(k2_funct_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_684, c_636])).
% 3.33/1.62  tff(c_703, plain, (v4_relat_1(k2_funct_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_688, c_693])).
% 3.33/1.62  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k1_relat_1(B_2), A_1) | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.33/1.62  tff(c_931, plain, (![B_83, A_84]: (k2_relat_1(k5_relat_1(B_83, A_84))=k2_relat_1(A_84) | ~r1_tarski(k1_relat_1(A_84), k2_relat_1(B_83)) | ~v1_relat_1(B_83) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.33/1.62  tff(c_1026, plain, (![B_89, B_90]: (k2_relat_1(k5_relat_1(B_89, B_90))=k2_relat_1(B_90) | ~v1_relat_1(B_89) | ~v4_relat_1(B_90, k2_relat_1(B_89)) | ~v1_relat_1(B_90))), inference(resolution, [status(thm)], [c_4, c_931])).
% 3.33/1.62  tff(c_1056, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k2_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_703, c_1026])).
% 3.33/1.62  tff(c_1083, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_688, c_38, c_686, c_1056])).
% 3.33/1.62  tff(c_1085, plain, $false, inference(negUnitSimplification, [status(thm)], [c_577, c_1083])).
% 3.33/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.62  
% 3.33/1.62  Inference rules
% 3.33/1.62  ----------------------
% 3.33/1.62  #Ref     : 0
% 3.33/1.62  #Sup     : 234
% 3.33/1.62  #Fact    : 0
% 3.33/1.62  #Define  : 0
% 3.33/1.62  #Split   : 4
% 3.33/1.62  #Chain   : 0
% 3.33/1.62  #Close   : 0
% 3.33/1.62  
% 3.33/1.62  Ordering : KBO
% 3.33/1.62  
% 3.33/1.62  Simplification rules
% 3.33/1.62  ----------------------
% 3.33/1.62  #Subsume      : 6
% 3.33/1.62  #Demod        : 197
% 3.33/1.62  #Tautology    : 93
% 3.33/1.62  #SimpNegUnit  : 2
% 3.33/1.62  #BackRed      : 0
% 3.33/1.62  
% 3.33/1.62  #Partial instantiations: 0
% 3.33/1.62  #Strategies tried      : 1
% 3.33/1.62  
% 3.33/1.62  Timing (in seconds)
% 3.33/1.62  ----------------------
% 3.33/1.62  Preprocessing        : 0.33
% 3.33/1.62  Parsing              : 0.18
% 3.33/1.62  CNF conversion       : 0.02
% 3.33/1.62  Main loop            : 0.40
% 3.33/1.62  Inferencing          : 0.15
% 3.33/1.62  Reduction            : 0.13
% 3.33/1.62  Demodulation         : 0.09
% 3.33/1.62  BG Simplification    : 0.02
% 3.33/1.62  Subsumption          : 0.06
% 3.33/1.62  Abstraction          : 0.02
% 3.33/1.62  MUC search           : 0.00
% 3.33/1.62  Cooper               : 0.00
% 3.33/1.62  Total                : 0.77
% 3.33/1.62  Index Insertion      : 0.00
% 3.33/1.62  Index Deletion       : 0.00
% 3.33/1.62  Index Matching       : 0.00
% 3.33/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
