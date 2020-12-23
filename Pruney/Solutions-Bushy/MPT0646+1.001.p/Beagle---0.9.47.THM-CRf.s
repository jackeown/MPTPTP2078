%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0646+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:38 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   34 (  41 expanded)
%              Number of leaves         :   18 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   61 (  98 expanded)
%              Number of equality atoms :   10 (  17 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( ? [B] :
              ( v1_relat_1(B)
              & v1_funct_1(B)
              & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
         => v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).

tff(f_60,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_28,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_41,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
           => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & r1_tarski(k2_relat_1(B),k1_relat_1(A)) )
           => v2_funct_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_1)).

tff(c_14,plain,(
    ~ v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_18,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_24,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_22,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_16,plain,(
    k6_relat_1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_10,plain,(
    ! [A_8] : k1_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_51,plain,(
    k1_relat_1(k5_relat_1('#skF_1','#skF_2')) = k1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_10])).

tff(c_4,plain,(
    ! [A_1] : v2_funct_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_53,plain,(
    v2_funct_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_4])).

tff(c_6,plain,(
    ! [B_4,A_2] :
      ( r1_tarski(k2_relat_1(B_4),k1_relat_1(A_2))
      | k1_relat_1(k5_relat_1(B_4,A_2)) != k1_relat_1(B_4)
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_88,plain,(
    ! [B_16,A_17] :
      ( v2_funct_1(B_16)
      | ~ r1_tarski(k2_relat_1(B_16),k1_relat_1(A_17))
      | ~ v2_funct_1(k5_relat_1(B_16,A_17))
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_129,plain,(
    ! [B_24,A_25] :
      ( v2_funct_1(B_24)
      | ~ v2_funct_1(k5_relat_1(B_24,A_25))
      | k1_relat_1(k5_relat_1(B_24,A_25)) != k1_relat_1(B_24)
      | ~ v1_funct_1(B_24)
      | ~ v1_relat_1(B_24)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(resolution,[status(thm)],[c_6,c_88])).

tff(c_132,plain,
    ( v2_funct_1('#skF_1')
    | k1_relat_1(k5_relat_1('#skF_1','#skF_2')) != k1_relat_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_53,c_129])).

tff(c_135,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_24,c_22,c_51,c_132])).

tff(c_137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_135])).

%------------------------------------------------------------------------------
