%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0648+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   34 (  51 expanded)
%              Number of leaves         :   14 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   47 ( 106 expanded)
%              Number of equality atoms :   21 (  44 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > v1_funct_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_49,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
            & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_32,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(c_8,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_33,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_8])).

tff(c_14,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_34,plain,(
    ! [A_5] :
      ( k4_relat_1(A_5) = k2_funct_1(A_5)
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_37,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_34])).

tff(c_40,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_37])).

tff(c_6,plain,(
    ! [A_2] :
      ( k1_relat_1(k4_relat_1(A_2)) = k2_relat_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_47,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_6])).

tff(c_53,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_47])).

tff(c_55,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_53])).

tff(c_56,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_8])).

tff(c_62,plain,(
    ! [A_6] :
      ( k4_relat_1(A_6) = k2_funct_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_65,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_62])).

tff(c_68,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_65])).

tff(c_4,plain,(
    ! [A_2] :
      ( k2_relat_1(k4_relat_1(A_2)) = k1_relat_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_72,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_4])).

tff(c_79,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_72])).

tff(c_81,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_79])).

%------------------------------------------------------------------------------
