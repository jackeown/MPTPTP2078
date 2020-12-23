%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1093+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:24 EST 2020

% Result     : Theorem 1.56s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   27 (  35 expanded)
%              Number of leaves         :   15 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  68 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > v1_finset_1 > k9_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(f_51,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( r1_tarski(A,k2_relat_1(B))
            & v1_finset_1(k10_relat_1(B,A)) )
         => v1_finset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_finset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_finset_1(B) )
     => v1_finset_1(k9_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_finset_1)).

tff(c_6,plain,(
    ~ v1_finset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    v1_finset_1(k10_relat_1('#skF_2','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16,plain,(
    ! [B_7,A_8] :
      ( k9_relat_1(B_7,k10_relat_1(B_7,A_8)) = A_8
      | ~ r1_tarski(A_8,k2_relat_1(B_7))
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_18,plain,
    ( k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_16])).

tff(c_21,plain,(
    k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_18])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_finset_1(k9_relat_1(A_1,B_2))
      | ~ v1_finset_1(B_2)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_25,plain,
    ( v1_finset_1('#skF_1')
    | ~ v1_finset_1(k10_relat_1('#skF_2','#skF_1'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_21,c_2])).

tff(c_29,plain,(
    v1_finset_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_8,c_25])).

tff(c_31,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_29])).

%------------------------------------------------------------------------------
