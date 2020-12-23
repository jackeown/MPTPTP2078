%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1089+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:23 EST 2020

% Result     : Theorem 1.50s
% Output     : CNFRefutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   18 (  21 expanded)
%              Number of leaves         :   11 (  14 expanded)
%              Depth                    :    3
%              Number of atoms          :   20 (  32 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > v1_funct_1 > v1_finset_1 > k9_relat_1 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(f_41,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( v1_finset_1(A)
         => v1_finset_1(k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_finset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_finset_1(B) )
     => v1_finset_1(k9_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_finset_1)).

tff(c_10,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    v1_finset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_11,plain,(
    ! [A_3,B_4] :
      ( v1_finset_1(k9_relat_1(A_3,B_4))
      | ~ v1_finset_1(B_4)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ~ v1_finset_1(k9_relat_1('#skF_2','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,
    ( ~ v1_finset_1('#skF_1')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_11,c_4])).

tff(c_18,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_8,c_6,c_14])).

%------------------------------------------------------------------------------
