%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1085+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:23 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   21 (  23 expanded)
%              Number of leaves         :   12 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   23 (  29 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_finset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_42,negated_conjecture,(
    ~ ! [A,B] :
        ( ( r1_tarski(A,B)
          & v1_finset_1(B) )
       => v1_finset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_finset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_finset_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_finset_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_finset_1)).

tff(c_8,plain,(
    ~ v1_finset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_10,plain,(
    v1_finset_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_12,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_19,plain,(
    ! [B_10,A_11] :
      ( v1_finset_1(B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_11))
      | ~ v1_finset_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    ! [A_12,B_13] :
      ( v1_finset_1(A_12)
      | ~ v1_finset_1(B_13)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(resolution,[status(thm)],[c_6,c_19])).

tff(c_27,plain,
    ( v1_finset_1('#skF_1')
    | ~ v1_finset_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_24])).

tff(c_30,plain,(
    v1_finset_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_27])).

tff(c_32,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_30])).

%------------------------------------------------------------------------------
