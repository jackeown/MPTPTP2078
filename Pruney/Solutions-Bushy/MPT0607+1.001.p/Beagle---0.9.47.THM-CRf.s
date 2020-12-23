%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0607+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:34 EST 2020

% Result     : Theorem 1.50s
% Output     : CNFRefutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   24 (  28 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :   23 (  33 expanded)
%              Number of equality atoms :   10 (  13 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_41,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(k1_relat_1(C),A)
         => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_relat_1)).

tff(c_10,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_11,plain,(
    ! [B_6,A_7] :
      ( k7_relat_1(B_6,A_7) = B_6
      | ~ r1_tarski(k1_relat_1(B_6),A_7)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_11])).

tff(c_17,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14])).

tff(c_22,plain,(
    ! [C_8,A_9,B_10] :
      ( k6_subset_1(k7_relat_1(C_8,A_9),k7_relat_1(C_8,B_10)) = k7_relat_1(C_8,k6_subset_1(A_9,B_10))
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_31,plain,(
    ! [B_10] :
      ( k7_relat_1('#skF_3',k6_subset_1('#skF_1',B_10)) = k6_subset_1('#skF_3',k7_relat_1('#skF_3',B_10))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17,c_22])).

tff(c_38,plain,(
    ! [B_10] : k7_relat_1('#skF_3',k6_subset_1('#skF_1',B_10)) = k6_subset_1('#skF_3',k7_relat_1('#skF_3',B_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_31])).

tff(c_6,plain,(
    k7_relat_1('#skF_3',k6_subset_1('#skF_1','#skF_2')) != k6_subset_1('#skF_3',k7_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_43,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_6])).

%------------------------------------------------------------------------------
