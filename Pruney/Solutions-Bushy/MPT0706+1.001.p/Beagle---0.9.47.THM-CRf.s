%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0706+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:44 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   33 (  49 expanded)
%              Number of leaves         :   14 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   52 ( 120 expanded)
%              Number of equality atoms :    8 (  27 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_53,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( k10_relat_1(C,A) = k10_relat_1(C,B)
            & r1_tarski(A,k2_relat_1(C))
            & r1_tarski(B,k2_relat_1(C)) )
         => A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t161_funct_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
          & r1_tarski(A,k2_relat_1(C)) )
       => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

tff(c_10,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_16,plain,(
    k10_relat_1('#skF_3','#skF_2') = k10_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_42,plain,(
    ! [A_9,B_10,C_11] :
      ( r1_tarski(A_9,B_10)
      | ~ r1_tarski(A_9,k2_relat_1(C_11))
      | ~ r1_tarski(k10_relat_1(C_11,A_9),k10_relat_1(C_11,B_10))
      | ~ v1_funct_1(C_11)
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_45,plain,(
    ! [B_10] :
      ( r1_tarski('#skF_2',B_10)
      | ~ r1_tarski('#skF_2',k2_relat_1('#skF_3'))
      | ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3',B_10))
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_42])).

tff(c_59,plain,(
    ! [B_12] :
      ( r1_tarski('#skF_2',B_12)
      | ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3',B_12)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_12,c_45])).

tff(c_69,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_59])).

tff(c_14,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_48,plain,(
    ! [A_9] :
      ( r1_tarski(A_9,'#skF_2')
      | ~ r1_tarski(A_9,k2_relat_1('#skF_3'))
      | ~ r1_tarski(k10_relat_1('#skF_3',A_9),k10_relat_1('#skF_3','#skF_1'))
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_42])).

tff(c_75,plain,(
    ! [A_13] :
      ( r1_tarski(A_13,'#skF_2')
      | ~ r1_tarski(A_13,k2_relat_1('#skF_3'))
      | ~ r1_tarski(k10_relat_1('#skF_3',A_13),k10_relat_1('#skF_3','#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_48])).

tff(c_82,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | ~ r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_75])).

tff(c_87,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_82])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_89,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_87,c_2])).

tff(c_92,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_89])).

tff(c_94,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_92])).

%------------------------------------------------------------------------------
