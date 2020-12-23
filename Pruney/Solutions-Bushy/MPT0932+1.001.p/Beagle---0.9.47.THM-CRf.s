%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0932+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:06 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   34 (  45 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   41 (  64 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k11_relat_1 > a_2_0_mcart_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(a_2_0_mcart_1,type,(
    a_2_0_mcart_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_63,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( r2_hidden(B,A)
           => r2_hidden(k2_mcart_1(B),k11_relat_1(A,k1_mcart_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_mcart_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(B)
        & v1_relat_1(B) )
     => ( r2_hidden(A,a_2_0_mcart_1(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,B)
            & A = k2_mcart_1(D)
            & k1_mcart_1(D) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_mcart_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ! [B] : k11_relat_1(A,B) = a_2_0_mcart_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_mcart_1)).

tff(c_18,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_21,plain,(
    ! [B_15,A_16] :
      ( ~ v1_xboole_0(B_15)
      | ~ r2_hidden(A_16,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_25,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_21])).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_26,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,B_18)
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_30,plain,(
    m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_26])).

tff(c_77,plain,(
    ! [D_22,B_23] :
      ( r2_hidden(k2_mcart_1(D_22),a_2_0_mcart_1(B_23,k1_mcart_1(D_22)))
      | ~ m1_subset_1(D_22,B_23)
      | ~ v1_relat_1(B_23)
      | v1_xboole_0(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_31,plain,(
    ! [A_19,B_20] :
      ( k11_relat_1(A_19,B_20) = a_2_0_mcart_1(A_19,B_20)
      | ~ v1_relat_1(A_19)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_40,plain,(
    ! [B_20] :
      ( k11_relat_1('#skF_2',B_20) = a_2_0_mcart_1('#skF_2',B_20)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_31,c_25])).

tff(c_50,plain,(
    ! [B_20] : k11_relat_1('#skF_2',B_20) = a_2_0_mcart_1('#skF_2',B_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_40])).

tff(c_16,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_3'),k11_relat_1('#skF_2',k1_mcart_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_52,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_3'),a_2_0_mcart_1('#skF_2',k1_mcart_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_16])).

tff(c_80,plain,
    ( ~ m1_subset_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_77,c_52])).

tff(c_89,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_30,c_80])).

tff(c_91,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25,c_89])).

%------------------------------------------------------------------------------
