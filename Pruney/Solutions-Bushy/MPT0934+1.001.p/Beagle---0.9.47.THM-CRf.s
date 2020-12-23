%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0934+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   31 (  39 expanded)
%              Number of leaves         :   15 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   65 ( 113 expanded)
%              Number of equality atoms :   26 (  44 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_61,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_relat_1(A) )
       => ! [B] :
            ( m1_subset_1(B,A)
           => ! [C] :
                ( m1_subset_1(C,A)
               => ( ( k1_mcart_1(B) = k1_mcart_1(C)
                    & k2_mcart_1(B) = k2_mcart_1(C) )
                 => B = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_mcart_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( ( r2_hidden(C,B)
            & r2_hidden(A,B)
            & k1_mcart_1(C) = k1_mcart_1(A)
            & k2_mcart_1(C) = k2_mcart_1(A) )
         => C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_mcart_1)).

tff(c_18,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12,plain,(
    m1_subset_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_10,plain,(
    k1_mcart_1('#skF_2') = k1_mcart_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8,plain,(
    k2_mcart_1('#skF_2') = k2_mcart_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_33,plain,(
    ! [C_13,A_14,B_15] :
      ( C_13 = A_14
      | k2_mcart_1(C_13) != k2_mcart_1(A_14)
      | k1_mcart_1(C_13) != k1_mcart_1(A_14)
      | ~ r2_hidden(A_14,B_15)
      | ~ r2_hidden(C_13,B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_35,plain,(
    ! [A_14,B_15] :
      ( A_14 = '#skF_2'
      | k2_mcart_1(A_14) != k2_mcart_1('#skF_3')
      | k1_mcart_1(A_14) != k1_mcart_1('#skF_2')
      | ~ r2_hidden(A_14,B_15)
      | ~ r2_hidden('#skF_2',B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_33])).

tff(c_40,plain,(
    ! [A_16,B_17] :
      ( A_16 = '#skF_2'
      | k2_mcart_1(A_16) != k2_mcart_1('#skF_3')
      | k1_mcart_1(A_16) != k1_mcart_1('#skF_3')
      | ~ r2_hidden(A_16,B_17)
      | ~ r2_hidden('#skF_2',B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_35])).

tff(c_44,plain,(
    ! [A_18,B_19] :
      ( A_18 = '#skF_2'
      | k2_mcart_1(A_18) != k2_mcart_1('#skF_3')
      | k1_mcart_1(A_18) != k1_mcart_1('#skF_3')
      | ~ r2_hidden('#skF_2',B_19)
      | ~ v1_relat_1(B_19)
      | v1_xboole_0(B_19)
      | ~ m1_subset_1(A_18,B_19) ) ),
    inference(resolution,[status(thm)],[c_2,c_40])).

tff(c_49,plain,(
    ! [A_20,B_21] :
      ( A_20 = '#skF_2'
      | k2_mcart_1(A_20) != k2_mcart_1('#skF_3')
      | k1_mcart_1(A_20) != k1_mcart_1('#skF_3')
      | ~ v1_relat_1(B_21)
      | ~ m1_subset_1(A_20,B_21)
      | v1_xboole_0(B_21)
      | ~ m1_subset_1('#skF_2',B_21) ) ),
    inference(resolution,[status(thm)],[c_2,c_44])).

tff(c_53,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_relat_1('#skF_1')
    | v1_xboole_0('#skF_1')
    | ~ m1_subset_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_49])).

tff(c_61,plain,
    ( '#skF_2' = '#skF_3'
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16,c_53])).

tff(c_63,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_6,c_61])).

%------------------------------------------------------------------------------
