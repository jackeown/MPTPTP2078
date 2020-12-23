%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0812+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:52 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   29 (  35 expanded)
%              Number of leaves         :   14 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   66 (  98 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_wellord1 > r4_wellord1 > v2_wellord1 > v1_relat_1 > v1_funct_1 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(r4_wellord1,type,(
    r4_wellord1: ( $i * $i ) > $o )).

tff(r3_wellord1,type,(
    r3_wellord1: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( ( r4_wellord1(A,B)
                & v2_wellord1(A) )
             => v2_wellord1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_wellord1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
          <=> ? [C] :
                ( v1_relat_1(C)
                & v1_funct_1(C)
                & r3_wellord1(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_wellord1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ( ( v2_wellord1(A)
                  & r3_wellord1(A,B,C) )
               => v2_wellord1(B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_wellord1)).

tff(c_12,plain,(
    ~ v2_wellord1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_18,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_14,plain,(
    v2_wellord1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_16,plain,(
    r4_wellord1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    ! [A_1,B_7] :
      ( v1_funct_1('#skF_1'(A_1,B_7))
      | ~ r4_wellord1(A_1,B_7)
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_1,B_7] :
      ( v1_relat_1('#skF_1'(A_1,B_7))
      | ~ r4_wellord1(A_1,B_7)
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4,plain,(
    ! [A_1,B_7] :
      ( r3_wellord1(A_1,B_7,'#skF_1'(A_1,B_7))
      | ~ r4_wellord1(A_1,B_7)
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_29,plain,(
    ! [B_28,A_29,C_30] :
      ( v2_wellord1(B_28)
      | ~ r3_wellord1(A_29,B_28,C_30)
      | ~ v2_wellord1(A_29)
      | ~ v1_funct_1(C_30)
      | ~ v1_relat_1(C_30)
      | ~ v1_relat_1(B_28)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_34,plain,(
    ! [B_31,A_32] :
      ( v2_wellord1(B_31)
      | ~ v2_wellord1(A_32)
      | ~ v1_funct_1('#skF_1'(A_32,B_31))
      | ~ v1_relat_1('#skF_1'(A_32,B_31))
      | ~ r4_wellord1(A_32,B_31)
      | ~ v1_relat_1(B_31)
      | ~ v1_relat_1(A_32) ) ),
    inference(resolution,[status(thm)],[c_4,c_29])).

tff(c_39,plain,(
    ! [B_33,A_34] :
      ( v2_wellord1(B_33)
      | ~ v2_wellord1(A_34)
      | ~ v1_funct_1('#skF_1'(A_34,B_33))
      | ~ r4_wellord1(A_34,B_33)
      | ~ v1_relat_1(B_33)
      | ~ v1_relat_1(A_34) ) ),
    inference(resolution,[status(thm)],[c_8,c_34])).

tff(c_44,plain,(
    ! [B_35,A_36] :
      ( v2_wellord1(B_35)
      | ~ v2_wellord1(A_36)
      | ~ r4_wellord1(A_36,B_35)
      | ~ v1_relat_1(B_35)
      | ~ v1_relat_1(A_36) ) ),
    inference(resolution,[status(thm)],[c_6,c_39])).

tff(c_47,plain,
    ( v2_wellord1('#skF_3')
    | ~ v2_wellord1('#skF_2')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_44])).

tff(c_50,plain,(
    v2_wellord1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_14,c_47])).

tff(c_52,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_50])).

%------------------------------------------------------------------------------
