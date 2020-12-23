%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0755+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:48 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   42 (  64 expanded)
%              Number of leaves         :   18 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   70 ( 202 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v5_ordinal1 > v3_ordinal1 > v1_relat_1 > v1_funct_1 > k7_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v5_relat_1(B,A)
          & v1_funct_1(B)
          & v5_ordinal1(B) )
       => ! [C] :
            ( v3_ordinal1(C)
           => ( v1_relat_1(k7_relat_1(B,C))
              & v5_relat_1(k7_relat_1(B,C),A)
              & v1_funct_1(k7_relat_1(B,C))
              & v5_ordinal1(k7_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_ordinal1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,B) )
     => ( v1_relat_1(k7_relat_1(C,A))
        & v5_relat_1(k7_relat_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc22_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v5_ordinal1(A)
        & v3_ordinal1(B) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v5_relat_1(k7_relat_1(A,B),k2_relat_1(A))
        & v5_ordinal1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_ordinal1)).

tff(f_28,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_24,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( v1_funct_1(k7_relat_1(A_8,B_9))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_26,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4,plain,(
    ! [C_5,A_3,B_4] :
      ( v5_relat_1(k7_relat_1(C_5,A_3),B_4)
      | ~ v5_relat_1(C_5,B_4)
      | ~ v1_relat_1(C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_22,plain,(
    v5_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_20,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( v5_ordinal1(k7_relat_1(A_6,B_7))
      | ~ v3_ordinal1(B_7)
      | ~ v5_ordinal1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k7_relat_1(A_1,B_2))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_18,plain,
    ( ~ v5_ordinal1(k7_relat_1('#skF_2','#skF_3'))
    | ~ v1_funct_1(k7_relat_1('#skF_2','#skF_3'))
    | ~ v5_relat_1(k7_relat_1('#skF_2','#skF_3'),'#skF_1')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_33,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_36,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_33])).

tff(c_40,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_36])).

tff(c_41,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_2','#skF_3'),'#skF_1')
    | ~ v1_funct_1(k7_relat_1('#skF_2','#skF_3'))
    | ~ v5_ordinal1(k7_relat_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_43,plain,(
    ~ v5_ordinal1(k7_relat_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_41])).

tff(c_46,plain,
    ( ~ v3_ordinal1('#skF_3')
    | ~ v5_ordinal1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_43])).

tff(c_50,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_22,c_20,c_46])).

tff(c_51,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_2','#skF_3'))
    | ~ v5_relat_1(k7_relat_1('#skF_2','#skF_3'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_41])).

tff(c_53,plain,(
    ~ v5_relat_1(k7_relat_1('#skF_2','#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_51])).

tff(c_56,plain,
    ( ~ v5_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_53])).

tff(c_60,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_56])).

tff(c_61,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_51])).

tff(c_65,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_61])).

tff(c_69,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_65])).

%------------------------------------------------------------------------------
