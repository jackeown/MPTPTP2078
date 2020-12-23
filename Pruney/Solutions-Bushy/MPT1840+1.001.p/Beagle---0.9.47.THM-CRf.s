%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1840+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:30 EST 2020

% Result     : Theorem 1.56s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   24 (  28 expanded)
%              Number of leaves         :   12 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  51 expanded)
%              Number of equality atoms :    2 (   6 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v7_struct_0 > v1_zfmisc_1 > l1_struct_0 > #nlpp > u1_struct_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( l1_struct_0(B)
           => ( ( u1_struct_0(A) = u1_struct_0(B)
                & v7_struct_0(A) )
             => v7_struct_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tex_2)).

tff(f_38,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

tff(f_32,axiom,(
    ! [A] :
      ( ( ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).

tff(c_8,plain,(
    v7_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_26,plain,(
    ! [A_5] :
      ( v1_zfmisc_1(u1_struct_0(A_5))
      | ~ l1_struct_0(A_5)
      | ~ v7_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ~ v7_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_19,plain,(
    ! [A_4] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_4))
      | ~ l1_struct_0(A_4)
      | v7_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_2')
    | v7_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_19])).

tff(c_24,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_1'))
    | v7_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_22])).

tff(c_25,plain,(
    ~ v1_zfmisc_1(u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_24])).

tff(c_29,plain,
    ( ~ l1_struct_0('#skF_1')
    | ~ v7_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_25])).

tff(c_39,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14,c_29])).

%------------------------------------------------------------------------------
