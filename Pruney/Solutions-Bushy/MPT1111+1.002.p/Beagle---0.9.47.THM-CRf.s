%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1111+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:25 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   44 (  60 expanded)
%              Number of leaves         :   22 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   52 ( 101 expanded)
%              Number of equality atoms :    9 (  16 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_67,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ~ ( B != k1_struct_0(A)
                & ! [C] :
                    ( m1_subset_1(C,u1_struct_0(A))
                   => ~ r2_hidden(C,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_pre_topc)).

tff(f_28,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => v1_xboole_0(k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_struct_0)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_31,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(c_20,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_24,plain,(
    ! [A_19] :
      ( v1_xboole_0(k1_struct_0(A_19))
      | ~ l1_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_29,plain,(
    ! [A_20] :
      ( k1_struct_0(A_20) = k1_xboole_0
      | ~ l1_struct_0(A_20) ) ),
    inference(resolution,[status(thm)],[c_24,c_12])).

tff(c_34,plain,(
    ! [A_21] :
      ( k1_struct_0(A_21) = k1_xboole_0
      | ~ l1_pre_topc(A_21) ) ),
    inference(resolution,[status(thm)],[c_2,c_29])).

tff(c_38,plain,(
    k1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_34])).

tff(c_16,plain,(
    k1_struct_0('#skF_2') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_45,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_16])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1('#skF_1'(A_2),A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_79,plain,(
    ! [A_25,C_26,B_27] :
      ( m1_subset_1(A_25,C_26)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(C_26))
      | ~ r2_hidden(A_25,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_87,plain,(
    ! [A_28] :
      ( m1_subset_1(A_28,u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_28,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_18,c_79])).

tff(c_14,plain,(
    ! [C_15] :
      ( ~ r2_hidden(C_15,'#skF_3')
      | ~ m1_subset_1(C_15,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_92,plain,(
    ! [A_29] : ~ r2_hidden(A_29,'#skF_3') ),
    inference(resolution,[status(thm)],[c_87,c_14])).

tff(c_97,plain,(
    ! [A_5] :
      ( v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_5,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_8,c_92])).

tff(c_99,plain,(
    ! [A_30] : ~ m1_subset_1(A_30,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_104,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_4,c_99])).

tff(c_105,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_114,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_105,c_12])).

tff(c_118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_114])).

%------------------------------------------------------------------------------
