%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1111+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:25 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   42 (  56 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :   55 ( 100 expanded)
%              Number of equality atoms :    8 (  13 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ~ ( B != k1_struct_0(A)
                & ! [C] :
                    ( m1_subset_1(C,u1_struct_0(A))
                   => ~ r2_hidden(C,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_pre_topc)).

tff(f_28,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => v1_xboole_0(k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_struct_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(c_16,plain,(
    k1_struct_0('#skF_2') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

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
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_52,plain,(
    ! [A_31,C_32,B_33] :
      ( m1_subset_1(A_31,C_32)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(C_32))
      | ~ r2_hidden(A_31,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_60,plain,(
    ! [A_34] :
      ( m1_subset_1(A_34,u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_34,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_18,c_52])).

tff(c_14,plain,(
    ! [C_16] :
      ( ~ r2_hidden(C_16,'#skF_3')
      | ~ m1_subset_1(C_16,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_65,plain,(
    ! [A_35] : ~ r2_hidden(A_35,'#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_14])).

tff(c_70,plain,(
    ! [A_5] :
      ( v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_5,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_8,c_65])).

tff(c_72,plain,(
    ! [A_36] : ~ m1_subset_1(A_36,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_77,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_4,c_72])).

tff(c_78,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_6,plain,(
    ! [A_4] :
      ( v1_xboole_0(k1_struct_0(A_4))
      | ~ l1_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_24,plain,(
    ! [B_20,A_21] :
      ( ~ v1_xboole_0(B_20)
      | B_20 = A_21
      | ~ v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_27,plain,(
    ! [A_4,A_21] :
      ( k1_struct_0(A_4) = A_21
      | ~ v1_xboole_0(A_21)
      | ~ l1_struct_0(A_4) ) ),
    inference(resolution,[status(thm)],[c_6,c_24])).

tff(c_95,plain,(
    ! [A_38] :
      ( k1_struct_0(A_38) = '#skF_3'
      | ~ l1_struct_0(A_38) ) ),
    inference(resolution,[status(thm)],[c_78,c_27])).

tff(c_100,plain,(
    ! [A_39] :
      ( k1_struct_0(A_39) = '#skF_3'
      | ~ l1_pre_topc(A_39) ) ),
    inference(resolution,[status(thm)],[c_2,c_95])).

tff(c_103,plain,(
    k1_struct_0('#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_20,c_100])).

tff(c_107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_103])).

%------------------------------------------------------------------------------
