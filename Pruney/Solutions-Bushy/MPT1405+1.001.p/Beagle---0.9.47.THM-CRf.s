%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1405+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:54 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 125 expanded)
%              Number of leaves         :   23 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :   84 ( 254 expanded)
%              Number of equality atoms :    6 (  30 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => m2_connsp_2(k2_struct_0(A),A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_38,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m2_connsp_2(C,A,B)
              <=> r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).

tff(c_20,plain,(
    ~ m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_12,plain,(
    ! [A_12] :
      ( l1_struct_0(A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_30,plain,(
    ! [A_18] :
      ( u1_struct_0(A_18) = k2_struct_0(A_18)
      | ~ l1_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_35,plain,(
    ! [A_19] :
      ( u1_struct_0(A_19) = k2_struct_0(A_19)
      | ~ l1_pre_topc(A_19) ) ),
    inference(resolution,[status(thm)],[c_12,c_30])).

tff(c_39,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_35])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_22])).

tff(c_45,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,B_21)
      | ~ m1_subset_1(A_20,k1_zfmisc_1(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_49,plain,(
    r1_tarski('#skF_2',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_40,c_45])).

tff(c_26,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_55,plain,(
    ! [A_24] :
      ( m1_subset_1(k2_struct_0(A_24),k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_63,plain,(
    ! [A_25] :
      ( r1_tarski(k2_struct_0(A_25),u1_struct_0(A_25))
      | ~ l1_struct_0(A_25) ) ),
    inference(resolution,[status(thm)],[c_55,c_14])).

tff(c_66,plain,
    ( r1_tarski(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_63])).

tff(c_76,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_79,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_76])).

tff(c_83,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_79])).

tff(c_85,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_61,plain,
    ( m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_55])).

tff(c_92,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_61])).

tff(c_18,plain,(
    ! [A_15] :
      ( k1_tops_1(A_15,k2_struct_0(A_15)) = k2_struct_0(A_15)
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_194,plain,(
    ! [C_41,A_42,B_43] :
      ( m2_connsp_2(C_41,A_42,B_43)
      | ~ r1_tarski(B_43,k1_tops_1(A_42,C_41))
      | ~ m1_subset_1(C_41,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42)
      | ~ v2_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_433,plain,(
    ! [A_87,B_88] :
      ( m2_connsp_2(k2_struct_0(A_87),A_87,B_88)
      | ~ r1_tarski(B_88,k2_struct_0(A_87))
      | ~ m1_subset_1(k2_struct_0(A_87),k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87)
      | ~ v2_pre_topc(A_87)
      | ~ l1_pre_topc(A_87)
      | ~ v2_pre_topc(A_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_194])).

tff(c_440,plain,(
    ! [B_88] :
      ( m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1',B_88)
      | ~ r1_tarski(B_88,k2_struct_0('#skF_1'))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_433])).

tff(c_460,plain,(
    ! [B_91] :
      ( m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1',B_91)
      | ~ r1_tarski(B_91,k2_struct_0('#skF_1'))
      | ~ m1_subset_1(B_91,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_26,c_24,c_39,c_92,c_440])).

tff(c_473,plain,
    ( m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1','#skF_2')
    | ~ r1_tarski('#skF_2',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_40,c_460])).

tff(c_481,plain,(
    m2_connsp_2(k2_struct_0('#skF_1'),'#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_473])).

tff(c_483,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_481])).

%------------------------------------------------------------------------------
