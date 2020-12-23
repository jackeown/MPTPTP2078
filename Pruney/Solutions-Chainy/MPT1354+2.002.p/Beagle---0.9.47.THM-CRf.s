%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:52 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 234 expanded)
%              Number of leaves         :   21 (  86 expanded)
%              Depth                    :   13
%              Number of atoms          :  146 ( 553 expanded)
%              Number of equality atoms :    5 (  21 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_2 > v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v2_tops_2,type,(
    v2_tops_2: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ( v2_tops_2(B,A)
            <=> r1_tarski(B,k7_setfam_1(u1_struct_0(A),u1_pre_topc(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_tops_2)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( r1_tarski(k7_setfam_1(A,B),C)
          <=> r1_tarski(B,k7_setfam_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_setfam_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> r1_tarski(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tops_2)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> v2_tops_2(k7_setfam_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tops_2)).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_10,plain,(
    ! [A_9] :
      ( m1_subset_1(u1_pre_topc(A_9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_9))))
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_24,plain,
    ( ~ r1_tarski('#skF_2',k7_setfam_1(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_32,plain,(
    ~ v2_tops_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_30,plain,
    ( v2_tops_2('#skF_2','#skF_1')
    | r1_tarski('#skF_2',k7_setfam_1(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_33,plain,(
    r1_tarski('#skF_2',k7_setfam_1(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30])).

tff(c_226,plain,(
    ! [A_39,B_40,C_41] :
      ( r1_tarski(k7_setfam_1(A_39,B_40),C_41)
      | ~ r1_tarski(B_40,k7_setfam_1(A_39,C_41))
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k1_zfmisc_1(A_39)))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(k1_zfmisc_1(A_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_234,plain,(
    ! [A_9,B_40] :
      ( r1_tarski(k7_setfam_1(u1_struct_0(A_9),B_40),u1_pre_topc(A_9))
      | ~ r1_tarski(B_40,k7_setfam_1(u1_struct_0(A_9),u1_pre_topc(A_9)))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_9))))
      | ~ l1_pre_topc(A_9) ) ),
    inference(resolution,[status(thm)],[c_10,c_226])).

tff(c_34,plain,(
    ! [A_18,B_19] :
      ( k7_setfam_1(A_18,k7_setfam_1(A_18,B_19)) = B_19
      | ~ m1_subset_1(B_19,k1_zfmisc_1(k1_zfmisc_1(A_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_40,plain,(
    k7_setfam_1(u1_struct_0('#skF_1'),k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_20,c_34])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k7_setfam_1(A_1,B_2),k1_zfmisc_1(k1_zfmisc_1(A_1)))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(k1_zfmisc_1(A_1))) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_53,plain,(
    ! [B_22,A_23] :
      ( r1_tarski(B_22,u1_pre_topc(A_23))
      | ~ v1_tops_2(B_22,A_23)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_23))))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_63,plain,
    ( r1_tarski('#skF_2',u1_pre_topc('#skF_1'))
    | ~ v1_tops_2('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_53])).

tff(c_68,plain,
    ( r1_tarski('#skF_2',u1_pre_topc('#skF_1'))
    | ~ v1_tops_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_63])).

tff(c_69,plain,(
    ~ v1_tops_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_83,plain,(
    ! [B_26,A_27] :
      ( v1_tops_2(B_26,A_27)
      | ~ r1_tarski(B_26,u1_pre_topc(A_27))
      | ~ m1_subset_1(B_26,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_27))))
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_93,plain,
    ( v1_tops_2('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_2',u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_83])).

tff(c_98,plain,
    ( v1_tops_2('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_93])).

tff(c_99,plain,(
    ~ r1_tarski('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_98])).

tff(c_353,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(k7_setfam_1(u1_struct_0(A_51),B_52),u1_pre_topc(A_51))
      | ~ r1_tarski(B_52,k7_setfam_1(u1_struct_0(A_51),u1_pre_topc(A_51)))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_51))))
      | ~ l1_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_10,c_226])).

tff(c_371,plain,
    ( r1_tarski('#skF_2',u1_pre_topc('#skF_1'))
    | ~ r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k7_setfam_1(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_353])).

tff(c_375,plain,
    ( r1_tarski('#skF_2',u1_pre_topc('#skF_1'))
    | ~ r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k7_setfam_1(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_371])).

tff(c_376,plain,
    ( ~ r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k7_setfam_1(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_375])).

tff(c_377,plain,(
    ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_376])).

tff(c_380,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(resolution,[status(thm)],[c_2,c_377])).

tff(c_384,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_380])).

tff(c_386,plain,(
    m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_376])).

tff(c_14,plain,(
    ! [A_10,B_12] :
      ( v2_tops_2(k7_setfam_1(u1_struct_0(A_10),B_12),A_10)
      | ~ v1_tops_2(B_12,A_10)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_10))))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_395,plain,
    ( v2_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2')),'#skF_1')
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_386,c_14])).

tff(c_412,plain,
    ( v2_tops_2('#skF_2','#skF_1')
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_40,c_395])).

tff(c_413,plain,(
    ~ v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_412])).

tff(c_16,plain,(
    ! [B_15,A_13] :
      ( v1_tops_2(B_15,A_13)
      | ~ r1_tarski(B_15,u1_pre_topc(A_13))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_13))))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_398,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_386,c_16])).

tff(c_416,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_398])).

tff(c_422,plain,(
    ~ r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),u1_pre_topc('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_413,c_416])).

tff(c_425,plain,
    ( ~ r1_tarski('#skF_2',k7_setfam_1(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_234,c_422])).

tff(c_432,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_33,c_425])).

tff(c_433,plain,(
    ~ r1_tarski('#skF_2',k7_setfam_1(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_434,plain,(
    v2_tops_2('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_437,plain,(
    ! [A_53,B_54] :
      ( k7_setfam_1(A_53,k7_setfam_1(A_53,B_54)) = B_54
      | ~ m1_subset_1(B_54,k1_zfmisc_1(k1_zfmisc_1(A_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_443,plain,(
    k7_setfam_1(u1_struct_0('#skF_1'),k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_20,c_437])).

tff(c_522,plain,(
    ! [B_67,A_68] :
      ( v1_tops_2(B_67,A_68)
      | ~ v2_tops_2(k7_setfam_1(u1_struct_0(A_68),B_67),A_68)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_68))))
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_528,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v2_tops_2('#skF_2','#skF_1')
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_443,c_522])).

tff(c_531,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_434,c_528])).

tff(c_543,plain,(
    ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_531])).

tff(c_546,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(resolution,[status(thm)],[c_2,c_543])).

tff(c_550,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_546])).

tff(c_551,plain,(
    v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_531])).

tff(c_552,plain,(
    m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_531])).

tff(c_18,plain,(
    ! [B_15,A_13] :
      ( r1_tarski(B_15,u1_pre_topc(A_13))
      | ~ v1_tops_2(B_15,A_13)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_13))))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_562,plain,
    ( r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),u1_pre_topc('#skF_1'))
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_552,c_18])).

tff(c_575,plain,(
    r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_551,c_562])).

tff(c_635,plain,(
    ! [B_76,A_77,C_78] :
      ( r1_tarski(B_76,k7_setfam_1(A_77,C_78))
      | ~ r1_tarski(k7_setfam_1(A_77,B_76),C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k1_zfmisc_1(A_77)))
      | ~ m1_subset_1(B_76,k1_zfmisc_1(k1_zfmisc_1(A_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_639,plain,
    ( r1_tarski('#skF_2',k7_setfam_1(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(resolution,[status(thm)],[c_575,c_635])).

tff(c_646,plain,
    ( r1_tarski('#skF_2',k7_setfam_1(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_639])).

tff(c_647,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(negUnitSimplification,[status(thm)],[c_433,c_646])).

tff(c_652,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_647])).

tff(c_656,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_652])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:37:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.39/1.88  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.89  
% 3.39/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.89  %$ v2_tops_2 > v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1
% 3.39/1.89  
% 3.39/1.89  %Foreground sorts:
% 3.39/1.89  
% 3.39/1.89  
% 3.39/1.89  %Background operators:
% 3.39/1.89  
% 3.39/1.89  
% 3.39/1.89  %Foreground operators:
% 3.39/1.89  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.39/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.39/1.89  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 3.39/1.89  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 3.39/1.89  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.39/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.39/1.89  tff('#skF_2', type, '#skF_2': $i).
% 3.39/1.89  tff('#skF_1', type, '#skF_1': $i).
% 3.39/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.39/1.89  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 3.39/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.39/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.39/1.89  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.39/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.39/1.89  
% 3.39/1.92  tff(f_74, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) <=> r1_tarski(B, k7_setfam_1(u1_struct_0(A), u1_pre_topc(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_tops_2)).
% 3.39/1.92  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 3.39/1.92  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(k7_setfam_1(A, B), C) <=> r1_tarski(B, k7_setfam_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_setfam_1)).
% 3.39/1.92  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 3.39/1.92  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 3.39/1.92  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> r1_tarski(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_tops_2)).
% 3.39/1.92  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> v2_tops_2(k7_setfam_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_tops_2)).
% 3.39/1.92  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.39/1.92  tff(c_10, plain, (![A_9]: (m1_subset_1(u1_pre_topc(A_9), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_9)))) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.39/1.92  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.39/1.92  tff(c_24, plain, (~r1_tarski('#skF_2', k7_setfam_1(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.39/1.92  tff(c_32, plain, (~v2_tops_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_24])).
% 3.39/1.92  tff(c_30, plain, (v2_tops_2('#skF_2', '#skF_1') | r1_tarski('#skF_2', k7_setfam_1(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.39/1.92  tff(c_33, plain, (r1_tarski('#skF_2', k7_setfam_1(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_32, c_30])).
% 3.39/1.92  tff(c_226, plain, (![A_39, B_40, C_41]: (r1_tarski(k7_setfam_1(A_39, B_40), C_41) | ~r1_tarski(B_40, k7_setfam_1(A_39, C_41)) | ~m1_subset_1(C_41, k1_zfmisc_1(k1_zfmisc_1(A_39))) | ~m1_subset_1(B_40, k1_zfmisc_1(k1_zfmisc_1(A_39))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.39/1.92  tff(c_234, plain, (![A_9, B_40]: (r1_tarski(k7_setfam_1(u1_struct_0(A_9), B_40), u1_pre_topc(A_9)) | ~r1_tarski(B_40, k7_setfam_1(u1_struct_0(A_9), u1_pre_topc(A_9))) | ~m1_subset_1(B_40, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_9)))) | ~l1_pre_topc(A_9))), inference(resolution, [status(thm)], [c_10, c_226])).
% 3.39/1.92  tff(c_34, plain, (![A_18, B_19]: (k7_setfam_1(A_18, k7_setfam_1(A_18, B_19))=B_19 | ~m1_subset_1(B_19, k1_zfmisc_1(k1_zfmisc_1(A_18))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.39/1.92  tff(c_40, plain, (k7_setfam_1(u1_struct_0('#skF_1'), k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_20, c_34])).
% 3.39/1.92  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k7_setfam_1(A_1, B_2), k1_zfmisc_1(k1_zfmisc_1(A_1))) | ~m1_subset_1(B_2, k1_zfmisc_1(k1_zfmisc_1(A_1))))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.39/1.92  tff(c_53, plain, (![B_22, A_23]: (r1_tarski(B_22, u1_pre_topc(A_23)) | ~v1_tops_2(B_22, A_23) | ~m1_subset_1(B_22, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_23)))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.39/1.92  tff(c_63, plain, (r1_tarski('#skF_2', u1_pre_topc('#skF_1')) | ~v1_tops_2('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_53])).
% 3.39/1.92  tff(c_68, plain, (r1_tarski('#skF_2', u1_pre_topc('#skF_1')) | ~v1_tops_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_63])).
% 3.39/1.92  tff(c_69, plain, (~v1_tops_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_68])).
% 3.39/1.92  tff(c_83, plain, (![B_26, A_27]: (v1_tops_2(B_26, A_27) | ~r1_tarski(B_26, u1_pre_topc(A_27)) | ~m1_subset_1(B_26, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_27)))) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.39/1.92  tff(c_93, plain, (v1_tops_2('#skF_2', '#skF_1') | ~r1_tarski('#skF_2', u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_83])).
% 3.39/1.92  tff(c_98, plain, (v1_tops_2('#skF_2', '#skF_1') | ~r1_tarski('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_93])).
% 3.39/1.92  tff(c_99, plain, (~r1_tarski('#skF_2', u1_pre_topc('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_69, c_98])).
% 3.39/1.92  tff(c_353, plain, (![A_51, B_52]: (r1_tarski(k7_setfam_1(u1_struct_0(A_51), B_52), u1_pre_topc(A_51)) | ~r1_tarski(B_52, k7_setfam_1(u1_struct_0(A_51), u1_pre_topc(A_51))) | ~m1_subset_1(B_52, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_51)))) | ~l1_pre_topc(A_51))), inference(resolution, [status(thm)], [c_10, c_226])).
% 3.39/1.92  tff(c_371, plain, (r1_tarski('#skF_2', u1_pre_topc('#skF_1')) | ~r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k7_setfam_1(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_40, c_353])).
% 3.39/1.92  tff(c_375, plain, (r1_tarski('#skF_2', u1_pre_topc('#skF_1')) | ~r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k7_setfam_1(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_371])).
% 3.39/1.92  tff(c_376, plain, (~r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k7_setfam_1(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_99, c_375])).
% 3.39/1.92  tff(c_377, plain, (~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitLeft, [status(thm)], [c_376])).
% 3.39/1.92  tff(c_380, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_2, c_377])).
% 3.39/1.92  tff(c_384, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_380])).
% 3.39/1.92  tff(c_386, plain, (m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_376])).
% 3.39/1.92  tff(c_14, plain, (![A_10, B_12]: (v2_tops_2(k7_setfam_1(u1_struct_0(A_10), B_12), A_10) | ~v1_tops_2(B_12, A_10) | ~m1_subset_1(B_12, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_10)))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.39/1.92  tff(c_395, plain, (v2_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2')), '#skF_1') | ~v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_386, c_14])).
% 3.39/1.92  tff(c_412, plain, (v2_tops_2('#skF_2', '#skF_1') | ~v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_40, c_395])).
% 3.39/1.92  tff(c_413, plain, (~v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_32, c_412])).
% 3.39/1.92  tff(c_16, plain, (![B_15, A_13]: (v1_tops_2(B_15, A_13) | ~r1_tarski(B_15, u1_pre_topc(A_13)) | ~m1_subset_1(B_15, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_13)))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.61/1.92  tff(c_398, plain, (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_386, c_16])).
% 3.61/1.92  tff(c_416, plain, (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_398])).
% 3.61/1.92  tff(c_422, plain, (~r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), u1_pre_topc('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_413, c_416])).
% 3.61/1.92  tff(c_425, plain, (~r1_tarski('#skF_2', k7_setfam_1(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_234, c_422])).
% 3.61/1.92  tff(c_432, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_33, c_425])).
% 3.61/1.92  tff(c_433, plain, (~r1_tarski('#skF_2', k7_setfam_1(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_24])).
% 3.61/1.92  tff(c_434, plain, (v2_tops_2('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_24])).
% 3.61/1.92  tff(c_437, plain, (![A_53, B_54]: (k7_setfam_1(A_53, k7_setfam_1(A_53, B_54))=B_54 | ~m1_subset_1(B_54, k1_zfmisc_1(k1_zfmisc_1(A_53))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.61/1.92  tff(c_443, plain, (k7_setfam_1(u1_struct_0('#skF_1'), k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_20, c_437])).
% 3.61/1.92  tff(c_522, plain, (![B_67, A_68]: (v1_tops_2(B_67, A_68) | ~v2_tops_2(k7_setfam_1(u1_struct_0(A_68), B_67), A_68) | ~m1_subset_1(B_67, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_68)))) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.61/1.92  tff(c_528, plain, (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v2_tops_2('#skF_2', '#skF_1') | ~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_443, c_522])).
% 3.61/1.92  tff(c_531, plain, (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_434, c_528])).
% 3.61/1.92  tff(c_543, plain, (~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitLeft, [status(thm)], [c_531])).
% 3.61/1.92  tff(c_546, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_2, c_543])).
% 3.61/1.92  tff(c_550, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_546])).
% 3.61/1.92  tff(c_551, plain, (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_531])).
% 3.61/1.92  tff(c_552, plain, (m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_531])).
% 3.61/1.92  tff(c_18, plain, (![B_15, A_13]: (r1_tarski(B_15, u1_pre_topc(A_13)) | ~v1_tops_2(B_15, A_13) | ~m1_subset_1(B_15, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_13)))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.61/1.92  tff(c_562, plain, (r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), u1_pre_topc('#skF_1')) | ~v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_552, c_18])).
% 3.61/1.92  tff(c_575, plain, (r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_551, c_562])).
% 3.61/1.92  tff(c_635, plain, (![B_76, A_77, C_78]: (r1_tarski(B_76, k7_setfam_1(A_77, C_78)) | ~r1_tarski(k7_setfam_1(A_77, B_76), C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k1_zfmisc_1(A_77))) | ~m1_subset_1(B_76, k1_zfmisc_1(k1_zfmisc_1(A_77))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.61/1.92  tff(c_639, plain, (r1_tarski('#skF_2', k7_setfam_1(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_575, c_635])).
% 3.61/1.92  tff(c_646, plain, (r1_tarski('#skF_2', k7_setfam_1(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_639])).
% 3.61/1.92  tff(c_647, plain, (~m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_433, c_646])).
% 3.61/1.92  tff(c_652, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_10, c_647])).
% 3.61/1.92  tff(c_656, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_652])).
% 3.61/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.61/1.92  
% 3.61/1.92  Inference rules
% 3.61/1.92  ----------------------
% 3.61/1.92  #Ref     : 0
% 3.61/1.92  #Sup     : 141
% 3.61/1.92  #Fact    : 0
% 3.61/1.92  #Define  : 0
% 3.61/1.92  #Split   : 11
% 3.61/1.92  #Chain   : 0
% 3.61/1.92  #Close   : 0
% 3.61/1.92  
% 3.61/1.92  Ordering : KBO
% 3.61/1.92  
% 3.61/1.92  Simplification rules
% 3.61/1.92  ----------------------
% 3.61/1.92  #Subsume      : 10
% 3.61/1.92  #Demod        : 61
% 3.61/1.92  #Tautology    : 49
% 3.61/1.92  #SimpNegUnit  : 10
% 3.61/1.92  #BackRed      : 0
% 3.61/1.92  
% 3.61/1.92  #Partial instantiations: 0
% 3.61/1.92  #Strategies tried      : 1
% 3.61/1.92  
% 3.61/1.92  Timing (in seconds)
% 3.61/1.92  ----------------------
% 3.61/1.92  Preprocessing        : 0.46
% 3.61/1.92  Parsing              : 0.25
% 3.61/1.92  CNF conversion       : 0.03
% 3.61/1.92  Main loop            : 0.58
% 3.61/1.92  Inferencing          : 0.22
% 3.61/1.92  Reduction            : 0.17
% 3.61/1.92  Demodulation         : 0.11
% 3.61/1.92  BG Simplification    : 0.03
% 3.61/1.92  Subsumption          : 0.12
% 3.61/1.92  Abstraction          : 0.03
% 3.61/1.92  MUC search           : 0.00
% 3.61/1.92  Cooper               : 0.00
% 3.61/1.92  Total                : 1.09
% 3.61/1.92  Index Insertion      : 0.00
% 3.61/1.92  Index Deletion       : 0.00
% 3.61/1.93  Index Matching       : 0.00
% 3.61/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
