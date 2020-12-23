%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:52 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 299 expanded)
%              Number of leaves         :   21 ( 106 expanded)
%              Depth                    :   16
%              Number of atoms          :  164 ( 700 expanded)
%              Number of equality atoms :   10 (  64 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( r1_tarski(k7_setfam_1(A,B),k7_setfam_1(A,C))
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_setfam_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> r1_tarski(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tops_2)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v2_tops_2(B,A)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tops_2)).

tff(c_22,plain,
    ( ~ r1_tarski('#skF_2',k7_setfam_1(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_30,plain,(
    ~ v2_tops_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_20,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k7_setfam_1(A_1,B_2),k1_zfmisc_1(k1_zfmisc_1(A_1)))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(k1_zfmisc_1(A_1))) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_32,plain,(
    ! [A_18,B_19] :
      ( k7_setfam_1(A_18,k7_setfam_1(A_18,B_19)) = B_19
      | ~ m1_subset_1(B_19,k1_zfmisc_1(k1_zfmisc_1(A_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_38,plain,(
    k7_setfam_1(u1_struct_0('#skF_1'),k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_18,c_32])).

tff(c_224,plain,(
    ! [B_39,C_40,A_41] :
      ( r1_tarski(B_39,C_40)
      | ~ r1_tarski(k7_setfam_1(A_41,B_39),k7_setfam_1(A_41,C_40))
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k1_zfmisc_1(A_41)))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(k1_zfmisc_1(A_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_245,plain,(
    ! [C_40] :
      ( r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),C_40)
      | ~ r1_tarski('#skF_2',k7_setfam_1(u1_struct_0('#skF_1'),C_40))
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_224])).

tff(c_323,plain,(
    ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_245])).

tff(c_326,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(resolution,[status(thm)],[c_2,c_323])).

tff(c_330,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_326])).

tff(c_332,plain,(
    m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_245])).

tff(c_14,plain,(
    ! [B_15,A_13] :
      ( v1_tops_2(B_15,A_13)
      | ~ r1_tarski(B_15,u1_pre_topc(A_13))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_13))))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_339,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_332,c_14])).

tff(c_353,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_339])).

tff(c_359,plain,(
    ~ r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),u1_pre_topc('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_353])).

tff(c_28,plain,
    ( v2_tops_2('#skF_2','#skF_1')
    | r1_tarski('#skF_2',k7_setfam_1(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_31,plain,(
    r1_tarski('#skF_2',k7_setfam_1(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28])).

tff(c_8,plain,(
    ! [A_9] :
      ( m1_subset_1(u1_pre_topc(A_9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_9))))
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_366,plain,(
    ! [C_49] :
      ( r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),C_49)
      | ~ r1_tarski('#skF_2',k7_setfam_1(u1_struct_0('#skF_1'),C_49))
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(splitRight,[status(thm)],[c_245])).

tff(c_377,plain,
    ( r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),u1_pre_topc('#skF_1'))
    | ~ r1_tarski('#skF_2',k7_setfam_1(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_366])).

tff(c_386,plain,(
    r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_31,c_377])).

tff(c_388,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_359,c_386])).

tff(c_389,plain,(
    v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_353])).

tff(c_10,plain,(
    ! [B_12,A_10] :
      ( v2_tops_2(B_12,A_10)
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0(A_10),B_12),A_10)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_10))))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_392,plain,
    ( v2_tops_2('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_389,c_10])).

tff(c_395,plain,(
    v2_tops_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_392])).

tff(c_397,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_395])).

tff(c_398,plain,(
    ~ r1_tarski('#skF_2',k7_setfam_1(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_399,plain,(
    v2_tops_2('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_491,plain,(
    ! [A_65,B_66] :
      ( v1_tops_2(k7_setfam_1(u1_struct_0(A_65),B_66),A_65)
      | ~ v2_tops_2(B_66,A_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_65))))
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_498,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v2_tops_2('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_491])).

tff(c_503,plain,(
    v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_399,c_498])).

tff(c_402,plain,(
    ! [A_50,B_51] :
      ( k7_setfam_1(A_50,k7_setfam_1(A_50,B_51)) = B_51
      | ~ m1_subset_1(B_51,k1_zfmisc_1(k1_zfmisc_1(A_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_408,plain,(
    k7_setfam_1(u1_struct_0('#skF_1'),k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_18,c_402])).

tff(c_509,plain,(
    ! [B_67,C_68,A_69] :
      ( r1_tarski(B_67,C_68)
      | ~ r1_tarski(k7_setfam_1(A_69,B_67),k7_setfam_1(A_69,C_68))
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k1_zfmisc_1(A_69)))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(k1_zfmisc_1(A_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_518,plain,(
    ! [C_68] :
      ( r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),C_68)
      | ~ r1_tarski('#skF_2',k7_setfam_1(u1_struct_0('#skF_1'),C_68))
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_408,c_509])).

tff(c_624,plain,(
    ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_518])).

tff(c_627,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(resolution,[status(thm)],[c_2,c_624])).

tff(c_631,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_627])).

tff(c_633,plain,(
    m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_518])).

tff(c_16,plain,(
    ! [B_15,A_13] :
      ( r1_tarski(B_15,u1_pre_topc(A_13))
      | ~ v1_tops_2(B_15,A_13)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_13))))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_643,plain,
    ( r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),u1_pre_topc('#skF_1'))
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_633,c_16])).

tff(c_657,plain,(
    r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_503,c_643])).

tff(c_407,plain,(
    ! [A_9] :
      ( k7_setfam_1(u1_struct_0(A_9),k7_setfam_1(u1_struct_0(A_9),u1_pre_topc(A_9))) = u1_pre_topc(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(resolution,[status(thm)],[c_8,c_402])).

tff(c_521,plain,(
    ! [B_67] :
      ( r1_tarski(B_67,k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'))
      | ~ r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'),B_67),'#skF_2')
      | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_408,c_509])).

tff(c_863,plain,(
    ! [B_88] :
      ( r1_tarski(B_88,k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'))
      | ~ r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'),B_88),'#skF_2')
      | ~ m1_subset_1(B_88,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_633,c_521])).

tff(c_888,plain,(
    ! [B_89] :
      ( r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'),B_89),k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'))
      | ~ r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'),k7_setfam_1(u1_struct_0('#skF_1'),B_89)),'#skF_2')
      | ~ m1_subset_1(B_89,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(resolution,[status(thm)],[c_2,c_863])).

tff(c_912,plain,
    ( r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ r1_tarski(u1_pre_topc('#skF_1'),'#skF_2')
    | ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_888])).

tff(c_926,plain,
    ( r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ r1_tarski(u1_pre_topc('#skF_1'),'#skF_2')
    | ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_912])).

tff(c_932,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_926])).

tff(c_942,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_932])).

tff(c_946,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_942])).

tff(c_948,plain,(
    m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_926])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k7_setfam_1(A_3,k7_setfam_1(A_3,B_4)) = B_4
      | ~ m1_subset_1(B_4,k1_zfmisc_1(k1_zfmisc_1(A_3))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_980,plain,(
    k7_setfam_1(u1_struct_0('#skF_1'),k7_setfam_1(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_948,c_4])).

tff(c_413,plain,(
    ! [A_52,B_53] :
      ( m1_subset_1(k7_setfam_1(A_52,B_53),k1_zfmisc_1(k1_zfmisc_1(A_52)))
      | ~ m1_subset_1(B_53,k1_zfmisc_1(k1_zfmisc_1(A_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_480,plain,(
    ! [A_63,B_64] :
      ( k7_setfam_1(A_63,k7_setfam_1(A_63,k7_setfam_1(A_63,B_64))) = k7_setfam_1(A_63,B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(k1_zfmisc_1(A_63))) ) ),
    inference(resolution,[status(thm)],[c_413,c_4])).

tff(c_526,plain,(
    ! [A_71] :
      ( k7_setfam_1(u1_struct_0(A_71),k7_setfam_1(u1_struct_0(A_71),k7_setfam_1(u1_struct_0(A_71),u1_pre_topc(A_71)))) = k7_setfam_1(u1_struct_0(A_71),u1_pre_topc(A_71))
      | ~ l1_pre_topc(A_71) ) ),
    inference(resolution,[status(thm)],[c_8,c_480])).

tff(c_540,plain,(
    ! [A_71] :
      ( m1_subset_1(k7_setfam_1(u1_struct_0(A_71),u1_pre_topc(A_71)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_71))))
      | ~ m1_subset_1(k7_setfam_1(u1_struct_0(A_71),k7_setfam_1(u1_struct_0(A_71),u1_pre_topc(A_71))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_71))))
      | ~ l1_pre_topc(A_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_526,c_2])).

tff(c_1064,plain,
    ( m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_980,c_540])).

tff(c_1121,plain,(
    m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_948,c_1064])).

tff(c_6,plain,(
    ! [B_6,C_8,A_5] :
      ( r1_tarski(B_6,C_8)
      | ~ r1_tarski(k7_setfam_1(A_5,B_6),k7_setfam_1(A_5,C_8))
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k1_zfmisc_1(A_5)))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(k1_zfmisc_1(A_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1100,plain,(
    ! [B_6] :
      ( r1_tarski(B_6,k7_setfam_1(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'),B_6),u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_980,c_6])).

tff(c_1555,plain,(
    ! [B_102] :
      ( r1_tarski(B_102,k7_setfam_1(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'),B_102),u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_102,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1121,c_1100])).

tff(c_1569,plain,
    ( r1_tarski('#skF_2',k7_setfam_1(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(resolution,[status(thm)],[c_657,c_1555])).

tff(c_1596,plain,(
    r1_tarski('#skF_2',k7_setfam_1(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1569])).

tff(c_1598,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_398,c_1596])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:30:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.57/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/1.62  
% 3.57/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/1.62  %$ v2_tops_2 > v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1
% 3.57/1.62  
% 3.57/1.62  %Foreground sorts:
% 3.57/1.62  
% 3.57/1.62  
% 3.57/1.62  %Background operators:
% 3.57/1.62  
% 3.57/1.62  
% 3.57/1.62  %Foreground operators:
% 3.57/1.62  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.57/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.57/1.62  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 3.57/1.62  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 3.57/1.62  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.57/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.57/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.57/1.62  tff('#skF_1', type, '#skF_1': $i).
% 3.57/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.57/1.62  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 3.57/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.57/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.57/1.62  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.57/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.57/1.62  
% 3.74/1.64  tff(f_74, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) <=> r1_tarski(B, k7_setfam_1(u1_struct_0(A), u1_pre_topc(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_tops_2)).
% 3.74/1.64  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 3.74/1.64  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 3.74/1.64  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(k7_setfam_1(A, B), k7_setfam_1(A, C)) => r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_setfam_1)).
% 3.74/1.64  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> r1_tarski(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_tops_2)).
% 3.74/1.64  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 3.74/1.64  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) <=> v1_tops_2(k7_setfam_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tops_2)).
% 3.74/1.64  tff(c_22, plain, (~r1_tarski('#skF_2', k7_setfam_1(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.74/1.64  tff(c_30, plain, (~v2_tops_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_22])).
% 3.74/1.64  tff(c_20, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.74/1.64  tff(c_18, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.74/1.64  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k7_setfam_1(A_1, B_2), k1_zfmisc_1(k1_zfmisc_1(A_1))) | ~m1_subset_1(B_2, k1_zfmisc_1(k1_zfmisc_1(A_1))))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.74/1.64  tff(c_32, plain, (![A_18, B_19]: (k7_setfam_1(A_18, k7_setfam_1(A_18, B_19))=B_19 | ~m1_subset_1(B_19, k1_zfmisc_1(k1_zfmisc_1(A_18))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.74/1.64  tff(c_38, plain, (k7_setfam_1(u1_struct_0('#skF_1'), k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_18, c_32])).
% 3.74/1.64  tff(c_224, plain, (![B_39, C_40, A_41]: (r1_tarski(B_39, C_40) | ~r1_tarski(k7_setfam_1(A_41, B_39), k7_setfam_1(A_41, C_40)) | ~m1_subset_1(C_40, k1_zfmisc_1(k1_zfmisc_1(A_41))) | ~m1_subset_1(B_39, k1_zfmisc_1(k1_zfmisc_1(A_41))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.74/1.64  tff(c_245, plain, (![C_40]: (r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), C_40) | ~r1_tarski('#skF_2', k7_setfam_1(u1_struct_0('#skF_1'), C_40)) | ~m1_subset_1(C_40, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_38, c_224])).
% 3.74/1.64  tff(c_323, plain, (~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitLeft, [status(thm)], [c_245])).
% 3.74/1.64  tff(c_326, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_2, c_323])).
% 3.74/1.64  tff(c_330, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_326])).
% 3.74/1.64  tff(c_332, plain, (m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_245])).
% 3.74/1.64  tff(c_14, plain, (![B_15, A_13]: (v1_tops_2(B_15, A_13) | ~r1_tarski(B_15, u1_pre_topc(A_13)) | ~m1_subset_1(B_15, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_13)))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.74/1.64  tff(c_339, plain, (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_332, c_14])).
% 3.74/1.64  tff(c_353, plain, (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_339])).
% 3.74/1.64  tff(c_359, plain, (~r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), u1_pre_topc('#skF_1'))), inference(splitLeft, [status(thm)], [c_353])).
% 3.74/1.64  tff(c_28, plain, (v2_tops_2('#skF_2', '#skF_1') | r1_tarski('#skF_2', k7_setfam_1(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.74/1.64  tff(c_31, plain, (r1_tarski('#skF_2', k7_setfam_1(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_30, c_28])).
% 3.74/1.64  tff(c_8, plain, (![A_9]: (m1_subset_1(u1_pre_topc(A_9), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_9)))) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.74/1.64  tff(c_366, plain, (![C_49]: (r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), C_49) | ~r1_tarski('#skF_2', k7_setfam_1(u1_struct_0('#skF_1'), C_49)) | ~m1_subset_1(C_49, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(splitRight, [status(thm)], [c_245])).
% 3.74/1.64  tff(c_377, plain, (r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), u1_pre_topc('#skF_1')) | ~r1_tarski('#skF_2', k7_setfam_1(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_366])).
% 3.74/1.64  tff(c_386, plain, (r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_31, c_377])).
% 3.74/1.64  tff(c_388, plain, $false, inference(negUnitSimplification, [status(thm)], [c_359, c_386])).
% 3.74/1.64  tff(c_389, plain, (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_353])).
% 3.74/1.64  tff(c_10, plain, (![B_12, A_10]: (v2_tops_2(B_12, A_10) | ~v1_tops_2(k7_setfam_1(u1_struct_0(A_10), B_12), A_10) | ~m1_subset_1(B_12, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_10)))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.74/1.64  tff(c_392, plain, (v2_tops_2('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_389, c_10])).
% 3.74/1.64  tff(c_395, plain, (v2_tops_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_392])).
% 3.74/1.64  tff(c_397, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_395])).
% 3.74/1.64  tff(c_398, plain, (~r1_tarski('#skF_2', k7_setfam_1(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_22])).
% 3.74/1.64  tff(c_399, plain, (v2_tops_2('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_22])).
% 3.74/1.64  tff(c_491, plain, (![A_65, B_66]: (v1_tops_2(k7_setfam_1(u1_struct_0(A_65), B_66), A_65) | ~v2_tops_2(B_66, A_65) | ~m1_subset_1(B_66, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_65)))) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.74/1.64  tff(c_498, plain, (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v2_tops_2('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_491])).
% 3.74/1.64  tff(c_503, plain, (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_399, c_498])).
% 3.74/1.64  tff(c_402, plain, (![A_50, B_51]: (k7_setfam_1(A_50, k7_setfam_1(A_50, B_51))=B_51 | ~m1_subset_1(B_51, k1_zfmisc_1(k1_zfmisc_1(A_50))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.74/1.64  tff(c_408, plain, (k7_setfam_1(u1_struct_0('#skF_1'), k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_18, c_402])).
% 3.74/1.64  tff(c_509, plain, (![B_67, C_68, A_69]: (r1_tarski(B_67, C_68) | ~r1_tarski(k7_setfam_1(A_69, B_67), k7_setfam_1(A_69, C_68)) | ~m1_subset_1(C_68, k1_zfmisc_1(k1_zfmisc_1(A_69))) | ~m1_subset_1(B_67, k1_zfmisc_1(k1_zfmisc_1(A_69))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.74/1.64  tff(c_518, plain, (![C_68]: (r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), C_68) | ~r1_tarski('#skF_2', k7_setfam_1(u1_struct_0('#skF_1'), C_68)) | ~m1_subset_1(C_68, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_408, c_509])).
% 3.74/1.64  tff(c_624, plain, (~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitLeft, [status(thm)], [c_518])).
% 3.74/1.64  tff(c_627, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_2, c_624])).
% 3.74/1.64  tff(c_631, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_627])).
% 3.74/1.64  tff(c_633, plain, (m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_518])).
% 3.74/1.64  tff(c_16, plain, (![B_15, A_13]: (r1_tarski(B_15, u1_pre_topc(A_13)) | ~v1_tops_2(B_15, A_13) | ~m1_subset_1(B_15, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_13)))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.74/1.64  tff(c_643, plain, (r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), u1_pre_topc('#skF_1')) | ~v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_633, c_16])).
% 3.74/1.64  tff(c_657, plain, (r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_503, c_643])).
% 3.74/1.64  tff(c_407, plain, (![A_9]: (k7_setfam_1(u1_struct_0(A_9), k7_setfam_1(u1_struct_0(A_9), u1_pre_topc(A_9)))=u1_pre_topc(A_9) | ~l1_pre_topc(A_9))), inference(resolution, [status(thm)], [c_8, c_402])).
% 3.74/1.64  tff(c_521, plain, (![B_67]: (r1_tarski(B_67, k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2')) | ~r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'), B_67), '#skF_2') | ~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1(B_67, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_408, c_509])).
% 3.74/1.64  tff(c_863, plain, (![B_88]: (r1_tarski(B_88, k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2')) | ~r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'), B_88), '#skF_2') | ~m1_subset_1(B_88, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_633, c_521])).
% 3.74/1.64  tff(c_888, plain, (![B_89]: (r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'), B_89), k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2')) | ~r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'), k7_setfam_1(u1_struct_0('#skF_1'), B_89)), '#skF_2') | ~m1_subset_1(B_89, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(resolution, [status(thm)], [c_2, c_863])).
% 3.74/1.64  tff(c_912, plain, (r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2')) | ~r1_tarski(u1_pre_topc('#skF_1'), '#skF_2') | ~m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_407, c_888])).
% 3.74/1.64  tff(c_926, plain, (r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2')) | ~r1_tarski(u1_pre_topc('#skF_1'), '#skF_2') | ~m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_912])).
% 3.74/1.64  tff(c_932, plain, (~m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitLeft, [status(thm)], [c_926])).
% 3.74/1.64  tff(c_942, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_932])).
% 3.74/1.64  tff(c_946, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_942])).
% 3.74/1.64  tff(c_948, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_926])).
% 3.74/1.64  tff(c_4, plain, (![A_3, B_4]: (k7_setfam_1(A_3, k7_setfam_1(A_3, B_4))=B_4 | ~m1_subset_1(B_4, k1_zfmisc_1(k1_zfmisc_1(A_3))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.74/1.64  tff(c_980, plain, (k7_setfam_1(u1_struct_0('#skF_1'), k7_setfam_1(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_948, c_4])).
% 3.74/1.64  tff(c_413, plain, (![A_52, B_53]: (m1_subset_1(k7_setfam_1(A_52, B_53), k1_zfmisc_1(k1_zfmisc_1(A_52))) | ~m1_subset_1(B_53, k1_zfmisc_1(k1_zfmisc_1(A_52))))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.74/1.64  tff(c_480, plain, (![A_63, B_64]: (k7_setfam_1(A_63, k7_setfam_1(A_63, k7_setfam_1(A_63, B_64)))=k7_setfam_1(A_63, B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(k1_zfmisc_1(A_63))))), inference(resolution, [status(thm)], [c_413, c_4])).
% 3.74/1.64  tff(c_526, plain, (![A_71]: (k7_setfam_1(u1_struct_0(A_71), k7_setfam_1(u1_struct_0(A_71), k7_setfam_1(u1_struct_0(A_71), u1_pre_topc(A_71))))=k7_setfam_1(u1_struct_0(A_71), u1_pre_topc(A_71)) | ~l1_pre_topc(A_71))), inference(resolution, [status(thm)], [c_8, c_480])).
% 3.74/1.64  tff(c_540, plain, (![A_71]: (m1_subset_1(k7_setfam_1(u1_struct_0(A_71), u1_pre_topc(A_71)), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_71)))) | ~m1_subset_1(k7_setfam_1(u1_struct_0(A_71), k7_setfam_1(u1_struct_0(A_71), u1_pre_topc(A_71))), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_71)))) | ~l1_pre_topc(A_71))), inference(superposition, [status(thm), theory('equality')], [c_526, c_2])).
% 3.74/1.64  tff(c_1064, plain, (m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_980, c_540])).
% 3.74/1.64  tff(c_1121, plain, (m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_948, c_1064])).
% 3.74/1.64  tff(c_6, plain, (![B_6, C_8, A_5]: (r1_tarski(B_6, C_8) | ~r1_tarski(k7_setfam_1(A_5, B_6), k7_setfam_1(A_5, C_8)) | ~m1_subset_1(C_8, k1_zfmisc_1(k1_zfmisc_1(A_5))) | ~m1_subset_1(B_6, k1_zfmisc_1(k1_zfmisc_1(A_5))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.74/1.64  tff(c_1100, plain, (![B_6]: (r1_tarski(B_6, k7_setfam_1(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'), B_6), u1_pre_topc('#skF_1')) | ~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1(B_6, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_980, c_6])).
% 3.74/1.64  tff(c_1555, plain, (![B_102]: (r1_tarski(B_102, k7_setfam_1(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~r1_tarski(k7_setfam_1(u1_struct_0('#skF_1'), B_102), u1_pre_topc('#skF_1')) | ~m1_subset_1(B_102, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_1121, c_1100])).
% 3.74/1.64  tff(c_1569, plain, (r1_tarski('#skF_2', k7_setfam_1(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_657, c_1555])).
% 3.74/1.64  tff(c_1596, plain, (r1_tarski('#skF_2', k7_setfam_1(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1569])).
% 3.74/1.64  tff(c_1598, plain, $false, inference(negUnitSimplification, [status(thm)], [c_398, c_1596])).
% 3.74/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/1.64  
% 3.74/1.64  Inference rules
% 3.74/1.64  ----------------------
% 3.74/1.64  #Ref     : 0
% 3.74/1.64  #Sup     : 329
% 3.74/1.64  #Fact    : 0
% 3.74/1.64  #Define  : 0
% 3.74/1.64  #Split   : 14
% 3.74/1.64  #Chain   : 0
% 3.74/1.64  #Close   : 0
% 3.74/1.64  
% 3.74/1.64  Ordering : KBO
% 3.74/1.64  
% 3.74/1.64  Simplification rules
% 3.74/1.64  ----------------------
% 3.74/1.64  #Subsume      : 101
% 3.74/1.64  #Demod        : 364
% 3.74/1.64  #Tautology    : 94
% 3.74/1.64  #SimpNegUnit  : 52
% 3.74/1.64  #BackRed      : 0
% 3.74/1.64  
% 3.74/1.64  #Partial instantiations: 0
% 3.74/1.64  #Strategies tried      : 1
% 3.74/1.64  
% 3.74/1.64  Timing (in seconds)
% 3.74/1.64  ----------------------
% 3.74/1.64  Preprocessing        : 0.28
% 3.74/1.64  Parsing              : 0.15
% 3.74/1.64  CNF conversion       : 0.02
% 3.74/1.64  Main loop            : 0.54
% 3.74/1.64  Inferencing          : 0.20
% 3.74/1.64  Reduction            : 0.18
% 3.74/1.64  Demodulation         : 0.12
% 3.74/1.64  BG Simplification    : 0.02
% 3.74/1.64  Subsumption          : 0.10
% 3.74/1.64  Abstraction          : 0.03
% 3.74/1.64  MUC search           : 0.00
% 3.74/1.64  Cooper               : 0.00
% 3.74/1.64  Total                : 0.85
% 3.74/1.64  Index Insertion      : 0.00
% 3.74/1.64  Index Deletion       : 0.00
% 3.74/1.64  Index Matching       : 0.00
% 3.74/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
