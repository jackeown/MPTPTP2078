%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1299+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:45 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   40 (  62 expanded)
%              Number of leaves         :   16 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   57 ( 118 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_2 > v1_tops_2 > m1_subset_1 > l1_pre_topc > k7_setfam_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff(f_51,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ( v1_tops_2(B,A)
            <=> v2_tops_2(k7_setfam_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tops_2)).

tff(f_28,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v2_tops_2(B,A)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tops_2)).

tff(c_10,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k7_setfam_1(A_1,B_2),k1_zfmisc_1(k1_zfmisc_1(A_1)))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(k1_zfmisc_1(A_1))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_14,plain,
    ( ~ v2_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v1_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_21,plain,(
    ~ v1_tops_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_12,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,
    ( v1_tops_2('#skF_2','#skF_1')
    | v2_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    v2_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_21,c_20])).

tff(c_23,plain,(
    ! [A_9,B_10] :
      ( k7_setfam_1(A_9,k7_setfam_1(A_9,B_10)) = B_10
      | ~ m1_subset_1(B_10,k1_zfmisc_1(k1_zfmisc_1(A_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26,plain,(
    k7_setfam_1(u1_struct_0('#skF_1'),k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_10,c_23])).

tff(c_47,plain,(
    ! [A_15,B_16] :
      ( v1_tops_2(k7_setfam_1(u1_struct_0(A_15),B_16),A_15)
      | ~ v2_tops_2(B_16,A_15)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_15))))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_111,plain,(
    ! [A_21,B_22] :
      ( v1_tops_2(k7_setfam_1(u1_struct_0(A_21),k7_setfam_1(u1_struct_0(A_21),B_22)),A_21)
      | ~ v2_tops_2(k7_setfam_1(u1_struct_0(A_21),B_22),A_21)
      | ~ l1_pre_topc(A_21)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_21)))) ) ),
    inference(resolution,[status(thm)],[c_2,c_47])).

tff(c_127,plain,
    ( v1_tops_2('#skF_2','#skF_1')
    | ~ v2_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_111])).

tff(c_132,plain,(
    v1_tops_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12,c_22,c_127])).

tff(c_134,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21,c_132])).

tff(c_135,plain,(
    ~ v2_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_136,plain,(
    v1_tops_2('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_139,plain,(
    ! [A_23,B_24] :
      ( k7_setfam_1(A_23,k7_setfam_1(A_23,B_24)) = B_24
      | ~ m1_subset_1(B_24,k1_zfmisc_1(k1_zfmisc_1(A_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_142,plain,(
    k7_setfam_1(u1_struct_0('#skF_1'),k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_10,c_139])).

tff(c_163,plain,(
    ! [B_29,A_30] :
      ( v2_tops_2(B_29,A_30)
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0(A_30),B_29),A_30)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_30))))
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_165,plain,
    ( v2_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v1_tops_2('#skF_2','#skF_1')
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_163])).

tff(c_167,plain,
    ( v2_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_136,c_165])).

tff(c_168,plain,(
    ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_167])).

tff(c_171,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(resolution,[status(thm)],[c_2,c_168])).

tff(c_175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_171])).

%------------------------------------------------------------------------------
