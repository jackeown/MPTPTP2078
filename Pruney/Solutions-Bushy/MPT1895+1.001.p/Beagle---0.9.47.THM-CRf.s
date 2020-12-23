%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1895+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:39 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   41 (  69 expanded)
%              Number of leaves         :   21 (  37 expanded)
%              Depth                    :    6
%              Number of atoms          :   72 ( 199 expanded)
%              Number of equality atoms :   11 (  30 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v1_tops_1 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_pre_topc > a_2_0_tex_2 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(a_2_0_tex_2,type,(
    a_2_0_tex_2: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_tex_2(B,A)
             => k3_tarski(a_2_0_tex_2(A,B)) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_tex_2)).

tff(f_33,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_63,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
           => v1_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tex_2)).

tff(f_47,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k3_tarski(a_2_0_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tex_2)).

tff(c_22,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_10,plain,(
    k3_tarski(a_2_0_tex_2('#skF_1','#skF_2')) != u1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_20,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_18,plain,(
    v3_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_16,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_14,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_23,plain,(
    ! [A_11,B_12] :
      ( k2_pre_topc(A_11,B_12) = u1_struct_0(A_11)
      | ~ v1_tops_1(B_12,A_11)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = u1_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_23])).

tff(c_29,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = u1_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_26])).

tff(c_30,plain,(
    ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_29])).

tff(c_12,plain,(
    v3_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_39,plain,(
    ! [B_15,A_16] :
      ( v1_tops_1(B_15,A_16)
      | ~ v3_tex_2(B_15,A_16)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16)
      | ~ v3_tdlat_3(A_16)
      | ~ v2_pre_topc(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_42,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v3_tex_2('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v3_tdlat_3('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_39])).

tff(c_45,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_12,c_42])).

tff(c_47,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_30,c_45])).

tff(c_48,plain,(
    k2_pre_topc('#skF_1','#skF_2') = u1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_29])).

tff(c_69,plain,(
    ! [A_21,B_22] :
      ( k3_tarski(a_2_0_tex_2(A_21,B_22)) = k2_pre_topc(A_21,B_22)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(A_21)
      | ~ v3_tdlat_3(A_21)
      | ~ v2_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_72,plain,
    ( k3_tarski(a_2_0_tex_2('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v3_tdlat_3('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_69])).

tff(c_75,plain,
    ( k3_tarski(a_2_0_tex_2('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_48,c_72])).

tff(c_77,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_10,c_75])).

%------------------------------------------------------------------------------
