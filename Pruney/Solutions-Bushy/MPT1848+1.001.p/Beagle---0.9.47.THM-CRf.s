%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1848+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:32 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   34 (  44 expanded)
%              Number of leaves         :   17 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   55 (  85 expanded)
%              Number of equality atoms :    4 (  11 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_63,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ~ ( u1_struct_0(B) = u1_struct_0(A)
                & v1_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_tex_2)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l17_tex_2)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v1_subset_1(C,u1_struct_0(A)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(c_20,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_16,plain,(
    v1_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_22,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_18,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_14,plain,(
    ! [B_15,A_13] :
      ( m1_subset_1(u1_struct_0(B_15),k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ m1_pre_topc(B_15,A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_178,plain,(
    ! [B_39,A_40] :
      ( v1_subset_1(u1_struct_0(B_39),u1_struct_0(A_40))
      | ~ m1_subset_1(u1_struct_0(B_39),k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ v1_tex_2(B_39,A_40)
      | ~ m1_pre_topc(B_39,A_40)
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_200,plain,(
    ! [B_41,A_42] :
      ( v1_subset_1(u1_struct_0(B_41),u1_struct_0(A_42))
      | ~ v1_tex_2(B_41,A_42)
      | ~ m1_pre_topc(B_41,A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(resolution,[status(thm)],[c_14,c_178])).

tff(c_213,plain,(
    ! [B_41] :
      ( v1_subset_1(u1_struct_0(B_41),u1_struct_0('#skF_3'))
      | ~ v1_tex_2(B_41,'#skF_2')
      | ~ m1_pre_topc(B_41,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_200])).

tff(c_249,plain,(
    ! [B_46] :
      ( v1_subset_1(u1_struct_0(B_46),u1_struct_0('#skF_3'))
      | ~ v1_tex_2(B_46,'#skF_2')
      | ~ m1_pre_topc(B_46,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_213])).

tff(c_29,plain,(
    ! [B_20,A_21] :
      ( m1_subset_1(u1_struct_0(B_20),k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ m1_pre_topc(B_20,A_21)
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_42,plain,(
    ! [B_20] :
      ( m1_subset_1(u1_struct_0(B_20),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_20,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_29])).

tff(c_47,plain,(
    ! [B_22] :
      ( m1_subset_1(u1_struct_0(B_22),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_22,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_42])).

tff(c_12,plain,(
    ! [B_12] :
      ( ~ v1_subset_1(B_12,B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_54,plain,
    ( ~ v1_subset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_47,c_12])).

tff(c_61,plain,(
    ~ v1_subset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_54])).

tff(c_256,plain,
    ( ~ v1_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_249,c_61])).

tff(c_266,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16,c_256])).

%------------------------------------------------------------------------------
