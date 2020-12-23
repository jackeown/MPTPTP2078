%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1898+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:39 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 107 expanded)
%              Number of leaves         :   21 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :   97 ( 329 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ? [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
            & v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tex_2)).

tff(f_29,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_43,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_66,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ~ ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ~ ( r1_tarski(B,C)
                      & v3_tex_2(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tex_2)).

tff(c_22,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_20,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_18,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_16,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2,plain,(
    ! [A_1] : v1_xboole_0('#skF_1'(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4,plain,(
    ! [A_1] : m1_subset_1('#skF_1'(A_1),k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_31,plain,(
    ! [B_17,A_18] :
      ( v2_tex_2(B_17,A_18)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ v1_xboole_0(B_17)
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_35,plain,(
    ! [A_18] :
      ( v2_tex_2('#skF_1'(u1_struct_0(A_18)),A_18)
      | ~ v1_xboole_0('#skF_1'(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18)
      | v2_struct_0(A_18) ) ),
    inference(resolution,[status(thm)],[c_4,c_31])).

tff(c_38,plain,(
    ! [A_18] :
      ( v2_tex_2('#skF_1'(u1_struct_0(A_18)),A_18)
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18)
      | v2_struct_0(A_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_35])).

tff(c_52,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1('#skF_2'(A_26,B_27),k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ v2_tex_2(B_27,A_26)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26)
      | ~ v3_tdlat_3(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_14,plain,(
    ! [B_13] :
      ( ~ v3_tex_2(B_13,'#skF_3')
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_63,plain,(
    ! [B_27] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_27),'#skF_3')
      | ~ v2_tex_2(B_27,'#skF_3')
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_52,c_14])).

tff(c_69,plain,(
    ! [B_27] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_27),'#skF_3')
      | ~ v2_tex_2(B_27,'#skF_3')
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_63])).

tff(c_71,plain,(
    ! [B_28] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_28),'#skF_3')
      | ~ v2_tex_2(B_28,'#skF_3')
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_69])).

tff(c_84,plain,
    ( ~ v3_tex_2('#skF_2'('#skF_3','#skF_1'(u1_struct_0('#skF_3'))),'#skF_3')
    | ~ v2_tex_2('#skF_1'(u1_struct_0('#skF_3')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_71])).

tff(c_85,plain,(
    ~ v2_tex_2('#skF_1'(u1_struct_0('#skF_3')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_88,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_85])).

tff(c_91,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16,c_88])).

tff(c_93,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_91])).

tff(c_95,plain,(
    v2_tex_2('#skF_1'(u1_struct_0('#skF_3')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_45,plain,(
    ! [A_22,B_23] :
      ( v3_tex_2('#skF_2'(A_22,B_23),A_22)
      | ~ v2_tex_2(B_23,A_22)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22)
      | ~ v3_tdlat_3(A_22)
      | ~ v2_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_49,plain,(
    ! [A_22] :
      ( v3_tex_2('#skF_2'(A_22,'#skF_1'(u1_struct_0(A_22))),A_22)
      | ~ v2_tex_2('#skF_1'(u1_struct_0(A_22)),A_22)
      | ~ l1_pre_topc(A_22)
      | ~ v3_tdlat_3(A_22)
      | ~ v2_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(resolution,[status(thm)],[c_4,c_45])).

tff(c_94,plain,(
    ~ v3_tex_2('#skF_2'('#skF_3','#skF_1'(u1_struct_0('#skF_3'))),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_99,plain,
    ( ~ v2_tex_2('#skF_1'(u1_struct_0('#skF_3')),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_49,c_94])).

tff(c_102,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_95,c_99])).

tff(c_104,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_102])).

%------------------------------------------------------------------------------
