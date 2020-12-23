%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1900+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:39 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   41 (  52 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   65 ( 148 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v4_pre_topc > m1_subset_1 > v2_pre_topc > v1_tdlat_3 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => v5_pre_topc(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_tex_2)).

tff(f_49,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k8_relset_1(A,B,C,D),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tdlat_3)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v5_pre_topc(C,A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( v4_pre_topc(D,B)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,D),A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_pre_topc)).

tff(c_18,plain,(
    ~ v5_pre_topc('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_30,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_26,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_24,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_22,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_20,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_34,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_32,plain,(
    v1_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_10,plain,(
    ! [A_23,B_24,C_25,D_26] :
      ( m1_subset_1(k8_relset_1(A_23,B_24,C_25,D_26),k1_zfmisc_1(A_23))
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_38,plain,(
    ! [B_41,A_42] :
      ( v4_pre_topc(B_41,A_42)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ v1_tdlat_3(A_42)
      | ~ l1_pre_topc(A_42)
      | ~ v2_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_48,plain,(
    ! [A_43,B_44,C_45,D_46] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_43),B_44,C_45,D_46),A_43)
      | ~ v1_tdlat_3(A_43)
      | ~ l1_pre_topc(A_43)
      | ~ v2_pre_topc(A_43)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_43),B_44))) ) ),
    inference(resolution,[status(thm)],[c_10,c_38])).

tff(c_53,plain,(
    ! [D_46] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_46),'#skF_3')
      | ~ v1_tdlat_3('#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_48])).

tff(c_57,plain,(
    ! [D_46] : v4_pre_topc(k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_46),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_32,c_53])).

tff(c_88,plain,(
    ! [A_60,B_61,C_62] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(A_60),u1_struct_0(B_61),C_62,'#skF_1'(A_60,B_61,C_62)),A_60)
      | v5_pre_topc(C_62,A_60,B_61)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_60),u1_struct_0(B_61))))
      | ~ v1_funct_2(C_62,u1_struct_0(A_60),u1_struct_0(B_61))
      | ~ v1_funct_1(C_62)
      | ~ l1_pre_topc(B_61)
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_96,plain,
    ( v5_pre_topc('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_57,c_88])).

tff(c_100,plain,(
    v5_pre_topc('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_24,c_22,c_20,c_96])).

tff(c_102,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_100])).

%------------------------------------------------------------------------------
