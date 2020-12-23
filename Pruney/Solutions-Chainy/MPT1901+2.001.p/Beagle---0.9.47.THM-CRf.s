%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:36 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 369 expanded)
%              Number of leaves         :   26 ( 143 expanded)
%              Depth                    :   20
%              Number of atoms          :  279 (2108 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v3_pre_topc > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k7_tmap_1 > k6_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k7_tmap_1,type,(
    k7_tmap_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

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

tff(f_129,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ( ! [B] :
              ( ( ~ v2_struct_0(B)
                & v2_pre_topc(B)
                & l1_pre_topc(B) )
             => ! [C] :
                  ( ( v1_funct_1(C)
                    & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                    & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                 => v5_pre_topc(C,A,B) ) )
         => v1_tdlat_3(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tex_2)).

tff(f_102,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_funct_1(k7_tmap_1(A,B))
        & v1_funct_2(k7_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B)))
        & m1_subset_1(k7_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B))))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( ~ v2_struct_0(k6_tmap_1(A,B))
        & v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tmap_1)).

tff(f_91,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> ( v1_funct_1(k7_tmap_1(A,B))
              & v1_funct_2(k7_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B)))
              & v5_pre_topc(k7_tmap_1(A,B),A,k6_tmap_1(A,B))
              & m1_subset_1(k7_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B))))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_tmap_1)).

tff(c_36,plain,(
    ~ v1_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_42,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_34,plain,(
    ! [A_10] :
      ( m1_subset_1('#skF_1'(A_10),k1_zfmisc_1(u1_struct_0(A_10)))
      | v1_tdlat_3(A_10)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_59,plain,(
    ! [A_29,B_30] :
      ( l1_pre_topc(k6_tmap_1(A_29,B_30))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_63,plain,(
    ! [A_10] :
      ( l1_pre_topc(k6_tmap_1(A_10,'#skF_1'(A_10)))
      | v2_struct_0(A_10)
      | v1_tdlat_3(A_10)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10) ) ),
    inference(resolution,[status(thm)],[c_34,c_59])).

tff(c_65,plain,(
    ! [A_32,B_33] :
      ( v1_funct_1(k7_tmap_1(A_32,B_33))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_69,plain,(
    ! [A_10] :
      ( v1_funct_1(k7_tmap_1(A_10,'#skF_1'(A_10)))
      | v2_struct_0(A_10)
      | v1_tdlat_3(A_10)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10) ) ),
    inference(resolution,[status(thm)],[c_34,c_65])).

tff(c_76,plain,(
    ! [A_37,B_38] :
      ( v2_pre_topc(k6_tmap_1(A_37,B_38))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_80,plain,(
    ! [A_10] :
      ( v2_pre_topc(k6_tmap_1(A_10,'#skF_1'(A_10)))
      | v2_struct_0(A_10)
      | v1_tdlat_3(A_10)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10) ) ),
    inference(resolution,[status(thm)],[c_34,c_76])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( v1_funct_2(k7_tmap_1(A_3,B_4),u1_struct_0(A_3),u1_struct_0(k6_tmap_1(A_3,B_4)))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ l1_pre_topc(A_3)
      | ~ v2_pre_topc(A_3)
      | v2_struct_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_85,plain,(
    ! [A_45,B_46] :
      ( m1_subset_1(k7_tmap_1(A_45,B_46),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_45),u1_struct_0(k6_tmap_1(A_45,B_46)))))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_38,plain,(
    ! [C_19,B_17] :
      ( v5_pre_topc(C_19,'#skF_2',B_17)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_17))))
      | ~ v1_funct_2(C_19,u1_struct_0('#skF_2'),u1_struct_0(B_17))
      | ~ v1_funct_1(C_19)
      | ~ l1_pre_topc(B_17)
      | ~ v2_pre_topc(B_17)
      | v2_struct_0(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_89,plain,(
    ! [B_46] :
      ( v5_pre_topc(k7_tmap_1('#skF_2',B_46),'#skF_2',k6_tmap_1('#skF_2',B_46))
      | ~ v1_funct_2(k7_tmap_1('#skF_2',B_46),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2',B_46)))
      | ~ v1_funct_1(k7_tmap_1('#skF_2',B_46))
      | ~ l1_pre_topc(k6_tmap_1('#skF_2',B_46))
      | ~ v2_pre_topc(k6_tmap_1('#skF_2',B_46))
      | v2_struct_0(k6_tmap_1('#skF_2',B_46))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_85,c_38])).

tff(c_92,plain,(
    ! [B_46] :
      ( v5_pre_topc(k7_tmap_1('#skF_2',B_46),'#skF_2',k6_tmap_1('#skF_2',B_46))
      | ~ v1_funct_2(k7_tmap_1('#skF_2',B_46),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2',B_46)))
      | ~ v1_funct_1(k7_tmap_1('#skF_2',B_46))
      | ~ l1_pre_topc(k6_tmap_1('#skF_2',B_46))
      | ~ v2_pre_topc(k6_tmap_1('#skF_2',B_46))
      | v2_struct_0(k6_tmap_1('#skF_2',B_46))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_89])).

tff(c_94,plain,(
    ! [B_47] :
      ( v5_pre_topc(k7_tmap_1('#skF_2',B_47),'#skF_2',k6_tmap_1('#skF_2',B_47))
      | ~ v1_funct_2(k7_tmap_1('#skF_2',B_47),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2',B_47)))
      | ~ v1_funct_1(k7_tmap_1('#skF_2',B_47))
      | ~ l1_pre_topc(k6_tmap_1('#skF_2',B_47))
      | ~ v2_pre_topc(k6_tmap_1('#skF_2',B_47))
      | v2_struct_0(k6_tmap_1('#skF_2',B_47))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_92])).

tff(c_98,plain,(
    ! [B_4] :
      ( v5_pre_topc(k7_tmap_1('#skF_2',B_4),'#skF_2',k6_tmap_1('#skF_2',B_4))
      | ~ v1_funct_1(k7_tmap_1('#skF_2',B_4))
      | ~ l1_pre_topc(k6_tmap_1('#skF_2',B_4))
      | ~ v2_pre_topc(k6_tmap_1('#skF_2',B_4))
      | v2_struct_0(k6_tmap_1('#skF_2',B_4))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_10,c_94])).

tff(c_101,plain,(
    ! [B_4] :
      ( v5_pre_topc(k7_tmap_1('#skF_2',B_4),'#skF_2',k6_tmap_1('#skF_2',B_4))
      | ~ v1_funct_1(k7_tmap_1('#skF_2',B_4))
      | ~ l1_pre_topc(k6_tmap_1('#skF_2',B_4))
      | ~ v2_pre_topc(k6_tmap_1('#skF_2',B_4))
      | v2_struct_0(k6_tmap_1('#skF_2',B_4))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_98])).

tff(c_102,plain,(
    ! [B_4] :
      ( v5_pre_topc(k7_tmap_1('#skF_2',B_4),'#skF_2',k6_tmap_1('#skF_2',B_4))
      | ~ v1_funct_1(k7_tmap_1('#skF_2',B_4))
      | ~ l1_pre_topc(k6_tmap_1('#skF_2',B_4))
      | ~ v2_pre_topc(k6_tmap_1('#skF_2',B_4))
      | v2_struct_0(k6_tmap_1('#skF_2',B_4))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_101])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k7_tmap_1(A_3,B_4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3),u1_struct_0(k6_tmap_1(A_3,B_4)))))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ l1_pre_topc(A_3)
      | ~ v2_pre_topc(A_3)
      | v2_struct_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_104,plain,(
    ! [B_49,A_50] :
      ( v3_pre_topc(B_49,A_50)
      | ~ m1_subset_1(k7_tmap_1(A_50,B_49),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_50),u1_struct_0(k6_tmap_1(A_50,B_49)))))
      | ~ v5_pre_topc(k7_tmap_1(A_50,B_49),A_50,k6_tmap_1(A_50,B_49))
      | ~ v1_funct_2(k7_tmap_1(A_50,B_49),u1_struct_0(A_50),u1_struct_0(k6_tmap_1(A_50,B_49)))
      | ~ v1_funct_1(k7_tmap_1(A_50,B_49))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50)
      | ~ v2_pre_topc(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_109,plain,(
    ! [B_51,A_52] :
      ( v3_pre_topc(B_51,A_52)
      | ~ v5_pre_topc(k7_tmap_1(A_52,B_51),A_52,k6_tmap_1(A_52,B_51))
      | ~ v1_funct_2(k7_tmap_1(A_52,B_51),u1_struct_0(A_52),u1_struct_0(k6_tmap_1(A_52,B_51)))
      | ~ v1_funct_1(k7_tmap_1(A_52,B_51))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52)
      | ~ v2_pre_topc(A_52)
      | v2_struct_0(A_52) ) ),
    inference(resolution,[status(thm)],[c_8,c_104])).

tff(c_114,plain,(
    ! [B_53,A_54] :
      ( v3_pre_topc(B_53,A_54)
      | ~ v5_pre_topc(k7_tmap_1(A_54,B_53),A_54,k6_tmap_1(A_54,B_53))
      | ~ v1_funct_1(k7_tmap_1(A_54,B_53))
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54)
      | ~ v2_pre_topc(A_54)
      | v2_struct_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_10,c_109])).

tff(c_117,plain,(
    ! [B_4] :
      ( v3_pre_topc(B_4,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ v1_funct_1(k7_tmap_1('#skF_2',B_4))
      | ~ l1_pre_topc(k6_tmap_1('#skF_2',B_4))
      | ~ v2_pre_topc(k6_tmap_1('#skF_2',B_4))
      | v2_struct_0(k6_tmap_1('#skF_2',B_4))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_102,c_114])).

tff(c_123,plain,(
    ! [B_4] :
      ( v3_pre_topc(B_4,'#skF_2')
      | v2_struct_0('#skF_2')
      | ~ v1_funct_1(k7_tmap_1('#skF_2',B_4))
      | ~ l1_pre_topc(k6_tmap_1('#skF_2',B_4))
      | ~ v2_pre_topc(k6_tmap_1('#skF_2',B_4))
      | v2_struct_0(k6_tmap_1('#skF_2',B_4))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_117])).

tff(c_126,plain,(
    ! [B_55] :
      ( v3_pre_topc(B_55,'#skF_2')
      | ~ v1_funct_1(k7_tmap_1('#skF_2',B_55))
      | ~ l1_pre_topc(k6_tmap_1('#skF_2',B_55))
      | ~ v2_pre_topc(k6_tmap_1('#skF_2',B_55))
      | v2_struct_0(k6_tmap_1('#skF_2',B_55))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_123])).

tff(c_130,plain,
    ( v3_pre_topc('#skF_1'('#skF_2'),'#skF_2')
    | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_1'('#skF_2')))
    | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_1'('#skF_2')))
    | ~ v2_pre_topc(k6_tmap_1('#skF_2','#skF_1'('#skF_2')))
    | v2_struct_0(k6_tmap_1('#skF_2','#skF_1'('#skF_2')))
    | v1_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_126])).

tff(c_133,plain,
    ( v3_pre_topc('#skF_1'('#skF_2'),'#skF_2')
    | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_1'('#skF_2')))
    | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_1'('#skF_2')))
    | ~ v2_pre_topc(k6_tmap_1('#skF_2','#skF_1'('#skF_2')))
    | v2_struct_0(k6_tmap_1('#skF_2','#skF_1'('#skF_2')))
    | v1_tdlat_3('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_130])).

tff(c_134,plain,
    ( v3_pre_topc('#skF_1'('#skF_2'),'#skF_2')
    | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_1'('#skF_2')))
    | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_1'('#skF_2')))
    | ~ v2_pre_topc(k6_tmap_1('#skF_2','#skF_1'('#skF_2')))
    | v2_struct_0(k6_tmap_1('#skF_2','#skF_1'('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_133])).

tff(c_135,plain,(
    ~ v2_pre_topc(k6_tmap_1('#skF_2','#skF_1'('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_138,plain,
    ( v2_struct_0('#skF_2')
    | v1_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_135])).

tff(c_141,plain,
    ( v2_struct_0('#skF_2')
    | v1_tdlat_3('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_138])).

tff(c_143,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_44,c_141])).

tff(c_144,plain,
    ( ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_1'('#skF_2')))
    | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_1'('#skF_2')))
    | v2_struct_0(k6_tmap_1('#skF_2','#skF_1'('#skF_2')))
    | v3_pre_topc('#skF_1'('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_146,plain,(
    ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_1'('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_149,plain,
    ( v2_struct_0('#skF_2')
    | v1_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_69,c_146])).

tff(c_152,plain,
    ( v2_struct_0('#skF_2')
    | v1_tdlat_3('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_149])).

tff(c_154,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_44,c_152])).

tff(c_155,plain,
    ( ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_1'('#skF_2')))
    | v3_pre_topc('#skF_1'('#skF_2'),'#skF_2')
    | v2_struct_0(k6_tmap_1('#skF_2','#skF_1'('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_157,plain,(
    ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_1'('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_155])).

tff(c_160,plain,
    ( v2_struct_0('#skF_2')
    | v1_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_63,c_157])).

tff(c_163,plain,
    ( v2_struct_0('#skF_2')
    | v1_tdlat_3('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_160])).

tff(c_165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_44,c_163])).

tff(c_166,plain,
    ( v2_struct_0(k6_tmap_1('#skF_2','#skF_1'('#skF_2')))
    | v3_pre_topc('#skF_1'('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_155])).

tff(c_168,plain,(
    v3_pre_topc('#skF_1'('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_32,plain,(
    ! [A_10] :
      ( ~ v3_pre_topc('#skF_1'(A_10),A_10)
      | v1_tdlat_3(A_10)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_171,plain,
    ( v1_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_168,c_32])).

tff(c_174,plain,(
    v1_tdlat_3('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_171])).

tff(c_176,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_174])).

tff(c_177,plain,(
    v2_struct_0(k6_tmap_1('#skF_2','#skF_1'('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_52,plain,(
    ! [A_24,B_25] :
      ( ~ v2_struct_0(k6_tmap_1(A_24,B_25))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24)
      | ~ v2_pre_topc(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_56,plain,(
    ! [A_10] :
      ( ~ v2_struct_0(k6_tmap_1(A_10,'#skF_1'(A_10)))
      | v2_struct_0(A_10)
      | v1_tdlat_3(A_10)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10) ) ),
    inference(resolution,[status(thm)],[c_34,c_52])).

tff(c_181,plain,
    ( v2_struct_0('#skF_2')
    | v1_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_177,c_56])).

tff(c_184,plain,
    ( v2_struct_0('#skF_2')
    | v1_tdlat_3('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_181])).

tff(c_186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_44,c_184])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:56:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.37  
% 2.23/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.37  %$ v5_pre_topc > v1_funct_2 > v3_pre_topc > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k7_tmap_1 > k6_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2
% 2.23/1.37  
% 2.23/1.37  %Foreground sorts:
% 2.23/1.37  
% 2.23/1.37  
% 2.23/1.37  %Background operators:
% 2.23/1.37  
% 2.23/1.37  
% 2.23/1.37  %Foreground operators:
% 2.23/1.37  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.23/1.37  tff(k7_tmap_1, type, k7_tmap_1: ($i * $i) > $i).
% 2.23/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.23/1.37  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.23/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.37  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.23/1.37  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.23/1.37  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.23/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.23/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.37  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.23/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.23/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.23/1.37  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 2.23/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.37  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 2.23/1.37  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.23/1.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.23/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.23/1.37  
% 2.52/1.39  tff(f_129, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => ((![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => v5_pre_topc(C, A, B))))) => v1_tdlat_3(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tex_2)).
% 2.52/1.39  tff(f_102, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_tdlat_3)).
% 2.52/1.39  tff(f_40, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 2.52/1.39  tff(f_55, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_funct_1(k7_tmap_1(A, B)) & v1_funct_2(k7_tmap_1(A, B), u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))) & m1_subset_1(k7_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 2.52/1.39  tff(f_71, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((~v2_struct_0(k6_tmap_1(A, B)) & v1_pre_topc(k6_tmap_1(A, B))) & v2_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_tmap_1)).
% 2.52/1.39  tff(f_91, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (((v1_funct_1(k7_tmap_1(A, B)) & v1_funct_2(k7_tmap_1(A, B), u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))) & v5_pre_topc(k7_tmap_1(A, B), A, k6_tmap_1(A, B))) & m1_subset_1(k7_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_tmap_1)).
% 2.52/1.39  tff(c_36, plain, (~v1_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.52/1.39  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.52/1.39  tff(c_42, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.52/1.39  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.52/1.39  tff(c_34, plain, (![A_10]: (m1_subset_1('#skF_1'(A_10), k1_zfmisc_1(u1_struct_0(A_10))) | v1_tdlat_3(A_10) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.52/1.39  tff(c_59, plain, (![A_29, B_30]: (l1_pre_topc(k6_tmap_1(A_29, B_30)) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29) | ~v2_pre_topc(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.52/1.39  tff(c_63, plain, (![A_10]: (l1_pre_topc(k6_tmap_1(A_10, '#skF_1'(A_10))) | v2_struct_0(A_10) | v1_tdlat_3(A_10) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10))), inference(resolution, [status(thm)], [c_34, c_59])).
% 2.52/1.39  tff(c_65, plain, (![A_32, B_33]: (v1_funct_1(k7_tmap_1(A_32, B_33)) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.52/1.39  tff(c_69, plain, (![A_10]: (v1_funct_1(k7_tmap_1(A_10, '#skF_1'(A_10))) | v2_struct_0(A_10) | v1_tdlat_3(A_10) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10))), inference(resolution, [status(thm)], [c_34, c_65])).
% 2.52/1.39  tff(c_76, plain, (![A_37, B_38]: (v2_pre_topc(k6_tmap_1(A_37, B_38)) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_37))) | ~l1_pre_topc(A_37) | ~v2_pre_topc(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.52/1.39  tff(c_80, plain, (![A_10]: (v2_pre_topc(k6_tmap_1(A_10, '#skF_1'(A_10))) | v2_struct_0(A_10) | v1_tdlat_3(A_10) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10))), inference(resolution, [status(thm)], [c_34, c_76])).
% 2.52/1.39  tff(c_10, plain, (![A_3, B_4]: (v1_funct_2(k7_tmap_1(A_3, B_4), u1_struct_0(A_3), u1_struct_0(k6_tmap_1(A_3, B_4))) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0(A_3))) | ~l1_pre_topc(A_3) | ~v2_pre_topc(A_3) | v2_struct_0(A_3))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.52/1.39  tff(c_85, plain, (![A_45, B_46]: (m1_subset_1(k7_tmap_1(A_45, B_46), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_45), u1_struct_0(k6_tmap_1(A_45, B_46))))) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45) | ~v2_pre_topc(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.52/1.39  tff(c_38, plain, (![C_19, B_17]: (v5_pre_topc(C_19, '#skF_2', B_17) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_17)))) | ~v1_funct_2(C_19, u1_struct_0('#skF_2'), u1_struct_0(B_17)) | ~v1_funct_1(C_19) | ~l1_pre_topc(B_17) | ~v2_pre_topc(B_17) | v2_struct_0(B_17))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.52/1.39  tff(c_89, plain, (![B_46]: (v5_pre_topc(k7_tmap_1('#skF_2', B_46), '#skF_2', k6_tmap_1('#skF_2', B_46)) | ~v1_funct_2(k7_tmap_1('#skF_2', B_46), u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', B_46))) | ~v1_funct_1(k7_tmap_1('#skF_2', B_46)) | ~l1_pre_topc(k6_tmap_1('#skF_2', B_46)) | ~v2_pre_topc(k6_tmap_1('#skF_2', B_46)) | v2_struct_0(k6_tmap_1('#skF_2', B_46)) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_85, c_38])).
% 2.52/1.39  tff(c_92, plain, (![B_46]: (v5_pre_topc(k7_tmap_1('#skF_2', B_46), '#skF_2', k6_tmap_1('#skF_2', B_46)) | ~v1_funct_2(k7_tmap_1('#skF_2', B_46), u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', B_46))) | ~v1_funct_1(k7_tmap_1('#skF_2', B_46)) | ~l1_pre_topc(k6_tmap_1('#skF_2', B_46)) | ~v2_pre_topc(k6_tmap_1('#skF_2', B_46)) | v2_struct_0(k6_tmap_1('#skF_2', B_46)) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_89])).
% 2.52/1.39  tff(c_94, plain, (![B_47]: (v5_pre_topc(k7_tmap_1('#skF_2', B_47), '#skF_2', k6_tmap_1('#skF_2', B_47)) | ~v1_funct_2(k7_tmap_1('#skF_2', B_47), u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', B_47))) | ~v1_funct_1(k7_tmap_1('#skF_2', B_47)) | ~l1_pre_topc(k6_tmap_1('#skF_2', B_47)) | ~v2_pre_topc(k6_tmap_1('#skF_2', B_47)) | v2_struct_0(k6_tmap_1('#skF_2', B_47)) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_44, c_92])).
% 2.52/1.39  tff(c_98, plain, (![B_4]: (v5_pre_topc(k7_tmap_1('#skF_2', B_4), '#skF_2', k6_tmap_1('#skF_2', B_4)) | ~v1_funct_1(k7_tmap_1('#skF_2', B_4)) | ~l1_pre_topc(k6_tmap_1('#skF_2', B_4)) | ~v2_pre_topc(k6_tmap_1('#skF_2', B_4)) | v2_struct_0(k6_tmap_1('#skF_2', B_4)) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_10, c_94])).
% 2.52/1.39  tff(c_101, plain, (![B_4]: (v5_pre_topc(k7_tmap_1('#skF_2', B_4), '#skF_2', k6_tmap_1('#skF_2', B_4)) | ~v1_funct_1(k7_tmap_1('#skF_2', B_4)) | ~l1_pre_topc(k6_tmap_1('#skF_2', B_4)) | ~v2_pre_topc(k6_tmap_1('#skF_2', B_4)) | v2_struct_0(k6_tmap_1('#skF_2', B_4)) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_98])).
% 2.52/1.39  tff(c_102, plain, (![B_4]: (v5_pre_topc(k7_tmap_1('#skF_2', B_4), '#skF_2', k6_tmap_1('#skF_2', B_4)) | ~v1_funct_1(k7_tmap_1('#skF_2', B_4)) | ~l1_pre_topc(k6_tmap_1('#skF_2', B_4)) | ~v2_pre_topc(k6_tmap_1('#skF_2', B_4)) | v2_struct_0(k6_tmap_1('#skF_2', B_4)) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_44, c_101])).
% 2.52/1.39  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(k7_tmap_1(A_3, B_4), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3), u1_struct_0(k6_tmap_1(A_3, B_4))))) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0(A_3))) | ~l1_pre_topc(A_3) | ~v2_pre_topc(A_3) | v2_struct_0(A_3))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.52/1.39  tff(c_104, plain, (![B_49, A_50]: (v3_pre_topc(B_49, A_50) | ~m1_subset_1(k7_tmap_1(A_50, B_49), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_50), u1_struct_0(k6_tmap_1(A_50, B_49))))) | ~v5_pre_topc(k7_tmap_1(A_50, B_49), A_50, k6_tmap_1(A_50, B_49)) | ~v1_funct_2(k7_tmap_1(A_50, B_49), u1_struct_0(A_50), u1_struct_0(k6_tmap_1(A_50, B_49))) | ~v1_funct_1(k7_tmap_1(A_50, B_49)) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50) | ~v2_pre_topc(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.52/1.39  tff(c_109, plain, (![B_51, A_52]: (v3_pre_topc(B_51, A_52) | ~v5_pre_topc(k7_tmap_1(A_52, B_51), A_52, k6_tmap_1(A_52, B_51)) | ~v1_funct_2(k7_tmap_1(A_52, B_51), u1_struct_0(A_52), u1_struct_0(k6_tmap_1(A_52, B_51))) | ~v1_funct_1(k7_tmap_1(A_52, B_51)) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_pre_topc(A_52) | ~v2_pre_topc(A_52) | v2_struct_0(A_52))), inference(resolution, [status(thm)], [c_8, c_104])).
% 2.52/1.39  tff(c_114, plain, (![B_53, A_54]: (v3_pre_topc(B_53, A_54) | ~v5_pre_topc(k7_tmap_1(A_54, B_53), A_54, k6_tmap_1(A_54, B_53)) | ~v1_funct_1(k7_tmap_1(A_54, B_53)) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54) | ~v2_pre_topc(A_54) | v2_struct_0(A_54))), inference(resolution, [status(thm)], [c_10, c_109])).
% 2.52/1.39  tff(c_117, plain, (![B_4]: (v3_pre_topc(B_4, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~v1_funct_1(k7_tmap_1('#skF_2', B_4)) | ~l1_pre_topc(k6_tmap_1('#skF_2', B_4)) | ~v2_pre_topc(k6_tmap_1('#skF_2', B_4)) | v2_struct_0(k6_tmap_1('#skF_2', B_4)) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_102, c_114])).
% 2.52/1.39  tff(c_123, plain, (![B_4]: (v3_pre_topc(B_4, '#skF_2') | v2_struct_0('#skF_2') | ~v1_funct_1(k7_tmap_1('#skF_2', B_4)) | ~l1_pre_topc(k6_tmap_1('#skF_2', B_4)) | ~v2_pre_topc(k6_tmap_1('#skF_2', B_4)) | v2_struct_0(k6_tmap_1('#skF_2', B_4)) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_117])).
% 2.52/1.39  tff(c_126, plain, (![B_55]: (v3_pre_topc(B_55, '#skF_2') | ~v1_funct_1(k7_tmap_1('#skF_2', B_55)) | ~l1_pre_topc(k6_tmap_1('#skF_2', B_55)) | ~v2_pre_topc(k6_tmap_1('#skF_2', B_55)) | v2_struct_0(k6_tmap_1('#skF_2', B_55)) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_44, c_123])).
% 2.52/1.39  tff(c_130, plain, (v3_pre_topc('#skF_1'('#skF_2'), '#skF_2') | ~v1_funct_1(k7_tmap_1('#skF_2', '#skF_1'('#skF_2'))) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_1'('#skF_2'))) | ~v2_pre_topc(k6_tmap_1('#skF_2', '#skF_1'('#skF_2'))) | v2_struct_0(k6_tmap_1('#skF_2', '#skF_1'('#skF_2'))) | v1_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_126])).
% 2.52/1.39  tff(c_133, plain, (v3_pre_topc('#skF_1'('#skF_2'), '#skF_2') | ~v1_funct_1(k7_tmap_1('#skF_2', '#skF_1'('#skF_2'))) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_1'('#skF_2'))) | ~v2_pre_topc(k6_tmap_1('#skF_2', '#skF_1'('#skF_2'))) | v2_struct_0(k6_tmap_1('#skF_2', '#skF_1'('#skF_2'))) | v1_tdlat_3('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_130])).
% 2.52/1.39  tff(c_134, plain, (v3_pre_topc('#skF_1'('#skF_2'), '#skF_2') | ~v1_funct_1(k7_tmap_1('#skF_2', '#skF_1'('#skF_2'))) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_1'('#skF_2'))) | ~v2_pre_topc(k6_tmap_1('#skF_2', '#skF_1'('#skF_2'))) | v2_struct_0(k6_tmap_1('#skF_2', '#skF_1'('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_36, c_133])).
% 2.52/1.39  tff(c_135, plain, (~v2_pre_topc(k6_tmap_1('#skF_2', '#skF_1'('#skF_2')))), inference(splitLeft, [status(thm)], [c_134])).
% 2.52/1.39  tff(c_138, plain, (v2_struct_0('#skF_2') | v1_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_80, c_135])).
% 2.52/1.39  tff(c_141, plain, (v2_struct_0('#skF_2') | v1_tdlat_3('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_138])).
% 2.52/1.39  tff(c_143, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_44, c_141])).
% 2.52/1.39  tff(c_144, plain, (~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_1'('#skF_2'))) | ~v1_funct_1(k7_tmap_1('#skF_2', '#skF_1'('#skF_2'))) | v2_struct_0(k6_tmap_1('#skF_2', '#skF_1'('#skF_2'))) | v3_pre_topc('#skF_1'('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_134])).
% 2.52/1.39  tff(c_146, plain, (~v1_funct_1(k7_tmap_1('#skF_2', '#skF_1'('#skF_2')))), inference(splitLeft, [status(thm)], [c_144])).
% 2.52/1.39  tff(c_149, plain, (v2_struct_0('#skF_2') | v1_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_69, c_146])).
% 2.52/1.39  tff(c_152, plain, (v2_struct_0('#skF_2') | v1_tdlat_3('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_149])).
% 2.52/1.39  tff(c_154, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_44, c_152])).
% 2.52/1.39  tff(c_155, plain, (~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_1'('#skF_2'))) | v3_pre_topc('#skF_1'('#skF_2'), '#skF_2') | v2_struct_0(k6_tmap_1('#skF_2', '#skF_1'('#skF_2')))), inference(splitRight, [status(thm)], [c_144])).
% 2.52/1.39  tff(c_157, plain, (~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_1'('#skF_2')))), inference(splitLeft, [status(thm)], [c_155])).
% 2.52/1.39  tff(c_160, plain, (v2_struct_0('#skF_2') | v1_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_63, c_157])).
% 2.52/1.39  tff(c_163, plain, (v2_struct_0('#skF_2') | v1_tdlat_3('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_160])).
% 2.52/1.39  tff(c_165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_44, c_163])).
% 2.52/1.39  tff(c_166, plain, (v2_struct_0(k6_tmap_1('#skF_2', '#skF_1'('#skF_2'))) | v3_pre_topc('#skF_1'('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_155])).
% 2.52/1.39  tff(c_168, plain, (v3_pre_topc('#skF_1'('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_166])).
% 2.52/1.39  tff(c_32, plain, (![A_10]: (~v3_pre_topc('#skF_1'(A_10), A_10) | v1_tdlat_3(A_10) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.52/1.39  tff(c_171, plain, (v1_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_168, c_32])).
% 2.52/1.39  tff(c_174, plain, (v1_tdlat_3('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_171])).
% 2.52/1.39  tff(c_176, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_174])).
% 2.52/1.39  tff(c_177, plain, (v2_struct_0(k6_tmap_1('#skF_2', '#skF_1'('#skF_2')))), inference(splitRight, [status(thm)], [c_166])).
% 2.52/1.39  tff(c_52, plain, (![A_24, B_25]: (~v2_struct_0(k6_tmap_1(A_24, B_25)) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24) | ~v2_pre_topc(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.52/1.39  tff(c_56, plain, (![A_10]: (~v2_struct_0(k6_tmap_1(A_10, '#skF_1'(A_10))) | v2_struct_0(A_10) | v1_tdlat_3(A_10) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10))), inference(resolution, [status(thm)], [c_34, c_52])).
% 2.52/1.39  tff(c_181, plain, (v2_struct_0('#skF_2') | v1_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_177, c_56])).
% 2.52/1.39  tff(c_184, plain, (v2_struct_0('#skF_2') | v1_tdlat_3('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_181])).
% 2.52/1.39  tff(c_186, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_44, c_184])).
% 2.52/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.39  
% 2.52/1.39  Inference rules
% 2.52/1.39  ----------------------
% 2.52/1.39  #Ref     : 0
% 2.52/1.39  #Sup     : 18
% 2.52/1.39  #Fact    : 0
% 2.52/1.39  #Define  : 0
% 2.52/1.39  #Split   : 4
% 2.52/1.39  #Chain   : 0
% 2.52/1.39  #Close   : 0
% 2.52/1.39  
% 2.52/1.39  Ordering : KBO
% 2.52/1.39  
% 2.52/1.39  Simplification rules
% 2.52/1.39  ----------------------
% 2.52/1.39  #Subsume      : 8
% 2.52/1.39  #Demod        : 18
% 2.52/1.39  #Tautology    : 2
% 2.52/1.39  #SimpNegUnit  : 9
% 2.52/1.39  #BackRed      : 0
% 2.52/1.39  
% 2.52/1.39  #Partial instantiations: 0
% 2.52/1.39  #Strategies tried      : 1
% 2.52/1.39  
% 2.52/1.39  Timing (in seconds)
% 2.52/1.39  ----------------------
% 2.52/1.39  Preprocessing        : 0.36
% 2.52/1.39  Parsing              : 0.20
% 2.52/1.39  CNF conversion       : 0.03
% 2.52/1.39  Main loop            : 0.21
% 2.52/1.39  Inferencing          : 0.09
% 2.52/1.39  Reduction            : 0.05
% 2.52/1.39  Demodulation         : 0.04
% 2.52/1.39  BG Simplification    : 0.02
% 2.52/1.40  Subsumption          : 0.05
% 2.52/1.40  Abstraction          : 0.01
% 2.52/1.40  MUC search           : 0.00
% 2.52/1.40  Cooper               : 0.00
% 2.52/1.40  Total                : 0.61
% 2.52/1.40  Index Insertion      : 0.00
% 2.52/1.40  Index Deletion       : 0.00
% 2.52/1.40  Index Matching       : 0.00
% 2.52/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
