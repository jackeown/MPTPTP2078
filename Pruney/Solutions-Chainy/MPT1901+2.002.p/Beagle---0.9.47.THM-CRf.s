%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:37 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 371 expanded)
%              Number of leaves         :   28 ( 145 expanded)
%              Depth                    :   20
%              Number of atoms          :  281 (2128 expanded)
%              Number of equality atoms :    1 (  10 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v3_pre_topc > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k7_tmap_1 > k6_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1 > #skF_3

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

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_134,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tex_2)).

tff(f_107,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( B = k1_tarski(C)
                 => v3_pre_topc(B,A) ) ) )
       => v1_tdlat_3(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tdlat_3)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_funct_1(k7_tmap_1(A,B))
        & v1_funct_2(k7_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B)))
        & m1_subset_1(k7_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B))))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( ~ v2_struct_0(k6_tmap_1(A,B))
        & v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_tmap_1)).

tff(c_38,plain,(
    ~ v1_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_44,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_42,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_36,plain,(
    ! [A_10] :
      ( m1_subset_1('#skF_1'(A_10),k1_zfmisc_1(u1_struct_0(A_10)))
      | v1_tdlat_3(A_10)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_66,plain,(
    ! [A_30,B_31] :
      ( l1_pre_topc(k6_tmap_1(A_30,B_31))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_70,plain,(
    ! [A_10] :
      ( l1_pre_topc(k6_tmap_1(A_10,'#skF_1'(A_10)))
      | v2_struct_0(A_10)
      | v1_tdlat_3(A_10)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10) ) ),
    inference(resolution,[status(thm)],[c_36,c_66])).

tff(c_59,plain,(
    ! [A_25,B_26] :
      ( v1_funct_1(k7_tmap_1(A_25,B_26))
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_63,plain,(
    ! [A_10] :
      ( v1_funct_1(k7_tmap_1(A_10,'#skF_1'(A_10)))
      | v2_struct_0(A_10)
      | v1_tdlat_3(A_10)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10) ) ),
    inference(resolution,[status(thm)],[c_36,c_59])).

tff(c_72,plain,(
    ! [A_33,B_34] :
      ( v2_pre_topc(k6_tmap_1(A_33,B_34))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_76,plain,(
    ! [A_10] :
      ( v2_pre_topc(k6_tmap_1(A_10,'#skF_1'(A_10)))
      | v2_struct_0(A_10)
      | v1_tdlat_3(A_10)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10) ) ),
    inference(resolution,[status(thm)],[c_36,c_72])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( v1_funct_2(k7_tmap_1(A_3,B_4),u1_struct_0(A_3),u1_struct_0(k6_tmap_1(A_3,B_4)))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ l1_pre_topc(A_3)
      | ~ v2_pre_topc(A_3)
      | v2_struct_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_92,plain,(
    ! [A_46,B_47] :
      ( m1_subset_1(k7_tmap_1(A_46,B_47),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_46),u1_struct_0(k6_tmap_1(A_46,B_47)))))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46)
      | ~ v2_pre_topc(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_40,plain,(
    ! [C_20,B_18] :
      ( v5_pre_topc(C_20,'#skF_3',B_18)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_18))))
      | ~ v1_funct_2(C_20,u1_struct_0('#skF_3'),u1_struct_0(B_18))
      | ~ v1_funct_1(C_20)
      | ~ l1_pre_topc(B_18)
      | ~ v2_pre_topc(B_18)
      | v2_struct_0(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_96,plain,(
    ! [B_47] :
      ( v5_pre_topc(k7_tmap_1('#skF_3',B_47),'#skF_3',k6_tmap_1('#skF_3',B_47))
      | ~ v1_funct_2(k7_tmap_1('#skF_3',B_47),u1_struct_0('#skF_3'),u1_struct_0(k6_tmap_1('#skF_3',B_47)))
      | ~ v1_funct_1(k7_tmap_1('#skF_3',B_47))
      | ~ l1_pre_topc(k6_tmap_1('#skF_3',B_47))
      | ~ v2_pre_topc(k6_tmap_1('#skF_3',B_47))
      | v2_struct_0(k6_tmap_1('#skF_3',B_47))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_92,c_40])).

tff(c_99,plain,(
    ! [B_47] :
      ( v5_pre_topc(k7_tmap_1('#skF_3',B_47),'#skF_3',k6_tmap_1('#skF_3',B_47))
      | ~ v1_funct_2(k7_tmap_1('#skF_3',B_47),u1_struct_0('#skF_3'),u1_struct_0(k6_tmap_1('#skF_3',B_47)))
      | ~ v1_funct_1(k7_tmap_1('#skF_3',B_47))
      | ~ l1_pre_topc(k6_tmap_1('#skF_3',B_47))
      | ~ v2_pre_topc(k6_tmap_1('#skF_3',B_47))
      | v2_struct_0(k6_tmap_1('#skF_3',B_47))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_96])).

tff(c_101,plain,(
    ! [B_48] :
      ( v5_pre_topc(k7_tmap_1('#skF_3',B_48),'#skF_3',k6_tmap_1('#skF_3',B_48))
      | ~ v1_funct_2(k7_tmap_1('#skF_3',B_48),u1_struct_0('#skF_3'),u1_struct_0(k6_tmap_1('#skF_3',B_48)))
      | ~ v1_funct_1(k7_tmap_1('#skF_3',B_48))
      | ~ l1_pre_topc(k6_tmap_1('#skF_3',B_48))
      | ~ v2_pre_topc(k6_tmap_1('#skF_3',B_48))
      | v2_struct_0(k6_tmap_1('#skF_3',B_48))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_99])).

tff(c_105,plain,(
    ! [B_4] :
      ( v5_pre_topc(k7_tmap_1('#skF_3',B_4),'#skF_3',k6_tmap_1('#skF_3',B_4))
      | ~ v1_funct_1(k7_tmap_1('#skF_3',B_4))
      | ~ l1_pre_topc(k6_tmap_1('#skF_3',B_4))
      | ~ v2_pre_topc(k6_tmap_1('#skF_3',B_4))
      | v2_struct_0(k6_tmap_1('#skF_3',B_4))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_10,c_101])).

tff(c_108,plain,(
    ! [B_4] :
      ( v5_pre_topc(k7_tmap_1('#skF_3',B_4),'#skF_3',k6_tmap_1('#skF_3',B_4))
      | ~ v1_funct_1(k7_tmap_1('#skF_3',B_4))
      | ~ l1_pre_topc(k6_tmap_1('#skF_3',B_4))
      | ~ v2_pre_topc(k6_tmap_1('#skF_3',B_4))
      | v2_struct_0(k6_tmap_1('#skF_3',B_4))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_105])).

tff(c_109,plain,(
    ! [B_4] :
      ( v5_pre_topc(k7_tmap_1('#skF_3',B_4),'#skF_3',k6_tmap_1('#skF_3',B_4))
      | ~ v1_funct_1(k7_tmap_1('#skF_3',B_4))
      | ~ l1_pre_topc(k6_tmap_1('#skF_3',B_4))
      | ~ v2_pre_topc(k6_tmap_1('#skF_3',B_4))
      | v2_struct_0(k6_tmap_1('#skF_3',B_4))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_108])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k7_tmap_1(A_3,B_4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3),u1_struct_0(k6_tmap_1(A_3,B_4)))))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ l1_pre_topc(A_3)
      | ~ v2_pre_topc(A_3)
      | v2_struct_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_111,plain,(
    ! [B_50,A_51] :
      ( v3_pre_topc(B_50,A_51)
      | ~ m1_subset_1(k7_tmap_1(A_51,B_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_51),u1_struct_0(k6_tmap_1(A_51,B_50)))))
      | ~ v5_pre_topc(k7_tmap_1(A_51,B_50),A_51,k6_tmap_1(A_51,B_50))
      | ~ v1_funct_2(k7_tmap_1(A_51,B_50),u1_struct_0(A_51),u1_struct_0(k6_tmap_1(A_51,B_50)))
      | ~ v1_funct_1(k7_tmap_1(A_51,B_50))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_116,plain,(
    ! [B_52,A_53] :
      ( v3_pre_topc(B_52,A_53)
      | ~ v5_pre_topc(k7_tmap_1(A_53,B_52),A_53,k6_tmap_1(A_53,B_52))
      | ~ v1_funct_2(k7_tmap_1(A_53,B_52),u1_struct_0(A_53),u1_struct_0(k6_tmap_1(A_53,B_52)))
      | ~ v1_funct_1(k7_tmap_1(A_53,B_52))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(resolution,[status(thm)],[c_8,c_111])).

tff(c_121,plain,(
    ! [B_54,A_55] :
      ( v3_pre_topc(B_54,A_55)
      | ~ v5_pre_topc(k7_tmap_1(A_55,B_54),A_55,k6_tmap_1(A_55,B_54))
      | ~ v1_funct_1(k7_tmap_1(A_55,B_54))
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_pre_topc(A_55)
      | ~ v2_pre_topc(A_55)
      | v2_struct_0(A_55) ) ),
    inference(resolution,[status(thm)],[c_10,c_116])).

tff(c_124,plain,(
    ! [B_4] :
      ( v3_pre_topc(B_4,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ v1_funct_1(k7_tmap_1('#skF_3',B_4))
      | ~ l1_pre_topc(k6_tmap_1('#skF_3',B_4))
      | ~ v2_pre_topc(k6_tmap_1('#skF_3',B_4))
      | v2_struct_0(k6_tmap_1('#skF_3',B_4))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_109,c_121])).

tff(c_130,plain,(
    ! [B_4] :
      ( v3_pre_topc(B_4,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ v1_funct_1(k7_tmap_1('#skF_3',B_4))
      | ~ l1_pre_topc(k6_tmap_1('#skF_3',B_4))
      | ~ v2_pre_topc(k6_tmap_1('#skF_3',B_4))
      | v2_struct_0(k6_tmap_1('#skF_3',B_4))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_124])).

tff(c_133,plain,(
    ! [B_56] :
      ( v3_pre_topc(B_56,'#skF_3')
      | ~ v1_funct_1(k7_tmap_1('#skF_3',B_56))
      | ~ l1_pre_topc(k6_tmap_1('#skF_3',B_56))
      | ~ v2_pre_topc(k6_tmap_1('#skF_3',B_56))
      | v2_struct_0(k6_tmap_1('#skF_3',B_56))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_130])).

tff(c_137,plain,
    ( v3_pre_topc('#skF_1'('#skF_3'),'#skF_3')
    | ~ v1_funct_1(k7_tmap_1('#skF_3','#skF_1'('#skF_3')))
    | ~ l1_pre_topc(k6_tmap_1('#skF_3','#skF_1'('#skF_3')))
    | ~ v2_pre_topc(k6_tmap_1('#skF_3','#skF_1'('#skF_3')))
    | v2_struct_0(k6_tmap_1('#skF_3','#skF_1'('#skF_3')))
    | v1_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_133])).

tff(c_140,plain,
    ( v3_pre_topc('#skF_1'('#skF_3'),'#skF_3')
    | ~ v1_funct_1(k7_tmap_1('#skF_3','#skF_1'('#skF_3')))
    | ~ l1_pre_topc(k6_tmap_1('#skF_3','#skF_1'('#skF_3')))
    | ~ v2_pre_topc(k6_tmap_1('#skF_3','#skF_1'('#skF_3')))
    | v2_struct_0(k6_tmap_1('#skF_3','#skF_1'('#skF_3')))
    | v1_tdlat_3('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_137])).

tff(c_141,plain,
    ( v3_pre_topc('#skF_1'('#skF_3'),'#skF_3')
    | ~ v1_funct_1(k7_tmap_1('#skF_3','#skF_1'('#skF_3')))
    | ~ l1_pre_topc(k6_tmap_1('#skF_3','#skF_1'('#skF_3')))
    | ~ v2_pre_topc(k6_tmap_1('#skF_3','#skF_1'('#skF_3')))
    | v2_struct_0(k6_tmap_1('#skF_3','#skF_1'('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_140])).

tff(c_142,plain,(
    ~ v2_pre_topc(k6_tmap_1('#skF_3','#skF_1'('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_141])).

tff(c_145,plain,
    ( v2_struct_0('#skF_3')
    | v1_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_142])).

tff(c_148,plain,
    ( v2_struct_0('#skF_3')
    | v1_tdlat_3('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_145])).

tff(c_150,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_46,c_148])).

tff(c_151,plain,
    ( ~ l1_pre_topc(k6_tmap_1('#skF_3','#skF_1'('#skF_3')))
    | ~ v1_funct_1(k7_tmap_1('#skF_3','#skF_1'('#skF_3')))
    | v2_struct_0(k6_tmap_1('#skF_3','#skF_1'('#skF_3')))
    | v3_pre_topc('#skF_1'('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_153,plain,(
    ~ v1_funct_1(k7_tmap_1('#skF_3','#skF_1'('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_156,plain,
    ( v2_struct_0('#skF_3')
    | v1_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_63,c_153])).

tff(c_159,plain,
    ( v2_struct_0('#skF_3')
    | v1_tdlat_3('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_156])).

tff(c_161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_46,c_159])).

tff(c_162,plain,
    ( ~ l1_pre_topc(k6_tmap_1('#skF_3','#skF_1'('#skF_3')))
    | v3_pre_topc('#skF_1'('#skF_3'),'#skF_3')
    | v2_struct_0(k6_tmap_1('#skF_3','#skF_1'('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_164,plain,(
    ~ l1_pre_topc(k6_tmap_1('#skF_3','#skF_1'('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_167,plain,
    ( v2_struct_0('#skF_3')
    | v1_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_164])).

tff(c_170,plain,
    ( v2_struct_0('#skF_3')
    | v1_tdlat_3('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_167])).

tff(c_172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_46,c_170])).

tff(c_173,plain,
    ( v2_struct_0(k6_tmap_1('#skF_3','#skF_1'('#skF_3')))
    | v3_pre_topc('#skF_1'('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_175,plain,(
    v3_pre_topc('#skF_1'('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_173])).

tff(c_30,plain,(
    ! [A_10] :
      ( ~ v3_pre_topc('#skF_1'(A_10),A_10)
      | v1_tdlat_3(A_10)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_178,plain,
    ( v1_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_175,c_30])).

tff(c_181,plain,(
    v1_tdlat_3('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_178])).

tff(c_183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_181])).

tff(c_184,plain,(
    v2_struct_0(k6_tmap_1('#skF_3','#skF_1'('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_173])).

tff(c_78,plain,(
    ! [A_36,B_37] :
      ( ~ v2_struct_0(k6_tmap_1(A_36,B_37))
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36)
      | ~ v2_pre_topc(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_82,plain,(
    ! [A_10] :
      ( ~ v2_struct_0(k6_tmap_1(A_10,'#skF_1'(A_10)))
      | v2_struct_0(A_10)
      | v1_tdlat_3(A_10)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10) ) ),
    inference(resolution,[status(thm)],[c_36,c_78])).

tff(c_188,plain,
    ( v2_struct_0('#skF_3')
    | v1_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_184,c_82])).

tff(c_191,plain,
    ( v2_struct_0('#skF_3')
    | v1_tdlat_3('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_188])).

tff(c_193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_46,c_191])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 13:20:56 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.28  
% 2.36/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.28  %$ v5_pre_topc > v1_funct_2 > v3_pre_topc > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k7_tmap_1 > k6_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1 > #skF_3
% 2.36/1.28  
% 2.36/1.28  %Foreground sorts:
% 2.36/1.28  
% 2.36/1.28  
% 2.36/1.28  %Background operators:
% 2.36/1.28  
% 2.36/1.28  
% 2.36/1.28  %Foreground operators:
% 2.36/1.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.36/1.28  tff(k7_tmap_1, type, k7_tmap_1: ($i * $i) > $i).
% 2.36/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.36/1.28  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.36/1.28  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.36/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.36/1.28  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.36/1.28  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.36/1.28  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.36/1.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.36/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.36/1.28  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.36/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.36/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.36/1.28  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 2.36/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.28  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 2.36/1.28  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.36/1.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.36/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.36/1.28  
% 2.36/1.30  tff(f_134, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => ((![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => v5_pre_topc(C, A, B))))) => v1_tdlat_3(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tex_2)).
% 2.36/1.30  tff(f_107, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => ((![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((B = k1_tarski(C)) => v3_pre_topc(B, A)))))) => v1_tdlat_3(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_tdlat_3)).
% 2.36/1.30  tff(f_40, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 2.36/1.30  tff(f_55, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_funct_1(k7_tmap_1(A, B)) & v1_funct_2(k7_tmap_1(A, B), u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))) & m1_subset_1(k7_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 2.36/1.30  tff(f_71, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((~v2_struct_0(k6_tmap_1(A, B)) & v1_pre_topc(k6_tmap_1(A, B))) & v2_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_tmap_1)).
% 2.36/1.30  tff(f_91, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (((v1_funct_1(k7_tmap_1(A, B)) & v1_funct_2(k7_tmap_1(A, B), u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))) & v5_pre_topc(k7_tmap_1(A, B), A, k6_tmap_1(A, B))) & m1_subset_1(k7_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_tmap_1)).
% 2.36/1.30  tff(c_38, plain, (~v1_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.36/1.30  tff(c_46, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.36/1.30  tff(c_44, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.36/1.30  tff(c_42, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.36/1.30  tff(c_36, plain, (![A_10]: (m1_subset_1('#skF_1'(A_10), k1_zfmisc_1(u1_struct_0(A_10))) | v1_tdlat_3(A_10) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.36/1.30  tff(c_66, plain, (![A_30, B_31]: (l1_pre_topc(k6_tmap_1(A_30, B_31)) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.36/1.30  tff(c_70, plain, (![A_10]: (l1_pre_topc(k6_tmap_1(A_10, '#skF_1'(A_10))) | v2_struct_0(A_10) | v1_tdlat_3(A_10) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10))), inference(resolution, [status(thm)], [c_36, c_66])).
% 2.36/1.30  tff(c_59, plain, (![A_25, B_26]: (v1_funct_1(k7_tmap_1(A_25, B_26)) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.36/1.30  tff(c_63, plain, (![A_10]: (v1_funct_1(k7_tmap_1(A_10, '#skF_1'(A_10))) | v2_struct_0(A_10) | v1_tdlat_3(A_10) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10))), inference(resolution, [status(thm)], [c_36, c_59])).
% 2.36/1.30  tff(c_72, plain, (![A_33, B_34]: (v2_pre_topc(k6_tmap_1(A_33, B_34)) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.36/1.30  tff(c_76, plain, (![A_10]: (v2_pre_topc(k6_tmap_1(A_10, '#skF_1'(A_10))) | v2_struct_0(A_10) | v1_tdlat_3(A_10) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10))), inference(resolution, [status(thm)], [c_36, c_72])).
% 2.36/1.30  tff(c_10, plain, (![A_3, B_4]: (v1_funct_2(k7_tmap_1(A_3, B_4), u1_struct_0(A_3), u1_struct_0(k6_tmap_1(A_3, B_4))) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0(A_3))) | ~l1_pre_topc(A_3) | ~v2_pre_topc(A_3) | v2_struct_0(A_3))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.36/1.30  tff(c_92, plain, (![A_46, B_47]: (m1_subset_1(k7_tmap_1(A_46, B_47), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_46), u1_struct_0(k6_tmap_1(A_46, B_47))))) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46) | ~v2_pre_topc(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.36/1.30  tff(c_40, plain, (![C_20, B_18]: (v5_pre_topc(C_20, '#skF_3', B_18) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_18)))) | ~v1_funct_2(C_20, u1_struct_0('#skF_3'), u1_struct_0(B_18)) | ~v1_funct_1(C_20) | ~l1_pre_topc(B_18) | ~v2_pre_topc(B_18) | v2_struct_0(B_18))), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.36/1.30  tff(c_96, plain, (![B_47]: (v5_pre_topc(k7_tmap_1('#skF_3', B_47), '#skF_3', k6_tmap_1('#skF_3', B_47)) | ~v1_funct_2(k7_tmap_1('#skF_3', B_47), u1_struct_0('#skF_3'), u1_struct_0(k6_tmap_1('#skF_3', B_47))) | ~v1_funct_1(k7_tmap_1('#skF_3', B_47)) | ~l1_pre_topc(k6_tmap_1('#skF_3', B_47)) | ~v2_pre_topc(k6_tmap_1('#skF_3', B_47)) | v2_struct_0(k6_tmap_1('#skF_3', B_47)) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_92, c_40])).
% 2.36/1.30  tff(c_99, plain, (![B_47]: (v5_pre_topc(k7_tmap_1('#skF_3', B_47), '#skF_3', k6_tmap_1('#skF_3', B_47)) | ~v1_funct_2(k7_tmap_1('#skF_3', B_47), u1_struct_0('#skF_3'), u1_struct_0(k6_tmap_1('#skF_3', B_47))) | ~v1_funct_1(k7_tmap_1('#skF_3', B_47)) | ~l1_pre_topc(k6_tmap_1('#skF_3', B_47)) | ~v2_pre_topc(k6_tmap_1('#skF_3', B_47)) | v2_struct_0(k6_tmap_1('#skF_3', B_47)) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_96])).
% 2.36/1.30  tff(c_101, plain, (![B_48]: (v5_pre_topc(k7_tmap_1('#skF_3', B_48), '#skF_3', k6_tmap_1('#skF_3', B_48)) | ~v1_funct_2(k7_tmap_1('#skF_3', B_48), u1_struct_0('#skF_3'), u1_struct_0(k6_tmap_1('#skF_3', B_48))) | ~v1_funct_1(k7_tmap_1('#skF_3', B_48)) | ~l1_pre_topc(k6_tmap_1('#skF_3', B_48)) | ~v2_pre_topc(k6_tmap_1('#skF_3', B_48)) | v2_struct_0(k6_tmap_1('#skF_3', B_48)) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_46, c_99])).
% 2.36/1.30  tff(c_105, plain, (![B_4]: (v5_pre_topc(k7_tmap_1('#skF_3', B_4), '#skF_3', k6_tmap_1('#skF_3', B_4)) | ~v1_funct_1(k7_tmap_1('#skF_3', B_4)) | ~l1_pre_topc(k6_tmap_1('#skF_3', B_4)) | ~v2_pre_topc(k6_tmap_1('#skF_3', B_4)) | v2_struct_0(k6_tmap_1('#skF_3', B_4)) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_10, c_101])).
% 2.36/1.30  tff(c_108, plain, (![B_4]: (v5_pre_topc(k7_tmap_1('#skF_3', B_4), '#skF_3', k6_tmap_1('#skF_3', B_4)) | ~v1_funct_1(k7_tmap_1('#skF_3', B_4)) | ~l1_pre_topc(k6_tmap_1('#skF_3', B_4)) | ~v2_pre_topc(k6_tmap_1('#skF_3', B_4)) | v2_struct_0(k6_tmap_1('#skF_3', B_4)) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_105])).
% 2.36/1.30  tff(c_109, plain, (![B_4]: (v5_pre_topc(k7_tmap_1('#skF_3', B_4), '#skF_3', k6_tmap_1('#skF_3', B_4)) | ~v1_funct_1(k7_tmap_1('#skF_3', B_4)) | ~l1_pre_topc(k6_tmap_1('#skF_3', B_4)) | ~v2_pre_topc(k6_tmap_1('#skF_3', B_4)) | v2_struct_0(k6_tmap_1('#skF_3', B_4)) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_46, c_108])).
% 2.36/1.30  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(k7_tmap_1(A_3, B_4), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3), u1_struct_0(k6_tmap_1(A_3, B_4))))) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0(A_3))) | ~l1_pre_topc(A_3) | ~v2_pre_topc(A_3) | v2_struct_0(A_3))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.36/1.30  tff(c_111, plain, (![B_50, A_51]: (v3_pre_topc(B_50, A_51) | ~m1_subset_1(k7_tmap_1(A_51, B_50), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_51), u1_struct_0(k6_tmap_1(A_51, B_50))))) | ~v5_pre_topc(k7_tmap_1(A_51, B_50), A_51, k6_tmap_1(A_51, B_50)) | ~v1_funct_2(k7_tmap_1(A_51, B_50), u1_struct_0(A_51), u1_struct_0(k6_tmap_1(A_51, B_50))) | ~v1_funct_1(k7_tmap_1(A_51, B_50)) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.36/1.30  tff(c_116, plain, (![B_52, A_53]: (v3_pre_topc(B_52, A_53) | ~v5_pre_topc(k7_tmap_1(A_53, B_52), A_53, k6_tmap_1(A_53, B_52)) | ~v1_funct_2(k7_tmap_1(A_53, B_52), u1_struct_0(A_53), u1_struct_0(k6_tmap_1(A_53, B_52))) | ~v1_funct_1(k7_tmap_1(A_53, B_52)) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53) | ~v2_pre_topc(A_53) | v2_struct_0(A_53))), inference(resolution, [status(thm)], [c_8, c_111])).
% 2.36/1.30  tff(c_121, plain, (![B_54, A_55]: (v3_pre_topc(B_54, A_55) | ~v5_pre_topc(k7_tmap_1(A_55, B_54), A_55, k6_tmap_1(A_55, B_54)) | ~v1_funct_1(k7_tmap_1(A_55, B_54)) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_pre_topc(A_55) | ~v2_pre_topc(A_55) | v2_struct_0(A_55))), inference(resolution, [status(thm)], [c_10, c_116])).
% 2.36/1.30  tff(c_124, plain, (![B_4]: (v3_pre_topc(B_4, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~v1_funct_1(k7_tmap_1('#skF_3', B_4)) | ~l1_pre_topc(k6_tmap_1('#skF_3', B_4)) | ~v2_pre_topc(k6_tmap_1('#skF_3', B_4)) | v2_struct_0(k6_tmap_1('#skF_3', B_4)) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_109, c_121])).
% 2.36/1.30  tff(c_130, plain, (![B_4]: (v3_pre_topc(B_4, '#skF_3') | v2_struct_0('#skF_3') | ~v1_funct_1(k7_tmap_1('#skF_3', B_4)) | ~l1_pre_topc(k6_tmap_1('#skF_3', B_4)) | ~v2_pre_topc(k6_tmap_1('#skF_3', B_4)) | v2_struct_0(k6_tmap_1('#skF_3', B_4)) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_124])).
% 2.36/1.30  tff(c_133, plain, (![B_56]: (v3_pre_topc(B_56, '#skF_3') | ~v1_funct_1(k7_tmap_1('#skF_3', B_56)) | ~l1_pre_topc(k6_tmap_1('#skF_3', B_56)) | ~v2_pre_topc(k6_tmap_1('#skF_3', B_56)) | v2_struct_0(k6_tmap_1('#skF_3', B_56)) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_46, c_130])).
% 2.36/1.30  tff(c_137, plain, (v3_pre_topc('#skF_1'('#skF_3'), '#skF_3') | ~v1_funct_1(k7_tmap_1('#skF_3', '#skF_1'('#skF_3'))) | ~l1_pre_topc(k6_tmap_1('#skF_3', '#skF_1'('#skF_3'))) | ~v2_pre_topc(k6_tmap_1('#skF_3', '#skF_1'('#skF_3'))) | v2_struct_0(k6_tmap_1('#skF_3', '#skF_1'('#skF_3'))) | v1_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_133])).
% 2.36/1.30  tff(c_140, plain, (v3_pre_topc('#skF_1'('#skF_3'), '#skF_3') | ~v1_funct_1(k7_tmap_1('#skF_3', '#skF_1'('#skF_3'))) | ~l1_pre_topc(k6_tmap_1('#skF_3', '#skF_1'('#skF_3'))) | ~v2_pre_topc(k6_tmap_1('#skF_3', '#skF_1'('#skF_3'))) | v2_struct_0(k6_tmap_1('#skF_3', '#skF_1'('#skF_3'))) | v1_tdlat_3('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_137])).
% 2.36/1.30  tff(c_141, plain, (v3_pre_topc('#skF_1'('#skF_3'), '#skF_3') | ~v1_funct_1(k7_tmap_1('#skF_3', '#skF_1'('#skF_3'))) | ~l1_pre_topc(k6_tmap_1('#skF_3', '#skF_1'('#skF_3'))) | ~v2_pre_topc(k6_tmap_1('#skF_3', '#skF_1'('#skF_3'))) | v2_struct_0(k6_tmap_1('#skF_3', '#skF_1'('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_38, c_140])).
% 2.36/1.30  tff(c_142, plain, (~v2_pre_topc(k6_tmap_1('#skF_3', '#skF_1'('#skF_3')))), inference(splitLeft, [status(thm)], [c_141])).
% 2.36/1.30  tff(c_145, plain, (v2_struct_0('#skF_3') | v1_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_76, c_142])).
% 2.36/1.30  tff(c_148, plain, (v2_struct_0('#skF_3') | v1_tdlat_3('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_145])).
% 2.36/1.30  tff(c_150, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_46, c_148])).
% 2.36/1.30  tff(c_151, plain, (~l1_pre_topc(k6_tmap_1('#skF_3', '#skF_1'('#skF_3'))) | ~v1_funct_1(k7_tmap_1('#skF_3', '#skF_1'('#skF_3'))) | v2_struct_0(k6_tmap_1('#skF_3', '#skF_1'('#skF_3'))) | v3_pre_topc('#skF_1'('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_141])).
% 2.36/1.30  tff(c_153, plain, (~v1_funct_1(k7_tmap_1('#skF_3', '#skF_1'('#skF_3')))), inference(splitLeft, [status(thm)], [c_151])).
% 2.36/1.30  tff(c_156, plain, (v2_struct_0('#skF_3') | v1_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_63, c_153])).
% 2.36/1.30  tff(c_159, plain, (v2_struct_0('#skF_3') | v1_tdlat_3('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_156])).
% 2.36/1.30  tff(c_161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_46, c_159])).
% 2.36/1.30  tff(c_162, plain, (~l1_pre_topc(k6_tmap_1('#skF_3', '#skF_1'('#skF_3'))) | v3_pre_topc('#skF_1'('#skF_3'), '#skF_3') | v2_struct_0(k6_tmap_1('#skF_3', '#skF_1'('#skF_3')))), inference(splitRight, [status(thm)], [c_151])).
% 2.36/1.30  tff(c_164, plain, (~l1_pre_topc(k6_tmap_1('#skF_3', '#skF_1'('#skF_3')))), inference(splitLeft, [status(thm)], [c_162])).
% 2.36/1.30  tff(c_167, plain, (v2_struct_0('#skF_3') | v1_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_70, c_164])).
% 2.36/1.30  tff(c_170, plain, (v2_struct_0('#skF_3') | v1_tdlat_3('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_167])).
% 2.36/1.30  tff(c_172, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_46, c_170])).
% 2.36/1.30  tff(c_173, plain, (v2_struct_0(k6_tmap_1('#skF_3', '#skF_1'('#skF_3'))) | v3_pre_topc('#skF_1'('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_162])).
% 2.36/1.30  tff(c_175, plain, (v3_pre_topc('#skF_1'('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_173])).
% 2.36/1.30  tff(c_30, plain, (![A_10]: (~v3_pre_topc('#skF_1'(A_10), A_10) | v1_tdlat_3(A_10) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.36/1.30  tff(c_178, plain, (v1_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_175, c_30])).
% 2.36/1.30  tff(c_181, plain, (v1_tdlat_3('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_178])).
% 2.36/1.30  tff(c_183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_181])).
% 2.36/1.30  tff(c_184, plain, (v2_struct_0(k6_tmap_1('#skF_3', '#skF_1'('#skF_3')))), inference(splitRight, [status(thm)], [c_173])).
% 2.36/1.30  tff(c_78, plain, (![A_36, B_37]: (~v2_struct_0(k6_tmap_1(A_36, B_37)) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(A_36) | ~v2_pre_topc(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.36/1.30  tff(c_82, plain, (![A_10]: (~v2_struct_0(k6_tmap_1(A_10, '#skF_1'(A_10))) | v2_struct_0(A_10) | v1_tdlat_3(A_10) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10))), inference(resolution, [status(thm)], [c_36, c_78])).
% 2.36/1.30  tff(c_188, plain, (v2_struct_0('#skF_3') | v1_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_184, c_82])).
% 2.36/1.30  tff(c_191, plain, (v2_struct_0('#skF_3') | v1_tdlat_3('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_188])).
% 2.36/1.30  tff(c_193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_46, c_191])).
% 2.36/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.30  
% 2.36/1.30  Inference rules
% 2.36/1.30  ----------------------
% 2.36/1.30  #Ref     : 0
% 2.36/1.30  #Sup     : 19
% 2.36/1.30  #Fact    : 0
% 2.36/1.30  #Define  : 0
% 2.36/1.30  #Split   : 4
% 2.36/1.30  #Chain   : 0
% 2.36/1.30  #Close   : 0
% 2.36/1.30  
% 2.36/1.30  Ordering : KBO
% 2.36/1.30  
% 2.36/1.30  Simplification rules
% 2.36/1.30  ----------------------
% 2.36/1.30  #Subsume      : 8
% 2.36/1.30  #Demod        : 18
% 2.36/1.30  #Tautology    : 3
% 2.36/1.30  #SimpNegUnit  : 9
% 2.36/1.30  #BackRed      : 0
% 2.36/1.30  
% 2.36/1.30  #Partial instantiations: 0
% 2.36/1.30  #Strategies tried      : 1
% 2.36/1.30  
% 2.36/1.30  Timing (in seconds)
% 2.36/1.30  ----------------------
% 2.36/1.30  Preprocessing        : 0.30
% 2.36/1.30  Parsing              : 0.17
% 2.36/1.30  CNF conversion       : 0.02
% 2.36/1.30  Main loop            : 0.21
% 2.36/1.30  Inferencing          : 0.09
% 2.36/1.30  Reduction            : 0.05
% 2.36/1.30  Demodulation         : 0.04
% 2.36/1.30  BG Simplification    : 0.02
% 2.36/1.30  Subsumption          : 0.05
% 2.36/1.30  Abstraction          : 0.01
% 2.36/1.30  MUC search           : 0.00
% 2.36/1.30  Cooper               : 0.00
% 2.36/1.30  Total                : 0.54
% 2.36/1.31  Index Insertion      : 0.00
% 2.36/1.31  Index Deletion       : 0.00
% 2.36/1.31  Index Matching       : 0.00
% 2.36/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
