%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1799+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:25 EST 2020

% Result     : Theorem 8.82s
% Output     : CNFRefutation 8.82s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 754 expanded)
%              Number of leaves         :   25 ( 266 expanded)
%              Depth                    :   24
%              Number of atoms          :  387 (4351 expanded)
%              Number of equality atoms :   28 ( 357 expanded)
%              Maximal formula depth    :   23 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k8_tmap_1 > k6_tmap_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k8_tmap_1,type,(
    k8_tmap_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_130,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( m1_pre_topc(C,k8_tmap_1(A,B))
               => ( u1_struct_0(C) = u1_struct_0(B)
                 => ( v1_tsep_1(C,k8_tmap_1(A,B))
                    & m1_pre_topc(C,k8_tmap_1(A,B)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_tmap_1)).

tff(f_107,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( ( v1_pre_topc(C)
                & v2_pre_topc(C)
                & l1_pre_topc(C) )
             => ( C = k8_tmap_1(A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( D = u1_struct_0(B)
                     => C = k6_tmap_1(A,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_tmap_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(k6_tmap_1(A,B))))
             => ( C = B
               => v3_pre_topc(C,k6_tmap_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_tmap_1)).

tff(f_100,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( ( v1_tsep_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_36,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_32,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_38,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_24,plain,(
    ! [B_41,A_39] :
      ( m1_subset_1(u1_struct_0(B_41),k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ m1_pre_topc(B_41,A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_59,plain,(
    ! [A_49,B_50] :
      ( l1_pre_topc(k6_tmap_1(A_49,B_50))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49)
      | ~ v2_pre_topc(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_70,plain,(
    ! [A_39,B_41] :
      ( l1_pre_topc(k6_tmap_1(A_39,u1_struct_0(B_41)))
      | ~ v2_pre_topc(A_39)
      | v2_struct_0(A_39)
      | ~ m1_pre_topc(B_41,A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(resolution,[status(thm)],[c_24,c_59])).

tff(c_95,plain,(
    ! [A_59,B_60] :
      ( v1_pre_topc(k6_tmap_1(A_59,B_60))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59)
      | ~ v2_pre_topc(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_106,plain,(
    ! [A_39,B_41] :
      ( v1_pre_topc(k6_tmap_1(A_39,u1_struct_0(B_41)))
      | ~ v2_pre_topc(A_39)
      | v2_struct_0(A_39)
      | ~ m1_pre_topc(B_41,A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(resolution,[status(thm)],[c_24,c_95])).

tff(c_76,plain,(
    ! [A_53,B_54] :
      ( v2_pre_topc(k6_tmap_1(A_53,B_54))
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_87,plain,(
    ! [A_39,B_41] :
      ( v2_pre_topc(k6_tmap_1(A_39,u1_struct_0(B_41)))
      | ~ v2_pre_topc(A_39)
      | v2_struct_0(A_39)
      | ~ m1_pre_topc(B_41,A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(resolution,[status(thm)],[c_24,c_76])).

tff(c_189,plain,(
    ! [B_78,A_79,C_80] :
      ( u1_struct_0(B_78) = '#skF_1'(A_79,B_78,C_80)
      | k8_tmap_1(A_79,B_78) = C_80
      | ~ l1_pre_topc(C_80)
      | ~ v2_pre_topc(C_80)
      | ~ v1_pre_topc(C_80)
      | ~ m1_pre_topc(B_78,A_79)
      | ~ l1_pre_topc(A_79)
      | ~ v2_pre_topc(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_335,plain,(
    ! [A_113,B_114,A_115,B_116] :
      ( '#skF_1'(A_113,B_114,k6_tmap_1(A_115,u1_struct_0(B_116))) = u1_struct_0(B_114)
      | k8_tmap_1(A_113,B_114) = k6_tmap_1(A_115,u1_struct_0(B_116))
      | ~ l1_pre_topc(k6_tmap_1(A_115,u1_struct_0(B_116)))
      | ~ v1_pre_topc(k6_tmap_1(A_115,u1_struct_0(B_116)))
      | ~ m1_pre_topc(B_114,A_113)
      | ~ l1_pre_topc(A_113)
      | ~ v2_pre_topc(A_113)
      | v2_struct_0(A_113)
      | ~ v2_pre_topc(A_115)
      | v2_struct_0(A_115)
      | ~ m1_pre_topc(B_116,A_115)
      | ~ l1_pre_topc(A_115) ) ),
    inference(resolution,[status(thm)],[c_87,c_189])).

tff(c_345,plain,(
    ! [A_117,B_118,A_119,B_120] :
      ( '#skF_1'(A_117,B_118,k6_tmap_1(A_119,u1_struct_0(B_120))) = u1_struct_0(B_118)
      | k8_tmap_1(A_117,B_118) = k6_tmap_1(A_119,u1_struct_0(B_120))
      | ~ l1_pre_topc(k6_tmap_1(A_119,u1_struct_0(B_120)))
      | ~ m1_pre_topc(B_118,A_117)
      | ~ l1_pre_topc(A_117)
      | ~ v2_pre_topc(A_117)
      | v2_struct_0(A_117)
      | ~ v2_pre_topc(A_119)
      | v2_struct_0(A_119)
      | ~ m1_pre_topc(B_120,A_119)
      | ~ l1_pre_topc(A_119) ) ),
    inference(resolution,[status(thm)],[c_106,c_335])).

tff(c_355,plain,(
    ! [A_121,B_122,A_123,B_124] :
      ( '#skF_1'(A_121,B_122,k6_tmap_1(A_123,u1_struct_0(B_124))) = u1_struct_0(B_122)
      | k8_tmap_1(A_121,B_122) = k6_tmap_1(A_123,u1_struct_0(B_124))
      | ~ m1_pre_topc(B_122,A_121)
      | ~ l1_pre_topc(A_121)
      | ~ v2_pre_topc(A_121)
      | v2_struct_0(A_121)
      | ~ v2_pre_topc(A_123)
      | v2_struct_0(A_123)
      | ~ m1_pre_topc(B_124,A_123)
      | ~ l1_pre_topc(A_123) ) ),
    inference(resolution,[status(thm)],[c_70,c_345])).

tff(c_4,plain,(
    ! [A_1,B_13,C_19] :
      ( k6_tmap_1(A_1,'#skF_1'(A_1,B_13,C_19)) != C_19
      | k8_tmap_1(A_1,B_13) = C_19
      | ~ l1_pre_topc(C_19)
      | ~ v2_pre_topc(C_19)
      | ~ v1_pre_topc(C_19)
      | ~ m1_pre_topc(B_13,A_1)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_373,plain,(
    ! [A_123,B_124,A_121,B_122] :
      ( k6_tmap_1(A_123,u1_struct_0(B_124)) != k6_tmap_1(A_121,u1_struct_0(B_122))
      | k8_tmap_1(A_121,B_122) = k6_tmap_1(A_123,u1_struct_0(B_124))
      | ~ l1_pre_topc(k6_tmap_1(A_123,u1_struct_0(B_124)))
      | ~ v2_pre_topc(k6_tmap_1(A_123,u1_struct_0(B_124)))
      | ~ v1_pre_topc(k6_tmap_1(A_123,u1_struct_0(B_124)))
      | ~ m1_pre_topc(B_122,A_121)
      | ~ l1_pre_topc(A_121)
      | ~ v2_pre_topc(A_121)
      | v2_struct_0(A_121)
      | k8_tmap_1(A_121,B_122) = k6_tmap_1(A_123,u1_struct_0(B_124))
      | ~ m1_pre_topc(B_122,A_121)
      | ~ l1_pre_topc(A_121)
      | ~ v2_pre_topc(A_121)
      | v2_struct_0(A_121)
      | ~ v2_pre_topc(A_123)
      | v2_struct_0(A_123)
      | ~ m1_pre_topc(B_124,A_123)
      | ~ l1_pre_topc(A_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_355,c_4])).

tff(c_478,plain,(
    ! [A_147,B_148] :
      ( k6_tmap_1(A_147,u1_struct_0(B_148)) = k8_tmap_1(A_147,B_148)
      | ~ l1_pre_topc(k6_tmap_1(A_147,u1_struct_0(B_148)))
      | ~ v2_pre_topc(k6_tmap_1(A_147,u1_struct_0(B_148)))
      | ~ v1_pre_topc(k6_tmap_1(A_147,u1_struct_0(B_148)))
      | ~ m1_pre_topc(B_148,A_147)
      | ~ l1_pre_topc(A_147)
      | ~ v2_pre_topc(A_147)
      | v2_struct_0(A_147)
      | k6_tmap_1(A_147,u1_struct_0(B_148)) = k8_tmap_1(A_147,B_148)
      | ~ m1_pre_topc(B_148,A_147)
      | ~ l1_pre_topc(A_147)
      | ~ v2_pre_topc(A_147)
      | v2_struct_0(A_147)
      | ~ v2_pre_topc(A_147)
      | v2_struct_0(A_147)
      | ~ m1_pre_topc(B_148,A_147)
      | ~ l1_pre_topc(A_147) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_373])).

tff(c_498,plain,(
    ! [A_152,B_153] :
      ( ~ l1_pre_topc(k6_tmap_1(A_152,u1_struct_0(B_153)))
      | ~ v1_pre_topc(k6_tmap_1(A_152,u1_struct_0(B_153)))
      | k6_tmap_1(A_152,u1_struct_0(B_153)) = k8_tmap_1(A_152,B_153)
      | ~ v2_pre_topc(A_152)
      | v2_struct_0(A_152)
      | ~ m1_pre_topc(B_153,A_152)
      | ~ l1_pre_topc(A_152) ) ),
    inference(resolution,[status(thm)],[c_87,c_478])).

tff(c_511,plain,(
    ! [A_154,B_155] :
      ( ~ l1_pre_topc(k6_tmap_1(A_154,u1_struct_0(B_155)))
      | k6_tmap_1(A_154,u1_struct_0(B_155)) = k8_tmap_1(A_154,B_155)
      | ~ v2_pre_topc(A_154)
      | v2_struct_0(A_154)
      | ~ m1_pre_topc(B_155,A_154)
      | ~ l1_pre_topc(A_154) ) ),
    inference(resolution,[status(thm)],[c_106,c_498])).

tff(c_524,plain,(
    ! [A_156,B_157] :
      ( k6_tmap_1(A_156,u1_struct_0(B_157)) = k8_tmap_1(A_156,B_157)
      | ~ v2_pre_topc(A_156)
      | v2_struct_0(A_156)
      | ~ m1_pre_topc(B_157,A_156)
      | ~ l1_pre_topc(A_156) ) ),
    inference(resolution,[status(thm)],[c_70,c_511])).

tff(c_589,plain,(
    ! [A_156,B_157] :
      ( l1_pre_topc(k8_tmap_1(A_156,B_157))
      | ~ v2_pre_topc(A_156)
      | v2_struct_0(A_156)
      | ~ m1_pre_topc(B_157,A_156)
      | ~ l1_pre_topc(A_156)
      | ~ v2_pre_topc(A_156)
      | v2_struct_0(A_156)
      | ~ m1_pre_topc(B_157,A_156)
      | ~ l1_pre_topc(A_156) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_524,c_70])).

tff(c_30,plain,(
    m1_pre_topc('#skF_4',k8_tmap_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_28,plain,(
    u1_struct_0('#skF_3') = u1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_522,plain,(
    ! [A_39,B_41] :
      ( k6_tmap_1(A_39,u1_struct_0(B_41)) = k8_tmap_1(A_39,B_41)
      | ~ v2_pre_topc(A_39)
      | v2_struct_0(A_39)
      | ~ m1_pre_topc(B_41,A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(resolution,[status(thm)],[c_70,c_511])).

tff(c_16,plain,(
    ! [C_31,A_25] :
      ( v3_pre_topc(C_31,k6_tmap_1(A_25,C_31))
      | ~ m1_subset_1(C_31,k1_zfmisc_1(u1_struct_0(k6_tmap_1(A_25,C_31))))
      | ~ m1_subset_1(C_31,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1110,plain,(
    ! [B_195,A_196] :
      ( v3_pre_topc(u1_struct_0(B_195),k6_tmap_1(A_196,u1_struct_0(B_195)))
      | ~ m1_subset_1(u1_struct_0(B_195),k1_zfmisc_1(u1_struct_0(k8_tmap_1(A_196,B_195))))
      | ~ m1_subset_1(u1_struct_0(B_195),k1_zfmisc_1(u1_struct_0(A_196)))
      | ~ l1_pre_topc(A_196)
      | ~ v2_pre_topc(A_196)
      | v2_struct_0(A_196)
      | ~ v2_pre_topc(A_196)
      | v2_struct_0(A_196)
      | ~ m1_pre_topc(B_195,A_196)
      | ~ l1_pre_topc(A_196) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_524,c_16])).

tff(c_1147,plain,(
    ! [B_198,A_199] :
      ( v3_pre_topc(u1_struct_0(B_198),k6_tmap_1(A_199,u1_struct_0(B_198)))
      | ~ m1_subset_1(u1_struct_0(B_198),k1_zfmisc_1(u1_struct_0(A_199)))
      | ~ v2_pre_topc(A_199)
      | v2_struct_0(A_199)
      | ~ m1_pre_topc(B_198,A_199)
      | ~ l1_pre_topc(A_199)
      | ~ m1_pre_topc(B_198,k8_tmap_1(A_199,B_198))
      | ~ l1_pre_topc(k8_tmap_1(A_199,B_198)) ) ),
    inference(resolution,[status(thm)],[c_24,c_1110])).

tff(c_2418,plain,(
    ! [B_258,A_259] :
      ( v3_pre_topc(u1_struct_0(B_258),k8_tmap_1(A_259,B_258))
      | ~ m1_subset_1(u1_struct_0(B_258),k1_zfmisc_1(u1_struct_0(A_259)))
      | ~ v2_pre_topc(A_259)
      | v2_struct_0(A_259)
      | ~ m1_pre_topc(B_258,A_259)
      | ~ l1_pre_topc(A_259)
      | ~ m1_pre_topc(B_258,k8_tmap_1(A_259,B_258))
      | ~ l1_pre_topc(k8_tmap_1(A_259,B_258))
      | ~ v2_pre_topc(A_259)
      | v2_struct_0(A_259)
      | ~ m1_pre_topc(B_258,A_259)
      | ~ l1_pre_topc(A_259) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_522,c_1147])).

tff(c_2431,plain,(
    ! [B_260,A_261] :
      ( v3_pre_topc(u1_struct_0(B_260),k8_tmap_1(A_261,B_260))
      | ~ m1_pre_topc(B_260,k8_tmap_1(A_261,B_260))
      | ~ l1_pre_topc(k8_tmap_1(A_261,B_260))
      | ~ v2_pre_topc(A_261)
      | v2_struct_0(A_261)
      | ~ m1_pre_topc(B_260,A_261)
      | ~ l1_pre_topc(A_261) ) ),
    inference(resolution,[status(thm)],[c_24,c_2418])).

tff(c_2459,plain,(
    ! [A_262] :
      ( v3_pre_topc(u1_struct_0('#skF_4'),k8_tmap_1(A_262,'#skF_3'))
      | ~ m1_pre_topc('#skF_3',k8_tmap_1(A_262,'#skF_3'))
      | ~ l1_pre_topc(k8_tmap_1(A_262,'#skF_3'))
      | ~ v2_pre_topc(A_262)
      | v2_struct_0(A_262)
      | ~ m1_pre_topc('#skF_3',A_262)
      | ~ l1_pre_topc(A_262) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2431])).

tff(c_113,plain,(
    ! [B_64,A_65] :
      ( v1_tsep_1(B_64,A_65)
      | ~ v3_pre_topc(u1_struct_0(B_64),A_65)
      | ~ m1_subset_1(u1_struct_0(B_64),k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ m1_pre_topc(B_64,A_65)
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_127,plain,(
    ! [B_41,A_39] :
      ( v1_tsep_1(B_41,A_39)
      | ~ v3_pre_topc(u1_struct_0(B_41),A_39)
      | ~ v2_pre_topc(A_39)
      | ~ m1_pre_topc(B_41,A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(resolution,[status(thm)],[c_24,c_113])).

tff(c_2872,plain,(
    ! [A_269] :
      ( v1_tsep_1('#skF_4',k8_tmap_1(A_269,'#skF_3'))
      | ~ v2_pre_topc(k8_tmap_1(A_269,'#skF_3'))
      | ~ m1_pre_topc('#skF_4',k8_tmap_1(A_269,'#skF_3'))
      | ~ m1_pre_topc('#skF_3',k8_tmap_1(A_269,'#skF_3'))
      | ~ l1_pre_topc(k8_tmap_1(A_269,'#skF_3'))
      | ~ v2_pre_topc(A_269)
      | v2_struct_0(A_269)
      | ~ m1_pre_topc('#skF_3',A_269)
      | ~ l1_pre_topc(A_269) ) ),
    inference(resolution,[status(thm)],[c_2459,c_127])).

tff(c_26,plain,
    ( ~ m1_pre_topc('#skF_4',k8_tmap_1('#skF_2','#skF_3'))
    | ~ v1_tsep_1('#skF_4',k8_tmap_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_42,plain,(
    ~ v1_tsep_1('#skF_4',k8_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26])).

tff(c_2875,plain,
    ( ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_4',k8_tmap_1('#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_3',k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2872,c_42])).

tff(c_2902,plain,
    ( ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_3',k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_38,c_30,c_2875])).

tff(c_2903,plain,
    ( ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_3',k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_2902])).

tff(c_2910,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2903])).

tff(c_2916,plain,
    ( ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_589,c_2910])).

tff(c_2923,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_38,c_2916])).

tff(c_2925,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_2923])).

tff(c_2927,plain,(
    l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2903])).

tff(c_586,plain,(
    ! [A_156,B_157] :
      ( v2_pre_topc(k8_tmap_1(A_156,B_157))
      | ~ v2_pre_topc(A_156)
      | v2_struct_0(A_156)
      | ~ m1_pre_topc(B_157,A_156)
      | ~ l1_pre_topc(A_156)
      | ~ v2_pre_topc(A_156)
      | v2_struct_0(A_156)
      | ~ m1_pre_topc(B_157,A_156)
      | ~ l1_pre_topc(A_156) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_524,c_87])).

tff(c_2926,plain,
    ( ~ m1_pre_topc('#skF_3',k8_tmap_1('#skF_2','#skF_3'))
    | ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2903])).

tff(c_2928,plain,(
    ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2926])).

tff(c_2948,plain,
    ( ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_586,c_2928])).

tff(c_2955,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_38,c_2948])).

tff(c_2957,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_2955])).

tff(c_2959,plain,(
    v2_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2926])).

tff(c_47,plain,(
    ! [B_46,A_47] :
      ( m1_subset_1(u1_struct_0(B_46),k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ m1_pre_topc(B_46,A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_50,plain,(
    ! [A_47] :
      ( m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ m1_pre_topc('#skF_3',A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_47])).

tff(c_595,plain,(
    ! [A_156] :
      ( k6_tmap_1(A_156,u1_struct_0('#skF_4')) = k8_tmap_1(A_156,'#skF_3')
      | ~ v2_pre_topc(A_156)
      | v2_struct_0(A_156)
      | ~ m1_pre_topc('#skF_3',A_156)
      | ~ l1_pre_topc(A_156) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_524])).

tff(c_598,plain,(
    ! [A_158] :
      ( k6_tmap_1(A_158,u1_struct_0('#skF_4')) = k8_tmap_1(A_158,'#skF_3')
      | ~ v2_pre_topc(A_158)
      | v2_struct_0(A_158)
      | ~ m1_pre_topc('#skF_3',A_158)
      | ~ l1_pre_topc(A_158) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_524])).

tff(c_1059,plain,(
    ! [A_192] :
      ( v3_pre_topc(u1_struct_0('#skF_4'),k6_tmap_1(A_192,u1_struct_0('#skF_4')))
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(k8_tmap_1(A_192,'#skF_3'))))
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_192)))
      | ~ l1_pre_topc(A_192)
      | ~ v2_pre_topc(A_192)
      | v2_struct_0(A_192)
      | ~ v2_pre_topc(A_192)
      | v2_struct_0(A_192)
      | ~ m1_pre_topc('#skF_3',A_192)
      | ~ l1_pre_topc(A_192) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_598,c_16])).

tff(c_1094,plain,(
    ! [A_194] :
      ( v3_pre_topc(u1_struct_0('#skF_4'),k6_tmap_1(A_194,u1_struct_0('#skF_4')))
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_194)))
      | ~ v2_pre_topc(A_194)
      | v2_struct_0(A_194)
      | ~ m1_pre_topc('#skF_3',A_194)
      | ~ l1_pre_topc(A_194)
      | ~ m1_pre_topc('#skF_4',k8_tmap_1(A_194,'#skF_3'))
      | ~ l1_pre_topc(k8_tmap_1(A_194,'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_24,c_1059])).

tff(c_3121,plain,(
    ! [A_280] :
      ( v3_pre_topc(u1_struct_0('#skF_4'),k8_tmap_1(A_280,'#skF_3'))
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_280)))
      | ~ v2_pre_topc(A_280)
      | v2_struct_0(A_280)
      | ~ m1_pre_topc('#skF_3',A_280)
      | ~ l1_pre_topc(A_280)
      | ~ m1_pre_topc('#skF_4',k8_tmap_1(A_280,'#skF_3'))
      | ~ l1_pre_topc(k8_tmap_1(A_280,'#skF_3'))
      | ~ v2_pre_topc(A_280)
      | v2_struct_0(A_280)
      | ~ m1_pre_topc('#skF_3',A_280)
      | ~ l1_pre_topc(A_280) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_595,c_1094])).

tff(c_3135,plain,(
    ! [A_281] :
      ( v3_pre_topc(u1_struct_0('#skF_4'),k8_tmap_1(A_281,'#skF_3'))
      | ~ m1_pre_topc('#skF_4',k8_tmap_1(A_281,'#skF_3'))
      | ~ l1_pre_topc(k8_tmap_1(A_281,'#skF_3'))
      | ~ v2_pre_topc(A_281)
      | v2_struct_0(A_281)
      | ~ m1_pre_topc('#skF_3',A_281)
      | ~ l1_pre_topc(A_281) ) ),
    inference(resolution,[status(thm)],[c_50,c_3121])).

tff(c_3174,plain,(
    ! [A_282] :
      ( v1_tsep_1('#skF_4',k8_tmap_1(A_282,'#skF_3'))
      | ~ v2_pre_topc(k8_tmap_1(A_282,'#skF_3'))
      | ~ m1_pre_topc('#skF_4',k8_tmap_1(A_282,'#skF_3'))
      | ~ l1_pre_topc(k8_tmap_1(A_282,'#skF_3'))
      | ~ v2_pre_topc(A_282)
      | v2_struct_0(A_282)
      | ~ m1_pre_topc('#skF_3',A_282)
      | ~ l1_pre_topc(A_282) ) ),
    inference(resolution,[status(thm)],[c_3135,c_127])).

tff(c_3177,plain,
    ( ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_4',k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_3174,c_42])).

tff(c_3204,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_38,c_2927,c_30,c_2959,c_3177])).

tff(c_3206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_3204])).

%------------------------------------------------------------------------------
