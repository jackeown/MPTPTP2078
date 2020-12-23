%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1799+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:25 EST 2020

% Result     : Theorem 4.30s
% Output     : CNFRefutation 4.30s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 437 expanded)
%              Number of leaves         :   25 ( 165 expanded)
%              Depth                    :   19
%              Number of atoms          :  318 (2316 expanded)
%              Number of equality atoms :   14 ( 162 expanded)
%              Maximal formula depth    :   15 (   6 average)
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

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_pre_topc(k8_tmap_1(A,B))
        & v2_pre_topc(k8_tmap_1(A,B))
        & l1_pre_topc(k8_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).

tff(f_107,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

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

tff(c_10,plain,(
    ! [A_23,B_24] :
      ( l1_pre_topc(k8_tmap_1(A_23,B_24))
      | ~ m1_pre_topc(B_24,A_23)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_30,plain,(
    m1_pre_topc('#skF_4',k8_tmap_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_24,plain,(
    ! [B_41,A_39] :
      ( m1_subset_1(u1_struct_0(B_41),k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ m1_pre_topc(B_41,A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_14,plain,(
    ! [A_23,B_24] :
      ( v1_pre_topc(k8_tmap_1(A_23,B_24))
      | ~ m1_pre_topc(B_24,A_23)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_12,plain,(
    ! [A_23,B_24] :
      ( v2_pre_topc(k8_tmap_1(A_23,B_24))
      | ~ m1_pre_topc(B_24,A_23)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_163,plain,(
    ! [A_79,B_80] :
      ( k6_tmap_1(A_79,u1_struct_0(B_80)) = k8_tmap_1(A_79,B_80)
      | ~ m1_subset_1(u1_struct_0(B_80),k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(k8_tmap_1(A_79,B_80))
      | ~ v2_pre_topc(k8_tmap_1(A_79,B_80))
      | ~ v1_pre_topc(k8_tmap_1(A_79,B_80))
      | ~ m1_pre_topc(B_80,A_79)
      | ~ l1_pre_topc(A_79)
      | ~ v2_pre_topc(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_180,plain,(
    ! [A_81,B_82] :
      ( k6_tmap_1(A_81,u1_struct_0(B_82)) = k8_tmap_1(A_81,B_82)
      | ~ l1_pre_topc(k8_tmap_1(A_81,B_82))
      | ~ v2_pre_topc(k8_tmap_1(A_81,B_82))
      | ~ v1_pre_topc(k8_tmap_1(A_81,B_82))
      | ~ v2_pre_topc(A_81)
      | v2_struct_0(A_81)
      | ~ m1_pre_topc(B_82,A_81)
      | ~ l1_pre_topc(A_81) ) ),
    inference(resolution,[status(thm)],[c_24,c_163])).

tff(c_185,plain,(
    ! [A_83,B_84] :
      ( k6_tmap_1(A_83,u1_struct_0(B_84)) = k8_tmap_1(A_83,B_84)
      | ~ l1_pre_topc(k8_tmap_1(A_83,B_84))
      | ~ v1_pre_topc(k8_tmap_1(A_83,B_84))
      | ~ m1_pre_topc(B_84,A_83)
      | ~ l1_pre_topc(A_83)
      | ~ v2_pre_topc(A_83)
      | v2_struct_0(A_83) ) ),
    inference(resolution,[status(thm)],[c_12,c_180])).

tff(c_190,plain,(
    ! [A_85,B_86] :
      ( k6_tmap_1(A_85,u1_struct_0(B_86)) = k8_tmap_1(A_85,B_86)
      | ~ l1_pre_topc(k8_tmap_1(A_85,B_86))
      | ~ m1_pre_topc(B_86,A_85)
      | ~ l1_pre_topc(A_85)
      | ~ v2_pre_topc(A_85)
      | v2_struct_0(A_85) ) ),
    inference(resolution,[status(thm)],[c_14,c_185])).

tff(c_194,plain,(
    ! [A_23,B_24] :
      ( k6_tmap_1(A_23,u1_struct_0(B_24)) = k8_tmap_1(A_23,B_24)
      | ~ m1_pre_topc(B_24,A_23)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(resolution,[status(thm)],[c_10,c_190])).

tff(c_195,plain,(
    ! [A_87,B_88] :
      ( k6_tmap_1(A_87,u1_struct_0(B_88)) = k8_tmap_1(A_87,B_88)
      | ~ m1_pre_topc(B_88,A_87)
      | ~ l1_pre_topc(A_87)
      | ~ v2_pre_topc(A_87)
      | v2_struct_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_10,c_190])).

tff(c_16,plain,(
    ! [C_31,A_25] :
      ( v3_pre_topc(C_31,k6_tmap_1(A_25,C_31))
      | ~ m1_subset_1(C_31,k1_zfmisc_1(u1_struct_0(k6_tmap_1(A_25,C_31))))
      | ~ m1_subset_1(C_31,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_368,plain,(
    ! [B_113,A_114] :
      ( v3_pre_topc(u1_struct_0(B_113),k6_tmap_1(A_114,u1_struct_0(B_113)))
      | ~ m1_subset_1(u1_struct_0(B_113),k1_zfmisc_1(u1_struct_0(k8_tmap_1(A_114,B_113))))
      | ~ m1_subset_1(u1_struct_0(B_113),k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114)
      | ~ v2_pre_topc(A_114)
      | v2_struct_0(A_114)
      | ~ m1_pre_topc(B_113,A_114)
      | ~ l1_pre_topc(A_114)
      | ~ v2_pre_topc(A_114)
      | v2_struct_0(A_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_16])).

tff(c_399,plain,(
    ! [B_116,A_117] :
      ( v3_pre_topc(u1_struct_0(B_116),k6_tmap_1(A_117,u1_struct_0(B_116)))
      | ~ m1_subset_1(u1_struct_0(B_116),k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ m1_pre_topc(B_116,A_117)
      | ~ l1_pre_topc(A_117)
      | ~ v2_pre_topc(A_117)
      | v2_struct_0(A_117)
      | ~ m1_pre_topc(B_116,k8_tmap_1(A_117,B_116))
      | ~ l1_pre_topc(k8_tmap_1(A_117,B_116)) ) ),
    inference(resolution,[status(thm)],[c_24,c_368])).

tff(c_693,plain,(
    ! [B_155,A_156] :
      ( v3_pre_topc(u1_struct_0(B_155),k8_tmap_1(A_156,B_155))
      | ~ m1_subset_1(u1_struct_0(B_155),k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ m1_pre_topc(B_155,A_156)
      | ~ l1_pre_topc(A_156)
      | ~ v2_pre_topc(A_156)
      | v2_struct_0(A_156)
      | ~ m1_pre_topc(B_155,k8_tmap_1(A_156,B_155))
      | ~ l1_pre_topc(k8_tmap_1(A_156,B_155))
      | ~ m1_pre_topc(B_155,A_156)
      | ~ l1_pre_topc(A_156)
      | ~ v2_pre_topc(A_156)
      | v2_struct_0(A_156) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_399])).

tff(c_706,plain,(
    ! [B_157,A_158] :
      ( v3_pre_topc(u1_struct_0(B_157),k8_tmap_1(A_158,B_157))
      | ~ m1_pre_topc(B_157,k8_tmap_1(A_158,B_157))
      | ~ l1_pre_topc(k8_tmap_1(A_158,B_157))
      | ~ v2_pre_topc(A_158)
      | v2_struct_0(A_158)
      | ~ m1_pre_topc(B_157,A_158)
      | ~ l1_pre_topc(A_158) ) ),
    inference(resolution,[status(thm)],[c_24,c_693])).

tff(c_83,plain,(
    ! [B_60,A_61] :
      ( v1_tsep_1(B_60,A_61)
      | ~ v3_pre_topc(u1_struct_0(B_60),A_61)
      | ~ m1_subset_1(u1_struct_0(B_60),k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ m1_pre_topc(B_60,A_61)
      | ~ l1_pre_topc(A_61)
      | ~ v2_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_97,plain,(
    ! [B_41,A_39] :
      ( v1_tsep_1(B_41,A_39)
      | ~ v3_pre_topc(u1_struct_0(B_41),A_39)
      | ~ v2_pre_topc(A_39)
      | ~ m1_pre_topc(B_41,A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(resolution,[status(thm)],[c_24,c_83])).

tff(c_728,plain,(
    ! [B_160,A_161] :
      ( v1_tsep_1(B_160,k8_tmap_1(A_161,B_160))
      | ~ v2_pre_topc(k8_tmap_1(A_161,B_160))
      | ~ m1_pre_topc(B_160,k8_tmap_1(A_161,B_160))
      | ~ l1_pre_topc(k8_tmap_1(A_161,B_160))
      | ~ v2_pre_topc(A_161)
      | v2_struct_0(A_161)
      | ~ m1_pre_topc(B_160,A_161)
      | ~ l1_pre_topc(A_161) ) ),
    inference(resolution,[status(thm)],[c_706,c_97])).

tff(c_28,plain,(
    u1_struct_0('#skF_3') = u1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_62,plain,(
    ! [B_55,A_56] :
      ( v3_pre_topc(u1_struct_0(B_55),A_56)
      | ~ v1_tsep_1(B_55,A_56)
      | ~ m1_subset_1(u1_struct_0(B_55),k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ m1_pre_topc(B_55,A_56)
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_78,plain,(
    ! [B_57,A_58] :
      ( v3_pre_topc(u1_struct_0(B_57),A_58)
      | ~ v1_tsep_1(B_57,A_58)
      | ~ v2_pre_topc(A_58)
      | ~ m1_pre_topc(B_57,A_58)
      | ~ l1_pre_topc(A_58) ) ),
    inference(resolution,[status(thm)],[c_24,c_62])).

tff(c_81,plain,(
    ! [A_58] :
      ( v3_pre_topc(u1_struct_0('#skF_4'),A_58)
      | ~ v1_tsep_1('#skF_3',A_58)
      | ~ v2_pre_topc(A_58)
      | ~ m1_pre_topc('#skF_3',A_58)
      | ~ l1_pre_topc(A_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_78])).

tff(c_99,plain,(
    ! [B_62,A_63] :
      ( v1_tsep_1(B_62,A_63)
      | ~ v3_pre_topc(u1_struct_0(B_62),A_63)
      | ~ v2_pre_topc(A_63)
      | ~ m1_pre_topc(B_62,A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(resolution,[status(thm)],[c_24,c_83])).

tff(c_109,plain,(
    ! [A_58] :
      ( v1_tsep_1('#skF_4',A_58)
      | ~ m1_pre_topc('#skF_4',A_58)
      | ~ v1_tsep_1('#skF_3',A_58)
      | ~ v2_pre_topc(A_58)
      | ~ m1_pre_topc('#skF_3',A_58)
      | ~ l1_pre_topc(A_58) ) ),
    inference(resolution,[status(thm)],[c_81,c_99])).

tff(c_747,plain,(
    ! [A_165] :
      ( v1_tsep_1('#skF_4',k8_tmap_1(A_165,'#skF_3'))
      | ~ m1_pre_topc('#skF_4',k8_tmap_1(A_165,'#skF_3'))
      | ~ v2_pre_topc(k8_tmap_1(A_165,'#skF_3'))
      | ~ m1_pre_topc('#skF_3',k8_tmap_1(A_165,'#skF_3'))
      | ~ l1_pre_topc(k8_tmap_1(A_165,'#skF_3'))
      | ~ v2_pre_topc(A_165)
      | v2_struct_0(A_165)
      | ~ m1_pre_topc('#skF_3',A_165)
      | ~ l1_pre_topc(A_165) ) ),
    inference(resolution,[status(thm)],[c_728,c_109])).

tff(c_26,plain,
    ( ~ m1_pre_topc('#skF_4',k8_tmap_1('#skF_2','#skF_3'))
    | ~ v1_tsep_1('#skF_4',k8_tmap_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_42,plain,(
    ~ v1_tsep_1('#skF_4',k8_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26])).

tff(c_750,plain,
    ( ~ m1_pre_topc('#skF_4',k8_tmap_1('#skF_2','#skF_3'))
    | ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_3',k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_747,c_42])).

tff(c_753,plain,
    ( ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_3',k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_38,c_30,c_750])).

tff(c_754,plain,
    ( ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_3',k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_753])).

tff(c_755,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_754])).

tff(c_758,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_755])).

tff(c_761,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_32,c_758])).

tff(c_763,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_761])).

tff(c_765,plain,(
    l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_754])).

tff(c_764,plain,
    ( ~ m1_pre_topc('#skF_3',k8_tmap_1('#skF_2','#skF_3'))
    | ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_754])).

tff(c_766,plain,(
    ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_764])).

tff(c_769,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_766])).

tff(c_772,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_32,c_769])).

tff(c_774,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_772])).

tff(c_776,plain,(
    v2_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_764])).

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

tff(c_211,plain,(
    ! [A_87] :
      ( k6_tmap_1(A_87,u1_struct_0('#skF_4')) = k8_tmap_1(A_87,'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_87)
      | ~ l1_pre_topc(A_87)
      | ~ v2_pre_topc(A_87)
      | v2_struct_0(A_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_195])).

tff(c_379,plain,(
    ! [A_114] :
      ( v3_pre_topc(u1_struct_0('#skF_3'),k6_tmap_1(A_114,u1_struct_0('#skF_3')))
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(k8_tmap_1(A_114,'#skF_3'))))
      | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114)
      | ~ v2_pre_topc(A_114)
      | v2_struct_0(A_114)
      | ~ m1_pre_topc('#skF_3',A_114)
      | ~ l1_pre_topc(A_114)
      | ~ v2_pre_topc(A_114)
      | v2_struct_0(A_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_368])).

tff(c_439,plain,(
    ! [A_119] :
      ( v3_pre_topc(u1_struct_0('#skF_4'),k6_tmap_1(A_119,u1_struct_0('#skF_4')))
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(k8_tmap_1(A_119,'#skF_3'))))
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119)
      | v2_struct_0(A_119)
      | ~ m1_pre_topc('#skF_3',A_119)
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119)
      | v2_struct_0(A_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_28,c_379])).

tff(c_448,plain,(
    ! [A_120] :
      ( v3_pre_topc(u1_struct_0('#skF_4'),k6_tmap_1(A_120,u1_struct_0('#skF_4')))
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ m1_pre_topc('#skF_3',A_120)
      | ~ l1_pre_topc(A_120)
      | ~ v2_pre_topc(A_120)
      | v2_struct_0(A_120)
      | ~ m1_pre_topc('#skF_4',k8_tmap_1(A_120,'#skF_3'))
      | ~ l1_pre_topc(k8_tmap_1(A_120,'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_24,c_439])).

tff(c_959,plain,(
    ! [A_183] :
      ( v3_pre_topc(u1_struct_0('#skF_4'),k8_tmap_1(A_183,'#skF_3'))
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_183)))
      | ~ m1_pre_topc('#skF_3',A_183)
      | ~ l1_pre_topc(A_183)
      | ~ v2_pre_topc(A_183)
      | v2_struct_0(A_183)
      | ~ m1_pre_topc('#skF_4',k8_tmap_1(A_183,'#skF_3'))
      | ~ l1_pre_topc(k8_tmap_1(A_183,'#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_183)
      | ~ l1_pre_topc(A_183)
      | ~ v2_pre_topc(A_183)
      | v2_struct_0(A_183) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_448])).

tff(c_973,plain,(
    ! [A_184] :
      ( v3_pre_topc(u1_struct_0('#skF_4'),k8_tmap_1(A_184,'#skF_3'))
      | ~ m1_pre_topc('#skF_4',k8_tmap_1(A_184,'#skF_3'))
      | ~ l1_pre_topc(k8_tmap_1(A_184,'#skF_3'))
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184)
      | ~ m1_pre_topc('#skF_3',A_184)
      | ~ l1_pre_topc(A_184) ) ),
    inference(resolution,[status(thm)],[c_50,c_959])).

tff(c_982,plain,(
    ! [A_185] :
      ( v1_tsep_1('#skF_4',k8_tmap_1(A_185,'#skF_3'))
      | ~ v2_pre_topc(k8_tmap_1(A_185,'#skF_3'))
      | ~ m1_pre_topc('#skF_4',k8_tmap_1(A_185,'#skF_3'))
      | ~ l1_pre_topc(k8_tmap_1(A_185,'#skF_3'))
      | ~ v2_pre_topc(A_185)
      | v2_struct_0(A_185)
      | ~ m1_pre_topc('#skF_3',A_185)
      | ~ l1_pre_topc(A_185) ) ),
    inference(resolution,[status(thm)],[c_973,c_97])).

tff(c_985,plain,
    ( ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_4',k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_982,c_42])).

tff(c_988,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_38,c_765,c_30,c_776,c_985])).

tff(c_990,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_988])).

%------------------------------------------------------------------------------
