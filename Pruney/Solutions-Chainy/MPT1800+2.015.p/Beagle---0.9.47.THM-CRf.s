%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:00 EST 2020

% Result     : Theorem 9.20s
% Output     : CNFRefutation 9.24s
% Verified   : 
% Statistics : Number of formulae       :  167 (1083 expanded)
%              Number of leaves         :   30 ( 394 expanded)
%              Depth                    :   30
%              Number of atoms          :  623 (4589 expanded)
%              Number of equality atoms :   88 ( 688 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k8_tmap_1 > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

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

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_tmap_1,type,(
    k5_tmap_1: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_152,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ( ( v1_tsep_1(B,A)
                & m1_pre_topc(B,A) )
            <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k8_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_tmap_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_pre_topc(k8_tmap_1(A,B))
        & v2_pre_topc(k8_tmap_1(A,B))
        & l1_pre_topc(k8_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tsep_1(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tsep_1)).

tff(f_132,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_103,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k6_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_89,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
            & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_125,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ( u1_struct_0(k8_tmap_1(A,B)) = u1_struct_0(A)
            & ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => u1_pre_topc(k8_tmap_1(A,B)) = k5_tmap_1(A,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_tmap_1)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_38,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_48,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k8_tmap_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ v1_tsep_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_61,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k8_tmap_1('#skF_2','#skF_3')
    | ~ v1_tsep_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_48])).

tff(c_71,plain,(
    ~ v1_tsep_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_61])).

tff(c_42,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_44,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( v1_pre_topc(k8_tmap_1(A_14,B_15))
      | ~ m1_pre_topc(B_15,A_14)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( l1_pre_topc(k8_tmap_1(A_14,B_15))
      | ~ m1_pre_topc(B_15,A_14)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_89,plain,(
    ! [B_36,A_37] :
      ( u1_struct_0(B_36) = '#skF_1'(A_37,B_36)
      | v1_tsep_1(B_36,A_37)
      | ~ m1_pre_topc(B_36,A_37)
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_92,plain,
    ( u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_89,c_71])).

tff(c_95,plain,(
    u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_92])).

tff(c_36,plain,(
    ! [B_31,A_29] :
      ( m1_subset_1(u1_struct_0(B_31),k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ m1_pre_topc(B_31,A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_99,plain,(
    ! [A_29] :
      ( m1_subset_1('#skF_1'('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ m1_pre_topc('#skF_3',A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_36])).

tff(c_58,plain,
    ( v1_tsep_1('#skF_3','#skF_2')
    | g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k8_tmap_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_73,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k8_tmap_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_58])).

tff(c_569,plain,(
    ! [B_91,A_92] :
      ( v3_pre_topc(B_91,A_92)
      | k6_tmap_1(A_92,B_91) != g1_pre_topc(u1_struct_0(A_92),u1_pre_topc(A_92))
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92)
      | ~ v2_pre_topc(A_92)
      | v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_585,plain,(
    ! [B_91] :
      ( v3_pre_topc(B_91,'#skF_2')
      | k8_tmap_1('#skF_2','#skF_3') != k6_tmap_1('#skF_2',B_91)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_569])).

tff(c_591,plain,(
    ! [B_91] :
      ( v3_pre_topc(B_91,'#skF_2')
      | k8_tmap_1('#skF_2','#skF_3') != k6_tmap_1('#skF_2',B_91)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_585])).

tff(c_631,plain,(
    ! [B_95] :
      ( v3_pre_topc(B_95,'#skF_2')
      | k8_tmap_1('#skF_2','#skF_3') != k6_tmap_1('#skF_2',B_95)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_591])).

tff(c_639,plain,
    ( v3_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | k6_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')) != k8_tmap_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_99,c_631])).

tff(c_649,plain,
    ( v3_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | k6_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')) != k8_tmap_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_639])).

tff(c_653,plain,(
    k6_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')) != k8_tmap_1('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_649])).

tff(c_170,plain,(
    ! [A_60,B_61] :
      ( m1_subset_1('#skF_1'(A_60,B_61),k1_zfmisc_1(u1_struct_0(A_60)))
      | v1_tsep_1(B_61,A_60)
      | ~ m1_pre_topc(B_61,A_60)
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( v1_pre_topc(k6_tmap_1(A_12,B_13))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_183,plain,(
    ! [A_60,B_61] :
      ( v1_pre_topc(k6_tmap_1(A_60,'#skF_1'(A_60,B_61)))
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60)
      | v1_tsep_1(B_61,A_60)
      | ~ m1_pre_topc(B_61,A_60)
      | ~ l1_pre_topc(A_60) ) ),
    inference(resolution,[status(thm)],[c_170,c_16])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( l1_pre_topc(k6_tmap_1(A_12,B_13))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_184,plain,(
    ! [A_60,B_61] :
      ( l1_pre_topc(k6_tmap_1(A_60,'#skF_1'(A_60,B_61)))
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60)
      | v1_tsep_1(B_61,A_60)
      | ~ m1_pre_topc(B_61,A_60)
      | ~ l1_pre_topc(A_60) ) ),
    inference(resolution,[status(thm)],[c_170,c_12])).

tff(c_230,plain,(
    ! [A_66,B_67] :
      ( u1_struct_0(k6_tmap_1(A_66,B_67)) = u1_struct_0(A_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_251,plain,(
    ! [A_68,B_69] :
      ( u1_struct_0(k6_tmap_1(A_68,u1_struct_0(B_69))) = u1_struct_0(A_68)
      | ~ v2_pre_topc(A_68)
      | v2_struct_0(A_68)
      | ~ m1_pre_topc(B_69,A_68)
      | ~ l1_pre_topc(A_68) ) ),
    inference(resolution,[status(thm)],[c_36,c_230])).

tff(c_1380,plain,(
    ! [B_139,A_140,B_141] :
      ( m1_subset_1(u1_struct_0(B_139),k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ m1_pre_topc(B_139,k6_tmap_1(A_140,u1_struct_0(B_141)))
      | ~ l1_pre_topc(k6_tmap_1(A_140,u1_struct_0(B_141)))
      | ~ v2_pre_topc(A_140)
      | v2_struct_0(A_140)
      | ~ m1_pre_topc(B_141,A_140)
      | ~ l1_pre_topc(A_140) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_36])).

tff(c_1394,plain,(
    ! [B_139,A_140] :
      ( m1_subset_1(u1_struct_0(B_139),k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ m1_pre_topc(B_139,k6_tmap_1(A_140,'#skF_1'('#skF_2','#skF_3')))
      | ~ l1_pre_topc(k6_tmap_1(A_140,u1_struct_0('#skF_3')))
      | ~ v2_pre_topc(A_140)
      | v2_struct_0(A_140)
      | ~ m1_pre_topc('#skF_3',A_140)
      | ~ l1_pre_topc(A_140) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_1380])).

tff(c_1793,plain,(
    ! [B_209,A_210] :
      ( m1_subset_1(u1_struct_0(B_209),k1_zfmisc_1(u1_struct_0(A_210)))
      | ~ m1_pre_topc(B_209,k6_tmap_1(A_210,'#skF_1'('#skF_2','#skF_3')))
      | ~ l1_pre_topc(k6_tmap_1(A_210,'#skF_1'('#skF_2','#skF_3')))
      | ~ v2_pre_topc(A_210)
      | v2_struct_0(A_210)
      | ~ m1_pre_topc('#skF_3',A_210)
      | ~ l1_pre_topc(A_210) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_1394])).

tff(c_592,plain,(
    ! [B_91] :
      ( v3_pre_topc(B_91,'#skF_2')
      | k8_tmap_1('#skF_2','#skF_3') != k6_tmap_1('#skF_2',B_91)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_591])).

tff(c_1804,plain,(
    ! [B_209] :
      ( v3_pre_topc(u1_struct_0(B_209),'#skF_2')
      | k6_tmap_1('#skF_2',u1_struct_0(B_209)) != k8_tmap_1('#skF_2','#skF_3')
      | ~ m1_pre_topc(B_209,k6_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')))
      | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')))
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1793,c_592])).

tff(c_1857,plain,(
    ! [B_209] :
      ( v3_pre_topc(u1_struct_0(B_209),'#skF_2')
      | k6_tmap_1('#skF_2',u1_struct_0(B_209)) != k8_tmap_1('#skF_2','#skF_3')
      | ~ m1_pre_topc(B_209,k6_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')))
      | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_44,c_1804])).

tff(c_1858,plain,(
    ! [B_209] :
      ( v3_pre_topc(u1_struct_0(B_209),'#skF_2')
      | k6_tmap_1('#skF_2',u1_struct_0(B_209)) != k8_tmap_1('#skF_2','#skF_3')
      | ~ m1_pre_topc(B_209,k6_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')))
      | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1857])).

tff(c_1866,plain,(
    ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1858])).

tff(c_1872,plain,
    ( ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | v1_tsep_1('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_184,c_1866])).

tff(c_1881,plain,
    ( v2_struct_0('#skF_2')
    | v1_tsep_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_44,c_1872])).

tff(c_1883,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_46,c_1881])).

tff(c_1885,plain,(
    l1_pre_topc(k6_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1858])).

tff(c_10,plain,(
    ! [A_2,B_8] :
      ( m1_subset_1('#skF_1'(A_2,B_8),k1_zfmisc_1(u1_struct_0(A_2)))
      | v1_tsep_1(B_8,A_2)
      | ~ m1_pre_topc(B_8,A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_593,plain,(
    ! [A_93,B_94] :
      ( k5_tmap_1(A_93,u1_struct_0(B_94)) = u1_pre_topc(k8_tmap_1(A_93,B_94))
      | ~ m1_subset_1(u1_struct_0(B_94),k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ m1_pre_topc(B_94,A_93)
      | v2_struct_0(B_94)
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_620,plain,(
    ! [A_93] :
      ( k5_tmap_1(A_93,u1_struct_0('#skF_3')) = u1_pre_topc(k8_tmap_1(A_93,'#skF_3'))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ m1_pre_topc('#skF_3',A_93)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_593])).

tff(c_627,plain,(
    ! [A_93] :
      ( k5_tmap_1(A_93,'#skF_1'('#skF_2','#skF_3')) = u1_pre_topc(k8_tmap_1(A_93,'#skF_3'))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ m1_pre_topc('#skF_3',A_93)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_620])).

tff(c_654,plain,(
    ! [A_96] :
      ( k5_tmap_1(A_96,'#skF_1'('#skF_2','#skF_3')) = u1_pre_topc(k8_tmap_1(A_96,'#skF_3'))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ m1_pre_topc('#skF_3',A_96)
      | ~ l1_pre_topc(A_96)
      | ~ v2_pre_topc(A_96)
      | v2_struct_0(A_96) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_627])).

tff(c_670,plain,
    ( k5_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')) = u1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | v1_tsep_1('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_654])).

tff(c_679,plain,
    ( k5_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')) = u1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2')
    | v1_tsep_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_44,c_670])).

tff(c_680,plain,(
    k5_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')) = u1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_46,c_679])).

tff(c_408,plain,(
    ! [A_76,B_77] :
      ( u1_pre_topc(k6_tmap_1(A_76,B_77)) = k5_tmap_1(A_76,B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76)
      | ~ v2_pre_topc(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_430,plain,(
    ! [A_2,B_8] :
      ( u1_pre_topc(k6_tmap_1(A_2,'#skF_1'(A_2,B_8))) = k5_tmap_1(A_2,'#skF_1'(A_2,B_8))
      | ~ v2_pre_topc(A_2)
      | v2_struct_0(A_2)
      | v1_tsep_1(B_8,A_2)
      | ~ m1_pre_topc(B_8,A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(resolution,[status(thm)],[c_10,c_408])).

tff(c_308,plain,(
    ! [A_70] :
      ( u1_struct_0(k6_tmap_1(A_70,'#skF_1'('#skF_2','#skF_3'))) = u1_struct_0(A_70)
      | ~ v2_pre_topc(A_70)
      | v2_struct_0(A_70)
      | ~ m1_pre_topc('#skF_3',A_70)
      | ~ l1_pre_topc(A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_251])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3959,plain,(
    ! [A_369] :
      ( g1_pre_topc(u1_struct_0(A_369),u1_pre_topc(k6_tmap_1(A_369,'#skF_1'('#skF_2','#skF_3')))) = k6_tmap_1(A_369,'#skF_1'('#skF_2','#skF_3'))
      | ~ v1_pre_topc(k6_tmap_1(A_369,'#skF_1'('#skF_2','#skF_3')))
      | ~ l1_pre_topc(k6_tmap_1(A_369,'#skF_1'('#skF_2','#skF_3')))
      | ~ v2_pre_topc(A_369)
      | v2_struct_0(A_369)
      | ~ m1_pre_topc('#skF_3',A_369)
      | ~ l1_pre_topc(A_369) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_2])).

tff(c_3975,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3'))) = k6_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3'))
    | ~ v1_pre_topc(k6_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')))
    | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')))
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | v1_tsep_1('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_430,c_3959])).

tff(c_3997,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))) = k6_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3'))
    | ~ v1_pre_topc(k6_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')))
    | v2_struct_0('#skF_2')
    | v1_tsep_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_44,c_42,c_38,c_44,c_1885,c_680,c_3975])).

tff(c_3998,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))) = k6_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3'))
    | ~ v1_pre_topc(k6_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_46,c_3997])).

tff(c_4000,plain,(
    ~ v1_pre_topc(k6_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_3998])).

tff(c_4006,plain,
    ( ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | v1_tsep_1('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_183,c_4000])).

tff(c_4015,plain,
    ( v2_struct_0('#skF_2')
    | v1_tsep_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_44,c_4006])).

tff(c_4017,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_46,c_4015])).

tff(c_4018,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))) = k6_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3998])).

tff(c_188,plain,(
    ! [A_64,B_65] :
      ( u1_struct_0(k8_tmap_1(A_64,B_65)) = u1_struct_0(A_64)
      | ~ m1_pre_topc(B_65,A_64)
      | v2_struct_0(B_65)
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_224,plain,(
    ! [A_64,B_65] :
      ( g1_pre_topc(u1_struct_0(A_64),u1_pre_topc(k8_tmap_1(A_64,B_65))) = k8_tmap_1(A_64,B_65)
      | ~ v1_pre_topc(k8_tmap_1(A_64,B_65))
      | ~ l1_pre_topc(k8_tmap_1(A_64,B_65))
      | ~ m1_pre_topc(B_65,A_64)
      | v2_struct_0(B_65)
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64)
      | v2_struct_0(A_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_2])).

tff(c_4031,plain,
    ( k6_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')) = k8_tmap_1('#skF_2','#skF_3')
    | ~ v1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4018,c_224])).

tff(c_4044,plain,
    ( k6_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')) = k8_tmap_1('#skF_2','#skF_3')
    | ~ v1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_38,c_4031])).

tff(c_4045,plain,
    ( ~ v1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_40,c_653,c_4044])).

tff(c_4053,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_4045])).

tff(c_4056,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_4053])).

tff(c_4059,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_38,c_4056])).

tff(c_4061,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_4059])).

tff(c_4062,plain,(
    ~ v1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_4045])).

tff(c_4174,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_4062])).

tff(c_4177,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_38,c_4174])).

tff(c_4179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_4177])).

tff(c_4180,plain,(
    v3_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_649])).

tff(c_6,plain,(
    ! [A_2,B_8] :
      ( ~ v3_pre_topc('#skF_1'(A_2,B_8),A_2)
      | v1_tsep_1(B_8,A_2)
      | ~ m1_pre_topc(B_8,A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4184,plain,
    ( v1_tsep_1('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4180,c_6])).

tff(c_4187,plain,(
    v1_tsep_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_4184])).

tff(c_4189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_4187])).

tff(c_4190,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k8_tmap_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_4191,plain,(
    v1_tsep_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_4476,plain,(
    ! [A_425,B_426] :
      ( k5_tmap_1(A_425,u1_struct_0(B_426)) = u1_pre_topc(k8_tmap_1(A_425,B_426))
      | ~ m1_subset_1(u1_struct_0(B_426),k1_zfmisc_1(u1_struct_0(A_425)))
      | ~ m1_pre_topc(B_426,A_425)
      | v2_struct_0(B_426)
      | ~ l1_pre_topc(A_425)
      | ~ v2_pre_topc(A_425)
      | v2_struct_0(A_425) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_4498,plain,(
    ! [A_29,B_31] :
      ( k5_tmap_1(A_29,u1_struct_0(B_31)) = u1_pre_topc(k8_tmap_1(A_29,B_31))
      | v2_struct_0(B_31)
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29)
      | ~ m1_pre_topc(B_31,A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_36,c_4476])).

tff(c_4362,plain,(
    ! [A_409,B_410] :
      ( u1_pre_topc(k6_tmap_1(A_409,B_410)) = k5_tmap_1(A_409,B_410)
      | ~ m1_subset_1(B_410,k1_zfmisc_1(u1_struct_0(A_409)))
      | ~ l1_pre_topc(A_409)
      | ~ v2_pre_topc(A_409)
      | v2_struct_0(A_409) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4376,plain,(
    ! [A_29,B_31] :
      ( u1_pre_topc(k6_tmap_1(A_29,u1_struct_0(B_31))) = k5_tmap_1(A_29,u1_struct_0(B_31))
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29)
      | ~ m1_pre_topc(B_31,A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_36,c_4362])).

tff(c_4338,plain,(
    ! [B_405,A_406] :
      ( v3_pre_topc(u1_struct_0(B_405),A_406)
      | ~ m1_subset_1(u1_struct_0(B_405),k1_zfmisc_1(u1_struct_0(A_406)))
      | ~ v1_tsep_1(B_405,A_406)
      | ~ m1_pre_topc(B_405,A_406)
      | ~ l1_pre_topc(A_406) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4354,plain,(
    ! [B_31,A_29] :
      ( v3_pre_topc(u1_struct_0(B_31),A_29)
      | ~ v1_tsep_1(B_31,A_29)
      | ~ m1_pre_topc(B_31,A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_36,c_4338])).

tff(c_4463,plain,(
    ! [A_423,B_424] :
      ( k6_tmap_1(A_423,B_424) = g1_pre_topc(u1_struct_0(A_423),u1_pre_topc(A_423))
      | ~ v3_pre_topc(B_424,A_423)
      | ~ m1_subset_1(B_424,k1_zfmisc_1(u1_struct_0(A_423)))
      | ~ l1_pre_topc(A_423)
      | ~ v2_pre_topc(A_423)
      | v2_struct_0(A_423) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_4545,plain,(
    ! [A_433,B_434] :
      ( k6_tmap_1(A_433,u1_struct_0(B_434)) = g1_pre_topc(u1_struct_0(A_433),u1_pre_topc(A_433))
      | ~ v3_pre_topc(u1_struct_0(B_434),A_433)
      | ~ v2_pre_topc(A_433)
      | v2_struct_0(A_433)
      | ~ m1_pre_topc(B_434,A_433)
      | ~ l1_pre_topc(A_433) ) ),
    inference(resolution,[status(thm)],[c_36,c_4463])).

tff(c_4557,plain,(
    ! [A_29,B_31] :
      ( k6_tmap_1(A_29,u1_struct_0(B_31)) = g1_pre_topc(u1_struct_0(A_29),u1_pre_topc(A_29))
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29)
      | ~ v1_tsep_1(B_31,A_29)
      | ~ m1_pre_topc(B_31,A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_4354,c_4545])).

tff(c_4558,plain,(
    ! [A_435,B_436] :
      ( k6_tmap_1(A_435,u1_struct_0(B_436)) = g1_pre_topc(u1_struct_0(A_435),u1_pre_topc(A_435))
      | ~ v2_pre_topc(A_435)
      | v2_struct_0(A_435)
      | ~ v1_tsep_1(B_436,A_435)
      | ~ m1_pre_topc(B_436,A_435)
      | ~ l1_pre_topc(A_435) ) ),
    inference(resolution,[status(thm)],[c_4354,c_4545])).

tff(c_4205,plain,(
    ! [A_385,B_386] :
      ( l1_pre_topc(k6_tmap_1(A_385,B_386))
      | ~ m1_subset_1(B_386,k1_zfmisc_1(u1_struct_0(A_385)))
      | ~ l1_pre_topc(A_385)
      | ~ v2_pre_topc(A_385)
      | v2_struct_0(A_385) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4209,plain,(
    ! [A_29,B_31] :
      ( l1_pre_topc(k6_tmap_1(A_29,u1_struct_0(B_31)))
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29)
      | ~ m1_pre_topc(B_31,A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_36,c_4205])).

tff(c_5052,plain,(
    ! [A_514,B_515] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_514),u1_pre_topc(A_514)))
      | ~ v2_pre_topc(A_514)
      | v2_struct_0(A_514)
      | ~ m1_pre_topc(B_515,A_514)
      | ~ l1_pre_topc(A_514)
      | ~ v2_pre_topc(A_514)
      | v2_struct_0(A_514)
      | ~ v1_tsep_1(B_515,A_514)
      | ~ m1_pre_topc(B_515,A_514)
      | ~ l1_pre_topc(A_514) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4558,c_4209])).

tff(c_5056,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4191,c_5052])).

tff(c_5060,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_44,c_5056])).

tff(c_5061,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_5060])).

tff(c_4211,plain,(
    ! [A_389,B_390] :
      ( v1_pre_topc(k6_tmap_1(A_389,B_390))
      | ~ m1_subset_1(B_390,k1_zfmisc_1(u1_struct_0(A_389)))
      | ~ l1_pre_topc(A_389)
      | ~ v2_pre_topc(A_389)
      | v2_struct_0(A_389) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4215,plain,(
    ! [A_29,B_31] :
      ( v1_pre_topc(k6_tmap_1(A_29,u1_struct_0(B_31)))
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29)
      | ~ m1_pre_topc(B_31,A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_36,c_4211])).

tff(c_4876,plain,(
    ! [A_493,B_494] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_493),u1_pre_topc(A_493)))
      | ~ v2_pre_topc(A_493)
      | v2_struct_0(A_493)
      | ~ m1_pre_topc(B_494,A_493)
      | ~ l1_pre_topc(A_493)
      | ~ v2_pre_topc(A_493)
      | v2_struct_0(A_493)
      | ~ v1_tsep_1(B_494,A_493)
      | ~ m1_pre_topc(B_494,A_493)
      | ~ l1_pre_topc(A_493) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4558,c_4215])).

tff(c_4880,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4191,c_4876])).

tff(c_4884,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_44,c_4880])).

tff(c_4885,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_4884])).

tff(c_4275,plain,(
    ! [A_401,B_402] :
      ( u1_struct_0(k6_tmap_1(A_401,B_402)) = u1_struct_0(A_401)
      | ~ m1_subset_1(B_402,k1_zfmisc_1(u1_struct_0(A_401)))
      | ~ l1_pre_topc(A_401)
      | ~ v2_pre_topc(A_401)
      | v2_struct_0(A_401) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4286,plain,(
    ! [A_29,B_31] :
      ( u1_struct_0(k6_tmap_1(A_29,u1_struct_0(B_31))) = u1_struct_0(A_29)
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29)
      | ~ m1_pre_topc(B_31,A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_36,c_4275])).

tff(c_5197,plain,(
    ! [A_534,B_535] :
      ( u1_struct_0(g1_pre_topc(u1_struct_0(A_534),u1_pre_topc(A_534))) = u1_struct_0(A_534)
      | ~ v2_pre_topc(A_534)
      | v2_struct_0(A_534)
      | ~ m1_pre_topc(B_535,A_534)
      | ~ l1_pre_topc(A_534)
      | ~ v2_pre_topc(A_534)
      | v2_struct_0(A_534)
      | ~ v1_tsep_1(B_535,A_534)
      | ~ m1_pre_topc(B_535,A_534)
      | ~ l1_pre_topc(A_534) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4558,c_4286])).

tff(c_5201,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = u1_struct_0('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4191,c_5197])).

tff(c_5205,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = u1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_44,c_5201])).

tff(c_5206,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = u1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_5205])).

tff(c_5329,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_5206,c_2])).

tff(c_5377,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5061,c_4885,c_5329])).

tff(c_5700,plain,(
    ! [B_31] :
      ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc(k6_tmap_1('#skF_2',u1_struct_0(B_31)))) = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ v1_tsep_1(B_31,'#skF_2')
      | ~ m1_pre_topc(B_31,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4557,c_5377])).

tff(c_5707,plain,(
    ! [B_31] :
      ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc(k6_tmap_1('#skF_2',u1_struct_0(B_31)))) = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ v1_tsep_1(B_31,'#skF_2')
      | ~ m1_pre_topc(B_31,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_5700])).

tff(c_6048,plain,(
    ! [B_561] :
      ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc(k6_tmap_1('#skF_2',u1_struct_0(B_561)))) = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ v1_tsep_1(B_561,'#skF_2')
      | ~ m1_pre_topc(B_561,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_5707])).

tff(c_6075,plain,(
    ! [B_31] :
      ( g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2',u1_struct_0(B_31))) = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ v1_tsep_1(B_31,'#skF_2')
      | ~ m1_pre_topc(B_31,'#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_31,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4376,c_6048])).

tff(c_6091,plain,(
    ! [B_31] :
      ( g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2',u1_struct_0(B_31))) = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ v1_tsep_1(B_31,'#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_31,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_6075])).

tff(c_6093,plain,(
    ! [B_562] :
      ( g1_pre_topc(u1_struct_0('#skF_2'),k5_tmap_1('#skF_2',u1_struct_0(B_562))) = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ v1_tsep_1(B_562,'#skF_2')
      | ~ m1_pre_topc(B_562,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_6091])).

tff(c_6109,plain,(
    ! [B_31] :
      ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc(k8_tmap_1('#skF_2',B_31))) = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ v1_tsep_1(B_31,'#skF_2')
      | ~ m1_pre_topc(B_31,'#skF_2')
      | v2_struct_0(B_31)
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_31,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4498,c_6093])).

tff(c_6122,plain,(
    ! [B_31] :
      ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc(k8_tmap_1('#skF_2',B_31))) = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ v1_tsep_1(B_31,'#skF_2')
      | v2_struct_0(B_31)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_31,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_6109])).

tff(c_6337,plain,(
    ! [B_575] :
      ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc(k8_tmap_1('#skF_2',B_575))) = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ v1_tsep_1(B_575,'#skF_2')
      | v2_struct_0(B_575)
      | ~ m1_pre_topc(B_575,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_6122])).

tff(c_4235,plain,(
    ! [A_397,B_398] :
      ( u1_struct_0(k8_tmap_1(A_397,B_398)) = u1_struct_0(A_397)
      | ~ m1_pre_topc(B_398,A_397)
      | v2_struct_0(B_398)
      | ~ l1_pre_topc(A_397)
      | ~ v2_pre_topc(A_397)
      | v2_struct_0(A_397) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_4265,plain,(
    ! [A_397,B_398] :
      ( g1_pre_topc(u1_struct_0(A_397),u1_pre_topc(k8_tmap_1(A_397,B_398))) = k8_tmap_1(A_397,B_398)
      | ~ v1_pre_topc(k8_tmap_1(A_397,B_398))
      | ~ l1_pre_topc(k8_tmap_1(A_397,B_398))
      | ~ m1_pre_topc(B_398,A_397)
      | v2_struct_0(B_398)
      | ~ l1_pre_topc(A_397)
      | ~ v2_pre_topc(A_397)
      | v2_struct_0(A_397) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4235,c_2])).

tff(c_6343,plain,(
    ! [B_575] :
      ( k8_tmap_1('#skF_2',B_575) = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ v1_pre_topc(k8_tmap_1('#skF_2',B_575))
      | ~ l1_pre_topc(k8_tmap_1('#skF_2',B_575))
      | ~ m1_pre_topc(B_575,'#skF_2')
      | v2_struct_0(B_575)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ v1_tsep_1(B_575,'#skF_2')
      | v2_struct_0(B_575)
      | ~ m1_pre_topc(B_575,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6337,c_4265])).

tff(c_6353,plain,(
    ! [B_575] :
      ( k8_tmap_1('#skF_2',B_575) = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ v1_pre_topc(k8_tmap_1('#skF_2',B_575))
      | ~ l1_pre_topc(k8_tmap_1('#skF_2',B_575))
      | v2_struct_0('#skF_2')
      | ~ v1_tsep_1(B_575,'#skF_2')
      | v2_struct_0(B_575)
      | ~ m1_pre_topc(B_575,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_6343])).

tff(c_6646,plain,(
    ! [B_599] :
      ( k8_tmap_1('#skF_2',B_599) = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ v1_pre_topc(k8_tmap_1('#skF_2',B_599))
      | ~ l1_pre_topc(k8_tmap_1('#skF_2',B_599))
      | ~ v1_tsep_1(B_599,'#skF_2')
      | v2_struct_0(B_599)
      | ~ m1_pre_topc(B_599,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_6353])).

tff(c_6649,plain,(
    ! [B_15] :
      ( k8_tmap_1('#skF_2',B_15) = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ l1_pre_topc(k8_tmap_1('#skF_2',B_15))
      | ~ v1_tsep_1(B_15,'#skF_2')
      | v2_struct_0(B_15)
      | ~ m1_pre_topc(B_15,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_6646])).

tff(c_6652,plain,(
    ! [B_15] :
      ( k8_tmap_1('#skF_2',B_15) = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ l1_pre_topc(k8_tmap_1('#skF_2',B_15))
      | ~ v1_tsep_1(B_15,'#skF_2')
      | v2_struct_0(B_15)
      | ~ m1_pre_topc(B_15,'#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_6649])).

tff(c_6654,plain,(
    ! [B_600] :
      ( k8_tmap_1('#skF_2',B_600) = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ l1_pre_topc(k8_tmap_1('#skF_2',B_600))
      | ~ v1_tsep_1(B_600,'#skF_2')
      | v2_struct_0(B_600)
      | ~ m1_pre_topc(B_600,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_6652])).

tff(c_6657,plain,(
    ! [B_15] :
      ( k8_tmap_1('#skF_2',B_15) = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ v1_tsep_1(B_15,'#skF_2')
      | v2_struct_0(B_15)
      | ~ m1_pre_topc(B_15,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_6654])).

tff(c_6660,plain,(
    ! [B_15] :
      ( k8_tmap_1('#skF_2',B_15) = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ v1_tsep_1(B_15,'#skF_2')
      | v2_struct_0(B_15)
      | ~ m1_pre_topc(B_15,'#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_6657])).

tff(c_6662,plain,(
    ! [B_601] :
      ( k8_tmap_1('#skF_2',B_601) = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ v1_tsep_1(B_601,'#skF_2')
      | v2_struct_0(B_601)
      | ~ m1_pre_topc(B_601,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_6660])).

tff(c_6667,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k8_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_4191,c_6662])).

tff(c_6673,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k8_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_6667])).

tff(c_6675,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_4190,c_6673])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:30:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.20/3.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.24/3.26  
% 9.24/3.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.24/3.26  %$ v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k8_tmap_1 > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 9.24/3.26  
% 9.24/3.26  %Foreground sorts:
% 9.24/3.26  
% 9.24/3.26  
% 9.24/3.26  %Background operators:
% 9.24/3.26  
% 9.24/3.26  
% 9.24/3.26  %Foreground operators:
% 9.24/3.26  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.24/3.26  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 9.24/3.26  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 9.24/3.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.24/3.26  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 9.24/3.26  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.24/3.26  tff(k8_tmap_1, type, k8_tmap_1: ($i * $i) > $i).
% 9.24/3.26  tff('#skF_2', type, '#skF_2': $i).
% 9.24/3.26  tff('#skF_3', type, '#skF_3': $i).
% 9.24/3.26  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 9.24/3.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.24/3.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.24/3.26  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 9.24/3.26  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 9.24/3.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.24/3.26  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 9.24/3.26  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.24/3.26  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 9.24/3.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.24/3.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.24/3.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.24/3.26  
% 9.24/3.29  tff(f_152, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k8_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_tmap_1)).
% 9.24/3.29  tff(f_75, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_pre_topc(k8_tmap_1(A, B)) & v2_pre_topc(k8_tmap_1(A, B))) & l1_pre_topc(k8_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 9.24/3.29  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tsep_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tsep_1)).
% 9.24/3.29  tff(f_132, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 9.24/3.29  tff(f_103, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k6_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_tmap_1)).
% 9.24/3.29  tff(f_60, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 9.24/3.29  tff(f_89, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 9.24/3.29  tff(f_125, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => ((u1_struct_0(k8_tmap_1(A, B)) = u1_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (u1_pre_topc(k8_tmap_1(A, B)) = k5_tmap_1(A, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_tmap_1)).
% 9.24/3.29  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 9.24/3.29  tff(c_40, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_152])).
% 9.24/3.29  tff(c_38, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 9.24/3.29  tff(c_48, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k8_tmap_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~v1_tsep_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 9.24/3.29  tff(c_61, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k8_tmap_1('#skF_2', '#skF_3') | ~v1_tsep_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_48])).
% 9.24/3.29  tff(c_71, plain, (~v1_tsep_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_61])).
% 9.24/3.29  tff(c_42, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 9.24/3.29  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 9.24/3.29  tff(c_44, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 9.24/3.29  tff(c_22, plain, (![A_14, B_15]: (v1_pre_topc(k8_tmap_1(A_14, B_15)) | ~m1_pre_topc(B_15, A_14) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.24/3.29  tff(c_18, plain, (![A_14, B_15]: (l1_pre_topc(k8_tmap_1(A_14, B_15)) | ~m1_pre_topc(B_15, A_14) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.24/3.29  tff(c_89, plain, (![B_36, A_37]: (u1_struct_0(B_36)='#skF_1'(A_37, B_36) | v1_tsep_1(B_36, A_37) | ~m1_pre_topc(B_36, A_37) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.24/3.29  tff(c_92, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_89, c_71])).
% 9.24/3.29  tff(c_95, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_92])).
% 9.24/3.29  tff(c_36, plain, (![B_31, A_29]: (m1_subset_1(u1_struct_0(B_31), k1_zfmisc_1(u1_struct_0(A_29))) | ~m1_pre_topc(B_31, A_29) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.24/3.29  tff(c_99, plain, (![A_29]: (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0(A_29))) | ~m1_pre_topc('#skF_3', A_29) | ~l1_pre_topc(A_29))), inference(superposition, [status(thm), theory('equality')], [c_95, c_36])).
% 9.24/3.29  tff(c_58, plain, (v1_tsep_1('#skF_3', '#skF_2') | g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k8_tmap_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_152])).
% 9.24/3.29  tff(c_73, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k8_tmap_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_71, c_58])).
% 9.24/3.29  tff(c_569, plain, (![B_91, A_92]: (v3_pre_topc(B_91, A_92) | k6_tmap_1(A_92, B_91)!=g1_pre_topc(u1_struct_0(A_92), u1_pre_topc(A_92)) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92) | ~v2_pre_topc(A_92) | v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.24/3.29  tff(c_585, plain, (![B_91]: (v3_pre_topc(B_91, '#skF_2') | k8_tmap_1('#skF_2', '#skF_3')!=k6_tmap_1('#skF_2', B_91) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_569])).
% 9.24/3.29  tff(c_591, plain, (![B_91]: (v3_pre_topc(B_91, '#skF_2') | k8_tmap_1('#skF_2', '#skF_3')!=k6_tmap_1('#skF_2', B_91) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_585])).
% 9.24/3.29  tff(c_631, plain, (![B_95]: (v3_pre_topc(B_95, '#skF_2') | k8_tmap_1('#skF_2', '#skF_3')!=k6_tmap_1('#skF_2', B_95) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_46, c_591])).
% 9.24/3.29  tff(c_639, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | k6_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))!=k8_tmap_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_99, c_631])).
% 9.24/3.29  tff(c_649, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | k6_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))!=k8_tmap_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_639])).
% 9.24/3.29  tff(c_653, plain, (k6_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))!=k8_tmap_1('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_649])).
% 9.24/3.29  tff(c_170, plain, (![A_60, B_61]: (m1_subset_1('#skF_1'(A_60, B_61), k1_zfmisc_1(u1_struct_0(A_60))) | v1_tsep_1(B_61, A_60) | ~m1_pre_topc(B_61, A_60) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.24/3.29  tff(c_16, plain, (![A_12, B_13]: (v1_pre_topc(k6_tmap_1(A_12, B_13)) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_pre_topc(A_12) | ~v2_pre_topc(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.24/3.29  tff(c_183, plain, (![A_60, B_61]: (v1_pre_topc(k6_tmap_1(A_60, '#skF_1'(A_60, B_61))) | ~v2_pre_topc(A_60) | v2_struct_0(A_60) | v1_tsep_1(B_61, A_60) | ~m1_pre_topc(B_61, A_60) | ~l1_pre_topc(A_60))), inference(resolution, [status(thm)], [c_170, c_16])).
% 9.24/3.29  tff(c_12, plain, (![A_12, B_13]: (l1_pre_topc(k6_tmap_1(A_12, B_13)) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_pre_topc(A_12) | ~v2_pre_topc(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.24/3.29  tff(c_184, plain, (![A_60, B_61]: (l1_pre_topc(k6_tmap_1(A_60, '#skF_1'(A_60, B_61))) | ~v2_pre_topc(A_60) | v2_struct_0(A_60) | v1_tsep_1(B_61, A_60) | ~m1_pre_topc(B_61, A_60) | ~l1_pre_topc(A_60))), inference(resolution, [status(thm)], [c_170, c_12])).
% 9.24/3.29  tff(c_230, plain, (![A_66, B_67]: (u1_struct_0(k6_tmap_1(A_66, B_67))=u1_struct_0(A_66) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.24/3.29  tff(c_251, plain, (![A_68, B_69]: (u1_struct_0(k6_tmap_1(A_68, u1_struct_0(B_69)))=u1_struct_0(A_68) | ~v2_pre_topc(A_68) | v2_struct_0(A_68) | ~m1_pre_topc(B_69, A_68) | ~l1_pre_topc(A_68))), inference(resolution, [status(thm)], [c_36, c_230])).
% 9.24/3.29  tff(c_1380, plain, (![B_139, A_140, B_141]: (m1_subset_1(u1_struct_0(B_139), k1_zfmisc_1(u1_struct_0(A_140))) | ~m1_pre_topc(B_139, k6_tmap_1(A_140, u1_struct_0(B_141))) | ~l1_pre_topc(k6_tmap_1(A_140, u1_struct_0(B_141))) | ~v2_pre_topc(A_140) | v2_struct_0(A_140) | ~m1_pre_topc(B_141, A_140) | ~l1_pre_topc(A_140))), inference(superposition, [status(thm), theory('equality')], [c_251, c_36])).
% 9.24/3.29  tff(c_1394, plain, (![B_139, A_140]: (m1_subset_1(u1_struct_0(B_139), k1_zfmisc_1(u1_struct_0(A_140))) | ~m1_pre_topc(B_139, k6_tmap_1(A_140, '#skF_1'('#skF_2', '#skF_3'))) | ~l1_pre_topc(k6_tmap_1(A_140, u1_struct_0('#skF_3'))) | ~v2_pre_topc(A_140) | v2_struct_0(A_140) | ~m1_pre_topc('#skF_3', A_140) | ~l1_pre_topc(A_140))), inference(superposition, [status(thm), theory('equality')], [c_95, c_1380])).
% 9.24/3.29  tff(c_1793, plain, (![B_209, A_210]: (m1_subset_1(u1_struct_0(B_209), k1_zfmisc_1(u1_struct_0(A_210))) | ~m1_pre_topc(B_209, k6_tmap_1(A_210, '#skF_1'('#skF_2', '#skF_3'))) | ~l1_pre_topc(k6_tmap_1(A_210, '#skF_1'('#skF_2', '#skF_3'))) | ~v2_pre_topc(A_210) | v2_struct_0(A_210) | ~m1_pre_topc('#skF_3', A_210) | ~l1_pre_topc(A_210))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_1394])).
% 9.24/3.29  tff(c_592, plain, (![B_91]: (v3_pre_topc(B_91, '#skF_2') | k8_tmap_1('#skF_2', '#skF_3')!=k6_tmap_1('#skF_2', B_91) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_46, c_591])).
% 9.24/3.29  tff(c_1804, plain, (![B_209]: (v3_pre_topc(u1_struct_0(B_209), '#skF_2') | k6_tmap_1('#skF_2', u1_struct_0(B_209))!=k8_tmap_1('#skF_2', '#skF_3') | ~m1_pre_topc(B_209, k6_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))) | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_1793, c_592])).
% 9.24/3.29  tff(c_1857, plain, (![B_209]: (v3_pre_topc(u1_struct_0(B_209), '#skF_2') | k6_tmap_1('#skF_2', u1_struct_0(B_209))!=k8_tmap_1('#skF_2', '#skF_3') | ~m1_pre_topc(B_209, k6_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_44, c_1804])).
% 9.24/3.29  tff(c_1858, plain, (![B_209]: (v3_pre_topc(u1_struct_0(B_209), '#skF_2') | k6_tmap_1('#skF_2', u1_struct_0(B_209))!=k8_tmap_1('#skF_2', '#skF_3') | ~m1_pre_topc(B_209, k6_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_46, c_1857])).
% 9.24/3.29  tff(c_1866, plain, (~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_1858])).
% 9.24/3.29  tff(c_1872, plain, (~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v1_tsep_1('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_184, c_1866])).
% 9.24/3.29  tff(c_1881, plain, (v2_struct_0('#skF_2') | v1_tsep_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_44, c_1872])).
% 9.24/3.29  tff(c_1883, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_46, c_1881])).
% 9.24/3.29  tff(c_1885, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_1858])).
% 9.24/3.29  tff(c_10, plain, (![A_2, B_8]: (m1_subset_1('#skF_1'(A_2, B_8), k1_zfmisc_1(u1_struct_0(A_2))) | v1_tsep_1(B_8, A_2) | ~m1_pre_topc(B_8, A_2) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.24/3.29  tff(c_593, plain, (![A_93, B_94]: (k5_tmap_1(A_93, u1_struct_0(B_94))=u1_pre_topc(k8_tmap_1(A_93, B_94)) | ~m1_subset_1(u1_struct_0(B_94), k1_zfmisc_1(u1_struct_0(A_93))) | ~m1_pre_topc(B_94, A_93) | v2_struct_0(B_94) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_125])).
% 9.24/3.29  tff(c_620, plain, (![A_93]: (k5_tmap_1(A_93, u1_struct_0('#skF_3'))=u1_pre_topc(k8_tmap_1(A_93, '#skF_3')) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0(A_93))) | ~m1_pre_topc('#skF_3', A_93) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93) | v2_struct_0(A_93))), inference(superposition, [status(thm), theory('equality')], [c_95, c_593])).
% 9.24/3.29  tff(c_627, plain, (![A_93]: (k5_tmap_1(A_93, '#skF_1'('#skF_2', '#skF_3'))=u1_pre_topc(k8_tmap_1(A_93, '#skF_3')) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0(A_93))) | ~m1_pre_topc('#skF_3', A_93) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93) | v2_struct_0(A_93))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_620])).
% 9.24/3.29  tff(c_654, plain, (![A_96]: (k5_tmap_1(A_96, '#skF_1'('#skF_2', '#skF_3'))=u1_pre_topc(k8_tmap_1(A_96, '#skF_3')) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0(A_96))) | ~m1_pre_topc('#skF_3', A_96) | ~l1_pre_topc(A_96) | ~v2_pre_topc(A_96) | v2_struct_0(A_96))), inference(negUnitSimplification, [status(thm)], [c_40, c_627])).
% 9.24/3.29  tff(c_670, plain, (k5_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))=u1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v1_tsep_1('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_10, c_654])).
% 9.24/3.29  tff(c_679, plain, (k5_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))=u1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | v1_tsep_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_44, c_670])).
% 9.24/3.29  tff(c_680, plain, (k5_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))=u1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_71, c_46, c_679])).
% 9.24/3.29  tff(c_408, plain, (![A_76, B_77]: (u1_pre_topc(k6_tmap_1(A_76, B_77))=k5_tmap_1(A_76, B_77) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76) | ~v2_pre_topc(A_76) | v2_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.24/3.29  tff(c_430, plain, (![A_2, B_8]: (u1_pre_topc(k6_tmap_1(A_2, '#skF_1'(A_2, B_8)))=k5_tmap_1(A_2, '#skF_1'(A_2, B_8)) | ~v2_pre_topc(A_2) | v2_struct_0(A_2) | v1_tsep_1(B_8, A_2) | ~m1_pre_topc(B_8, A_2) | ~l1_pre_topc(A_2))), inference(resolution, [status(thm)], [c_10, c_408])).
% 9.24/3.29  tff(c_308, plain, (![A_70]: (u1_struct_0(k6_tmap_1(A_70, '#skF_1'('#skF_2', '#skF_3')))=u1_struct_0(A_70) | ~v2_pre_topc(A_70) | v2_struct_0(A_70) | ~m1_pre_topc('#skF_3', A_70) | ~l1_pre_topc(A_70))), inference(superposition, [status(thm), theory('equality')], [c_95, c_251])).
% 9.24/3.29  tff(c_2, plain, (![A_1]: (g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))=A_1 | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.24/3.29  tff(c_3959, plain, (![A_369]: (g1_pre_topc(u1_struct_0(A_369), u1_pre_topc(k6_tmap_1(A_369, '#skF_1'('#skF_2', '#skF_3'))))=k6_tmap_1(A_369, '#skF_1'('#skF_2', '#skF_3')) | ~v1_pre_topc(k6_tmap_1(A_369, '#skF_1'('#skF_2', '#skF_3'))) | ~l1_pre_topc(k6_tmap_1(A_369, '#skF_1'('#skF_2', '#skF_3'))) | ~v2_pre_topc(A_369) | v2_struct_0(A_369) | ~m1_pre_topc('#skF_3', A_369) | ~l1_pre_topc(A_369))), inference(superposition, [status(thm), theory('equality')], [c_308, c_2])).
% 9.24/3.29  tff(c_3975, plain, (g1_pre_topc(u1_struct_0('#skF_2'), k5_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3')))=k6_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3')) | ~v1_pre_topc(k6_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))) | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v1_tsep_1('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_430, c_3959])).
% 9.24/3.29  tff(c_3997, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')))=k6_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3')) | ~v1_pre_topc(k6_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))) | v2_struct_0('#skF_2') | v1_tsep_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_44, c_42, c_38, c_44, c_1885, c_680, c_3975])).
% 9.24/3.29  tff(c_3998, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')))=k6_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3')) | ~v1_pre_topc(k6_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_71, c_46, c_3997])).
% 9.24/3.29  tff(c_4000, plain, (~v1_pre_topc(k6_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_3998])).
% 9.24/3.29  tff(c_4006, plain, (~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v1_tsep_1('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_183, c_4000])).
% 9.24/3.29  tff(c_4015, plain, (v2_struct_0('#skF_2') | v1_tsep_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_44, c_4006])).
% 9.24/3.29  tff(c_4017, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_46, c_4015])).
% 9.24/3.29  tff(c_4018, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')))=k6_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_3998])).
% 9.24/3.29  tff(c_188, plain, (![A_64, B_65]: (u1_struct_0(k8_tmap_1(A_64, B_65))=u1_struct_0(A_64) | ~m1_pre_topc(B_65, A_64) | v2_struct_0(B_65) | ~l1_pre_topc(A_64) | ~v2_pre_topc(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_125])).
% 9.24/3.29  tff(c_224, plain, (![A_64, B_65]: (g1_pre_topc(u1_struct_0(A_64), u1_pre_topc(k8_tmap_1(A_64, B_65)))=k8_tmap_1(A_64, B_65) | ~v1_pre_topc(k8_tmap_1(A_64, B_65)) | ~l1_pre_topc(k8_tmap_1(A_64, B_65)) | ~m1_pre_topc(B_65, A_64) | v2_struct_0(B_65) | ~l1_pre_topc(A_64) | ~v2_pre_topc(A_64) | v2_struct_0(A_64))), inference(superposition, [status(thm), theory('equality')], [c_188, c_2])).
% 9.24/3.29  tff(c_4031, plain, (k6_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))=k8_tmap_1('#skF_2', '#skF_3') | ~v1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4018, c_224])).
% 9.24/3.29  tff(c_4044, plain, (k6_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))=k8_tmap_1('#skF_2', '#skF_3') | ~v1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_38, c_4031])).
% 9.24/3.29  tff(c_4045, plain, (~v1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_46, c_40, c_653, c_4044])).
% 9.24/3.29  tff(c_4053, plain, (~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_4045])).
% 9.24/3.29  tff(c_4056, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_18, c_4053])).
% 9.24/3.29  tff(c_4059, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_38, c_4056])).
% 9.24/3.29  tff(c_4061, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_4059])).
% 9.24/3.29  tff(c_4062, plain, (~v1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_4045])).
% 9.24/3.29  tff(c_4174, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_22, c_4062])).
% 9.24/3.29  tff(c_4177, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_38, c_4174])).
% 9.24/3.29  tff(c_4179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_4177])).
% 9.24/3.29  tff(c_4180, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_649])).
% 9.24/3.29  tff(c_6, plain, (![A_2, B_8]: (~v3_pre_topc('#skF_1'(A_2, B_8), A_2) | v1_tsep_1(B_8, A_2) | ~m1_pre_topc(B_8, A_2) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.24/3.29  tff(c_4184, plain, (v1_tsep_1('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4180, c_6])).
% 9.24/3.29  tff(c_4187, plain, (v1_tsep_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_4184])).
% 9.24/3.29  tff(c_4189, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_4187])).
% 9.24/3.29  tff(c_4190, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k8_tmap_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_61])).
% 9.24/3.29  tff(c_4191, plain, (v1_tsep_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_61])).
% 9.24/3.29  tff(c_4476, plain, (![A_425, B_426]: (k5_tmap_1(A_425, u1_struct_0(B_426))=u1_pre_topc(k8_tmap_1(A_425, B_426)) | ~m1_subset_1(u1_struct_0(B_426), k1_zfmisc_1(u1_struct_0(A_425))) | ~m1_pre_topc(B_426, A_425) | v2_struct_0(B_426) | ~l1_pre_topc(A_425) | ~v2_pre_topc(A_425) | v2_struct_0(A_425))), inference(cnfTransformation, [status(thm)], [f_125])).
% 9.24/3.29  tff(c_4498, plain, (![A_29, B_31]: (k5_tmap_1(A_29, u1_struct_0(B_31))=u1_pre_topc(k8_tmap_1(A_29, B_31)) | v2_struct_0(B_31) | ~v2_pre_topc(A_29) | v2_struct_0(A_29) | ~m1_pre_topc(B_31, A_29) | ~l1_pre_topc(A_29))), inference(resolution, [status(thm)], [c_36, c_4476])).
% 9.24/3.29  tff(c_4362, plain, (![A_409, B_410]: (u1_pre_topc(k6_tmap_1(A_409, B_410))=k5_tmap_1(A_409, B_410) | ~m1_subset_1(B_410, k1_zfmisc_1(u1_struct_0(A_409))) | ~l1_pre_topc(A_409) | ~v2_pre_topc(A_409) | v2_struct_0(A_409))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.24/3.29  tff(c_4376, plain, (![A_29, B_31]: (u1_pre_topc(k6_tmap_1(A_29, u1_struct_0(B_31)))=k5_tmap_1(A_29, u1_struct_0(B_31)) | ~v2_pre_topc(A_29) | v2_struct_0(A_29) | ~m1_pre_topc(B_31, A_29) | ~l1_pre_topc(A_29))), inference(resolution, [status(thm)], [c_36, c_4362])).
% 9.24/3.29  tff(c_4338, plain, (![B_405, A_406]: (v3_pre_topc(u1_struct_0(B_405), A_406) | ~m1_subset_1(u1_struct_0(B_405), k1_zfmisc_1(u1_struct_0(A_406))) | ~v1_tsep_1(B_405, A_406) | ~m1_pre_topc(B_405, A_406) | ~l1_pre_topc(A_406))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.24/3.29  tff(c_4354, plain, (![B_31, A_29]: (v3_pre_topc(u1_struct_0(B_31), A_29) | ~v1_tsep_1(B_31, A_29) | ~m1_pre_topc(B_31, A_29) | ~l1_pre_topc(A_29))), inference(resolution, [status(thm)], [c_36, c_4338])).
% 9.24/3.29  tff(c_4463, plain, (![A_423, B_424]: (k6_tmap_1(A_423, B_424)=g1_pre_topc(u1_struct_0(A_423), u1_pre_topc(A_423)) | ~v3_pre_topc(B_424, A_423) | ~m1_subset_1(B_424, k1_zfmisc_1(u1_struct_0(A_423))) | ~l1_pre_topc(A_423) | ~v2_pre_topc(A_423) | v2_struct_0(A_423))), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.24/3.29  tff(c_4545, plain, (![A_433, B_434]: (k6_tmap_1(A_433, u1_struct_0(B_434))=g1_pre_topc(u1_struct_0(A_433), u1_pre_topc(A_433)) | ~v3_pre_topc(u1_struct_0(B_434), A_433) | ~v2_pre_topc(A_433) | v2_struct_0(A_433) | ~m1_pre_topc(B_434, A_433) | ~l1_pre_topc(A_433))), inference(resolution, [status(thm)], [c_36, c_4463])).
% 9.24/3.29  tff(c_4557, plain, (![A_29, B_31]: (k6_tmap_1(A_29, u1_struct_0(B_31))=g1_pre_topc(u1_struct_0(A_29), u1_pre_topc(A_29)) | ~v2_pre_topc(A_29) | v2_struct_0(A_29) | ~v1_tsep_1(B_31, A_29) | ~m1_pre_topc(B_31, A_29) | ~l1_pre_topc(A_29))), inference(resolution, [status(thm)], [c_4354, c_4545])).
% 9.24/3.29  tff(c_4558, plain, (![A_435, B_436]: (k6_tmap_1(A_435, u1_struct_0(B_436))=g1_pre_topc(u1_struct_0(A_435), u1_pre_topc(A_435)) | ~v2_pre_topc(A_435) | v2_struct_0(A_435) | ~v1_tsep_1(B_436, A_435) | ~m1_pre_topc(B_436, A_435) | ~l1_pre_topc(A_435))), inference(resolution, [status(thm)], [c_4354, c_4545])).
% 9.24/3.29  tff(c_4205, plain, (![A_385, B_386]: (l1_pre_topc(k6_tmap_1(A_385, B_386)) | ~m1_subset_1(B_386, k1_zfmisc_1(u1_struct_0(A_385))) | ~l1_pre_topc(A_385) | ~v2_pre_topc(A_385) | v2_struct_0(A_385))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.24/3.29  tff(c_4209, plain, (![A_29, B_31]: (l1_pre_topc(k6_tmap_1(A_29, u1_struct_0(B_31))) | ~v2_pre_topc(A_29) | v2_struct_0(A_29) | ~m1_pre_topc(B_31, A_29) | ~l1_pre_topc(A_29))), inference(resolution, [status(thm)], [c_36, c_4205])).
% 9.24/3.29  tff(c_5052, plain, (![A_514, B_515]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_514), u1_pre_topc(A_514))) | ~v2_pre_topc(A_514) | v2_struct_0(A_514) | ~m1_pre_topc(B_515, A_514) | ~l1_pre_topc(A_514) | ~v2_pre_topc(A_514) | v2_struct_0(A_514) | ~v1_tsep_1(B_515, A_514) | ~m1_pre_topc(B_515, A_514) | ~l1_pre_topc(A_514))), inference(superposition, [status(thm), theory('equality')], [c_4558, c_4209])).
% 9.24/3.29  tff(c_5056, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4191, c_5052])).
% 9.24/3.29  tff(c_5060, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_44, c_5056])).
% 9.24/3.29  tff(c_5061, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_46, c_5060])).
% 9.24/3.29  tff(c_4211, plain, (![A_389, B_390]: (v1_pre_topc(k6_tmap_1(A_389, B_390)) | ~m1_subset_1(B_390, k1_zfmisc_1(u1_struct_0(A_389))) | ~l1_pre_topc(A_389) | ~v2_pre_topc(A_389) | v2_struct_0(A_389))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.24/3.29  tff(c_4215, plain, (![A_29, B_31]: (v1_pre_topc(k6_tmap_1(A_29, u1_struct_0(B_31))) | ~v2_pre_topc(A_29) | v2_struct_0(A_29) | ~m1_pre_topc(B_31, A_29) | ~l1_pre_topc(A_29))), inference(resolution, [status(thm)], [c_36, c_4211])).
% 9.24/3.29  tff(c_4876, plain, (![A_493, B_494]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_493), u1_pre_topc(A_493))) | ~v2_pre_topc(A_493) | v2_struct_0(A_493) | ~m1_pre_topc(B_494, A_493) | ~l1_pre_topc(A_493) | ~v2_pre_topc(A_493) | v2_struct_0(A_493) | ~v1_tsep_1(B_494, A_493) | ~m1_pre_topc(B_494, A_493) | ~l1_pre_topc(A_493))), inference(superposition, [status(thm), theory('equality')], [c_4558, c_4215])).
% 9.24/3.29  tff(c_4880, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4191, c_4876])).
% 9.24/3.29  tff(c_4884, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_44, c_4880])).
% 9.24/3.29  tff(c_4885, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_46, c_4884])).
% 9.24/3.29  tff(c_4275, plain, (![A_401, B_402]: (u1_struct_0(k6_tmap_1(A_401, B_402))=u1_struct_0(A_401) | ~m1_subset_1(B_402, k1_zfmisc_1(u1_struct_0(A_401))) | ~l1_pre_topc(A_401) | ~v2_pre_topc(A_401) | v2_struct_0(A_401))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.24/3.29  tff(c_4286, plain, (![A_29, B_31]: (u1_struct_0(k6_tmap_1(A_29, u1_struct_0(B_31)))=u1_struct_0(A_29) | ~v2_pre_topc(A_29) | v2_struct_0(A_29) | ~m1_pre_topc(B_31, A_29) | ~l1_pre_topc(A_29))), inference(resolution, [status(thm)], [c_36, c_4275])).
% 9.24/3.29  tff(c_5197, plain, (![A_534, B_535]: (u1_struct_0(g1_pre_topc(u1_struct_0(A_534), u1_pre_topc(A_534)))=u1_struct_0(A_534) | ~v2_pre_topc(A_534) | v2_struct_0(A_534) | ~m1_pre_topc(B_535, A_534) | ~l1_pre_topc(A_534) | ~v2_pre_topc(A_534) | v2_struct_0(A_534) | ~v1_tsep_1(B_535, A_534) | ~m1_pre_topc(B_535, A_534) | ~l1_pre_topc(A_534))), inference(superposition, [status(thm), theory('equality')], [c_4558, c_4286])).
% 9.24/3.29  tff(c_5201, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=u1_struct_0('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4191, c_5197])).
% 9.24/3.29  tff(c_5205, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=u1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_44, c_5201])).
% 9.24/3.29  tff(c_5206, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=u1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_46, c_5205])).
% 9.24/3.29  tff(c_5329, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_5206, c_2])).
% 9.24/3.29  tff(c_5377, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5061, c_4885, c_5329])).
% 9.24/3.29  tff(c_5700, plain, (![B_31]: (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc(k6_tmap_1('#skF_2', u1_struct_0(B_31))))=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~v1_tsep_1(B_31, '#skF_2') | ~m1_pre_topc(B_31, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4557, c_5377])).
% 9.24/3.29  tff(c_5707, plain, (![B_31]: (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc(k6_tmap_1('#skF_2', u1_struct_0(B_31))))=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | v2_struct_0('#skF_2') | ~v1_tsep_1(B_31, '#skF_2') | ~m1_pre_topc(B_31, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_5700])).
% 9.24/3.29  tff(c_6048, plain, (![B_561]: (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc(k6_tmap_1('#skF_2', u1_struct_0(B_561))))=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~v1_tsep_1(B_561, '#skF_2') | ~m1_pre_topc(B_561, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_46, c_5707])).
% 9.24/3.29  tff(c_6075, plain, (![B_31]: (g1_pre_topc(u1_struct_0('#skF_2'), k5_tmap_1('#skF_2', u1_struct_0(B_31)))=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~v1_tsep_1(B_31, '#skF_2') | ~m1_pre_topc(B_31, '#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(B_31, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4376, c_6048])).
% 9.24/3.29  tff(c_6091, plain, (![B_31]: (g1_pre_topc(u1_struct_0('#skF_2'), k5_tmap_1('#skF_2', u1_struct_0(B_31)))=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~v1_tsep_1(B_31, '#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(B_31, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_6075])).
% 9.24/3.29  tff(c_6093, plain, (![B_562]: (g1_pre_topc(u1_struct_0('#skF_2'), k5_tmap_1('#skF_2', u1_struct_0(B_562)))=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~v1_tsep_1(B_562, '#skF_2') | ~m1_pre_topc(B_562, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_46, c_6091])).
% 9.24/3.29  tff(c_6109, plain, (![B_31]: (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc(k8_tmap_1('#skF_2', B_31)))=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~v1_tsep_1(B_31, '#skF_2') | ~m1_pre_topc(B_31, '#skF_2') | v2_struct_0(B_31) | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(B_31, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4498, c_6093])).
% 9.24/3.29  tff(c_6122, plain, (![B_31]: (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc(k8_tmap_1('#skF_2', B_31)))=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~v1_tsep_1(B_31, '#skF_2') | v2_struct_0(B_31) | v2_struct_0('#skF_2') | ~m1_pre_topc(B_31, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_6109])).
% 9.24/3.29  tff(c_6337, plain, (![B_575]: (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc(k8_tmap_1('#skF_2', B_575)))=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~v1_tsep_1(B_575, '#skF_2') | v2_struct_0(B_575) | ~m1_pre_topc(B_575, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_46, c_6122])).
% 9.24/3.29  tff(c_4235, plain, (![A_397, B_398]: (u1_struct_0(k8_tmap_1(A_397, B_398))=u1_struct_0(A_397) | ~m1_pre_topc(B_398, A_397) | v2_struct_0(B_398) | ~l1_pre_topc(A_397) | ~v2_pre_topc(A_397) | v2_struct_0(A_397))), inference(cnfTransformation, [status(thm)], [f_125])).
% 9.24/3.29  tff(c_4265, plain, (![A_397, B_398]: (g1_pre_topc(u1_struct_0(A_397), u1_pre_topc(k8_tmap_1(A_397, B_398)))=k8_tmap_1(A_397, B_398) | ~v1_pre_topc(k8_tmap_1(A_397, B_398)) | ~l1_pre_topc(k8_tmap_1(A_397, B_398)) | ~m1_pre_topc(B_398, A_397) | v2_struct_0(B_398) | ~l1_pre_topc(A_397) | ~v2_pre_topc(A_397) | v2_struct_0(A_397))), inference(superposition, [status(thm), theory('equality')], [c_4235, c_2])).
% 9.24/3.29  tff(c_6343, plain, (![B_575]: (k8_tmap_1('#skF_2', B_575)=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~v1_pre_topc(k8_tmap_1('#skF_2', B_575)) | ~l1_pre_topc(k8_tmap_1('#skF_2', B_575)) | ~m1_pre_topc(B_575, '#skF_2') | v2_struct_0(B_575) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~v1_tsep_1(B_575, '#skF_2') | v2_struct_0(B_575) | ~m1_pre_topc(B_575, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_6337, c_4265])).
% 9.24/3.29  tff(c_6353, plain, (![B_575]: (k8_tmap_1('#skF_2', B_575)=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~v1_pre_topc(k8_tmap_1('#skF_2', B_575)) | ~l1_pre_topc(k8_tmap_1('#skF_2', B_575)) | v2_struct_0('#skF_2') | ~v1_tsep_1(B_575, '#skF_2') | v2_struct_0(B_575) | ~m1_pre_topc(B_575, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_6343])).
% 9.24/3.29  tff(c_6646, plain, (![B_599]: (k8_tmap_1('#skF_2', B_599)=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~v1_pre_topc(k8_tmap_1('#skF_2', B_599)) | ~l1_pre_topc(k8_tmap_1('#skF_2', B_599)) | ~v1_tsep_1(B_599, '#skF_2') | v2_struct_0(B_599) | ~m1_pre_topc(B_599, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_46, c_6353])).
% 9.24/3.29  tff(c_6649, plain, (![B_15]: (k8_tmap_1('#skF_2', B_15)=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~l1_pre_topc(k8_tmap_1('#skF_2', B_15)) | ~v1_tsep_1(B_15, '#skF_2') | v2_struct_0(B_15) | ~m1_pre_topc(B_15, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_6646])).
% 9.24/3.29  tff(c_6652, plain, (![B_15]: (k8_tmap_1('#skF_2', B_15)=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~l1_pre_topc(k8_tmap_1('#skF_2', B_15)) | ~v1_tsep_1(B_15, '#skF_2') | v2_struct_0(B_15) | ~m1_pre_topc(B_15, '#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_6649])).
% 9.24/3.29  tff(c_6654, plain, (![B_600]: (k8_tmap_1('#skF_2', B_600)=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~l1_pre_topc(k8_tmap_1('#skF_2', B_600)) | ~v1_tsep_1(B_600, '#skF_2') | v2_struct_0(B_600) | ~m1_pre_topc(B_600, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_46, c_6652])).
% 9.24/3.29  tff(c_6657, plain, (![B_15]: (k8_tmap_1('#skF_2', B_15)=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~v1_tsep_1(B_15, '#skF_2') | v2_struct_0(B_15) | ~m1_pre_topc(B_15, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_18, c_6654])).
% 9.24/3.29  tff(c_6660, plain, (![B_15]: (k8_tmap_1('#skF_2', B_15)=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~v1_tsep_1(B_15, '#skF_2') | v2_struct_0(B_15) | ~m1_pre_topc(B_15, '#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_6657])).
% 9.24/3.29  tff(c_6662, plain, (![B_601]: (k8_tmap_1('#skF_2', B_601)=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~v1_tsep_1(B_601, '#skF_2') | v2_struct_0(B_601) | ~m1_pre_topc(B_601, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_46, c_6660])).
% 9.24/3.29  tff(c_6667, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k8_tmap_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_4191, c_6662])).
% 9.24/3.29  tff(c_6673, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k8_tmap_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_6667])).
% 9.24/3.29  tff(c_6675, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_4190, c_6673])).
% 9.24/3.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.24/3.29  
% 9.24/3.29  Inference rules
% 9.24/3.29  ----------------------
% 9.24/3.29  #Ref     : 2
% 9.24/3.29  #Sup     : 1785
% 9.24/3.29  #Fact    : 0
% 9.24/3.29  #Define  : 0
% 9.24/3.29  #Split   : 13
% 9.24/3.29  #Chain   : 0
% 9.24/3.29  #Close   : 0
% 9.24/3.29  
% 9.24/3.29  Ordering : KBO
% 9.24/3.29  
% 9.24/3.29  Simplification rules
% 9.24/3.29  ----------------------
% 9.24/3.29  #Subsume      : 457
% 9.24/3.29  #Demod        : 857
% 9.24/3.29  #Tautology    : 158
% 9.24/3.29  #SimpNegUnit  : 243
% 9.24/3.29  #BackRed      : 0
% 9.24/3.29  
% 9.24/3.29  #Partial instantiations: 0
% 9.24/3.29  #Strategies tried      : 1
% 9.24/3.29  
% 9.24/3.29  Timing (in seconds)
% 9.24/3.29  ----------------------
% 9.24/3.29  Preprocessing        : 0.39
% 9.24/3.29  Parsing              : 0.19
% 9.24/3.29  CNF conversion       : 0.03
% 9.24/3.29  Main loop            : 2.08
% 9.24/3.29  Inferencing          : 0.64
% 9.24/3.29  Reduction            : 0.53
% 9.24/3.29  Demodulation         : 0.35
% 9.24/3.29  BG Simplification    : 0.09
% 9.24/3.29  Subsumption          : 0.69
% 9.24/3.29  Abstraction          : 0.10
% 9.24/3.29  MUC search           : 0.00
% 9.24/3.29  Cooper               : 0.00
% 9.24/3.29  Total                : 2.53
% 9.24/3.29  Index Insertion      : 0.00
% 9.24/3.29  Index Deletion       : 0.00
% 9.24/3.29  Index Matching       : 0.00
% 9.24/3.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
