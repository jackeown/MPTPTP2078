%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:04 EST 2020

% Result     : Theorem 28.22s
% Output     : CNFRefutation 28.61s
% Verified   : 
% Statistics : Number of formulae       :  318 (16397 expanded)
%              Number of leaves         :   48 (5813 expanded)
%              Depth                    :   46
%              Number of atoms          : 1232 (82085 expanded)
%              Number of equality atoms :  126 (4146 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > v5_pre_topc > v1_funct_2 > v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k9_tmap_1 > k8_tmap_1 > k7_tmap_1 > k6_tmap_1 > k5_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_pre_topc > k6_partfun1 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k7_tmap_1,type,(
    k7_tmap_1: ( $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k9_tmap_1,type,(
    k9_tmap_1: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_tmap_1,type,(
    k8_tmap_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

tff(r1_funct_2,type,(
    r1_funct_2: ( $i * $i * $i * $i * $i * $i ) > $o )).

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_tmap_1,type,(
    k5_tmap_1: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_253,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ( ( v1_tsep_1(B,A)
                & m1_pre_topc(B,A) )
            <=> ( v1_funct_1(k9_tmap_1(A,B))
                & v1_funct_2(k9_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k8_tmap_1(A,B)))
                & v5_pre_topc(k9_tmap_1(A,B),A,k8_tmap_1(A,B))
                & m1_subset_1(k9_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k8_tmap_1(A,B))))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t122_tmap_1)).

tff(f_189,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_funct_1(k9_tmap_1(A,B))
        & v1_funct_2(k9_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k8_tmap_1(A,B)))
        & m1_subset_1(k9_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k8_tmap_1(A,B))))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_tmap_1)).

tff(f_144,axiom,(
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

tff(f_174,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_pre_topc(k8_tmap_1(A,B))
        & v2_pre_topc(k8_tmap_1(A,B))
        & l1_pre_topc(k8_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).

tff(f_230,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_104,axiom,(
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

tff(f_203,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
            & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_66,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(B)
        & ~ v1_xboole_0(D)
        & v1_funct_1(E)
        & v1_funct_2(E,A,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,C,D)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( r1_funct_2(A,B,C,D,E,F)
      <=> E = F ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

tff(f_37,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_78,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k7_tmap_1(A,B) = k6_partfun1(u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_tmap_1)).

tff(f_159,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_funct_1(k7_tmap_1(A,B))
        & v1_funct_2(k7_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B)))
        & m1_subset_1(k7_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B))))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_connsp_1)).

tff(f_130,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(k8_tmap_1(A,B)))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k8_tmap_1(A,B))))) )
             => ( C = k9_tmap_1(A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( D = u1_struct_0(B)
                     => r1_funct_2(u1_struct_0(A),u1_struct_0(k8_tmap_1(A,B)),u1_struct_0(A),u1_struct_0(k6_tmap_1(A,D)),C,k7_tmap_1(A,D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_tmap_1)).

tff(f_223,axiom,(
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

tff(c_80,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_78,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_76,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_74,plain,(
    m1_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_44656,plain,(
    ! [A_1709,B_1710] :
      ( v1_funct_1(k9_tmap_1(A_1709,B_1710))
      | ~ m1_pre_topc(B_1710,A_1709)
      | ~ l1_pre_topc(A_1709)
      | ~ v2_pre_topc(A_1709)
      | v2_struct_0(A_1709) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_15306,plain,(
    ! [A_619,B_620] :
      ( v1_funct_2(k9_tmap_1(A_619,B_620),u1_struct_0(A_619),u1_struct_0(k8_tmap_1(A_619,B_620)))
      | ~ m1_pre_topc(B_620,A_619)
      | ~ l1_pre_topc(A_619)
      | ~ v2_pre_topc(A_619)
      | v2_struct_0(A_619) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_15065,plain,(
    ! [A_580,B_581] :
      ( m1_subset_1(k9_tmap_1(A_580,B_581),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_580),u1_struct_0(k8_tmap_1(A_580,B_581)))))
      | ~ m1_pre_topc(B_581,A_580)
      | ~ l1_pre_topc(A_580)
      | ~ v2_pre_topc(A_580)
      | v2_struct_0(A_580) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_110,plain,
    ( v1_tsep_1('#skF_6','#skF_5')
    | v1_funct_1(k9_tmap_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_120,plain,(
    v1_funct_1(k9_tmap_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_104,plain,
    ( v1_tsep_1('#skF_6','#skF_5')
    | v1_funct_2(k9_tmap_1('#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_125,plain,(
    v1_funct_2(k9_tmap_1('#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_98,plain,
    ( v1_tsep_1('#skF_6','#skF_5')
    | v5_pre_topc(k9_tmap_1('#skF_5','#skF_6'),'#skF_5',k8_tmap_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_121,plain,(
    v5_pre_topc(k9_tmap_1('#skF_5','#skF_6'),'#skF_5',k8_tmap_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_92,plain,
    ( v1_tsep_1('#skF_6','#skF_5')
    | m1_subset_1(k9_tmap_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5','#skF_6'))))) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_129,plain,(
    m1_subset_1(k9_tmap_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5','#skF_6'))))) ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_82,plain,
    ( ~ m1_subset_1(k9_tmap_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5','#skF_6')))))
    | ~ v5_pre_topc(k9_tmap_1('#skF_5','#skF_6'),'#skF_5',k8_tmap_1('#skF_5','#skF_6'))
    | ~ v1_funct_2(k9_tmap_1('#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5','#skF_6')))
    | ~ v1_funct_1(k9_tmap_1('#skF_5','#skF_6'))
    | ~ m1_pre_topc('#skF_6','#skF_5')
    | ~ v1_tsep_1('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_115,plain,
    ( ~ m1_subset_1(k9_tmap_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5','#skF_6')))))
    | ~ v5_pre_topc(k9_tmap_1('#skF_5','#skF_6'),'#skF_5',k8_tmap_1('#skF_5','#skF_6'))
    | ~ v1_funct_2(k9_tmap_1('#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5','#skF_6')))
    | ~ v1_funct_1(k9_tmap_1('#skF_5','#skF_6'))
    | ~ v1_tsep_1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_82])).

tff(c_174,plain,(
    ~ v1_tsep_1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_125,c_121,c_129,c_115])).

tff(c_36,plain,(
    ! [B_64,A_58] :
      ( u1_struct_0(B_64) = '#skF_4'(A_58,B_64)
      | v1_tsep_1(B_64,A_58)
      | ~ m1_pre_topc(B_64,A_58)
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_177,plain,
    ( u1_struct_0('#skF_6') = '#skF_4'('#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_174])).

tff(c_180,plain,(
    u1_struct_0('#skF_6') = '#skF_4'('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_177])).

tff(c_46,plain,(
    ! [A_70,B_71] :
      ( l1_pre_topc(k8_tmap_1(A_70,B_71))
      | ~ m1_pre_topc(B_71,A_70)
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_50,plain,(
    ! [A_70,B_71] :
      ( v1_pre_topc(k8_tmap_1(A_70,B_71))
      | ~ m1_pre_topc(B_71,A_70)
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_48,plain,(
    ! [A_70,B_71] :
      ( v2_pre_topc(k8_tmap_1(A_70,B_71))
      | ~ m1_pre_topc(B_71,A_70)
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_72,plain,(
    ! [B_82,A_80] :
      ( m1_subset_1(u1_struct_0(B_82),k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ m1_pre_topc(B_82,A_80)
      | ~ l1_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_2461,plain,(
    ! [A_268,B_269] :
      ( k6_tmap_1(A_268,u1_struct_0(B_269)) = k8_tmap_1(A_268,B_269)
      | ~ m1_subset_1(u1_struct_0(B_269),k1_zfmisc_1(u1_struct_0(A_268)))
      | ~ l1_pre_topc(k8_tmap_1(A_268,B_269))
      | ~ v2_pre_topc(k8_tmap_1(A_268,B_269))
      | ~ v1_pre_topc(k8_tmap_1(A_268,B_269))
      | ~ m1_pre_topc(B_269,A_268)
      | ~ l1_pre_topc(A_268)
      | ~ v2_pre_topc(A_268)
      | v2_struct_0(A_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2525,plain,(
    ! [A_270,B_271] :
      ( k6_tmap_1(A_270,u1_struct_0(B_271)) = k8_tmap_1(A_270,B_271)
      | ~ l1_pre_topc(k8_tmap_1(A_270,B_271))
      | ~ v2_pre_topc(k8_tmap_1(A_270,B_271))
      | ~ v1_pre_topc(k8_tmap_1(A_270,B_271))
      | ~ v2_pre_topc(A_270)
      | v2_struct_0(A_270)
      | ~ m1_pre_topc(B_271,A_270)
      | ~ l1_pre_topc(A_270) ) ),
    inference(resolution,[status(thm)],[c_72,c_2461])).

tff(c_2530,plain,(
    ! [A_272,B_273] :
      ( k6_tmap_1(A_272,u1_struct_0(B_273)) = k8_tmap_1(A_272,B_273)
      | ~ l1_pre_topc(k8_tmap_1(A_272,B_273))
      | ~ v1_pre_topc(k8_tmap_1(A_272,B_273))
      | ~ m1_pre_topc(B_273,A_272)
      | ~ l1_pre_topc(A_272)
      | ~ v2_pre_topc(A_272)
      | v2_struct_0(A_272) ) ),
    inference(resolution,[status(thm)],[c_48,c_2525])).

tff(c_2535,plain,(
    ! [A_274,B_275] :
      ( k6_tmap_1(A_274,u1_struct_0(B_275)) = k8_tmap_1(A_274,B_275)
      | ~ l1_pre_topc(k8_tmap_1(A_274,B_275))
      | ~ m1_pre_topc(B_275,A_274)
      | ~ l1_pre_topc(A_274)
      | ~ v2_pre_topc(A_274)
      | v2_struct_0(A_274) ) ),
    inference(resolution,[status(thm)],[c_50,c_2530])).

tff(c_2541,plain,(
    ! [A_278,B_279] :
      ( k6_tmap_1(A_278,u1_struct_0(B_279)) = k8_tmap_1(A_278,B_279)
      | ~ m1_pre_topc(B_279,A_278)
      | ~ l1_pre_topc(A_278)
      | ~ v2_pre_topc(A_278)
      | v2_struct_0(A_278) ) ),
    inference(resolution,[status(thm)],[c_46,c_2535])).

tff(c_2625,plain,(
    ! [A_280] :
      ( k6_tmap_1(A_280,'#skF_4'('#skF_5','#skF_6')) = k8_tmap_1(A_280,'#skF_6')
      | ~ m1_pre_topc('#skF_6',A_280)
      | ~ l1_pre_topc(A_280)
      | ~ v2_pre_topc(A_280)
      | v2_struct_0(A_280) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_2541])).

tff(c_38,plain,(
    ! [A_58,B_64] :
      ( m1_subset_1('#skF_4'(A_58,B_64),k1_zfmisc_1(u1_struct_0(A_58)))
      | v1_tsep_1(B_64,A_58)
      | ~ m1_pre_topc(B_64,A_58)
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_215,plain,(
    ! [A_112,B_113] :
      ( u1_struct_0(k6_tmap_1(A_112,B_113)) = u1_struct_0(A_112)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112)
      | ~ v2_pre_topc(A_112)
      | v2_struct_0(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_229,plain,(
    ! [A_58,B_64] :
      ( u1_struct_0(k6_tmap_1(A_58,'#skF_4'(A_58,B_64))) = u1_struct_0(A_58)
      | ~ v2_pre_topc(A_58)
      | v2_struct_0(A_58)
      | v1_tsep_1(B_64,A_58)
      | ~ m1_pre_topc(B_64,A_58)
      | ~ l1_pre_topc(A_58) ) ),
    inference(resolution,[status(thm)],[c_38,c_215])).

tff(c_2684,plain,
    ( u1_struct_0(k8_tmap_1('#skF_5','#skF_6')) = u1_struct_0('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | v1_tsep_1('#skF_6','#skF_5')
    | ~ m1_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ m1_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2625,c_229])).

tff(c_2708,plain,
    ( u1_struct_0(k8_tmap_1('#skF_5','#skF_6')) = u1_struct_0('#skF_5')
    | v1_tsep_1('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_76,c_74,c_78,c_2684])).

tff(c_2709,plain,(
    u1_struct_0(k8_tmap_1('#skF_5','#skF_6')) = u1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_174,c_2708])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1828,plain,(
    ! [A_231,B_232] :
      ( k6_tmap_1(A_231,u1_struct_0(B_232)) = k8_tmap_1(A_231,B_232)
      | ~ m1_subset_1(u1_struct_0(B_232),k1_zfmisc_1(u1_struct_0(A_231)))
      | ~ l1_pre_topc(k8_tmap_1(A_231,B_232))
      | ~ v2_pre_topc(k8_tmap_1(A_231,B_232))
      | ~ v1_pre_topc(k8_tmap_1(A_231,B_232))
      | ~ m1_pre_topc(B_232,A_231)
      | ~ l1_pre_topc(A_231)
      | ~ v2_pre_topc(A_231)
      | v2_struct_0(A_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1914,plain,(
    ! [A_236,B_237] :
      ( k6_tmap_1(A_236,u1_struct_0(B_237)) = k8_tmap_1(A_236,B_237)
      | ~ l1_pre_topc(k8_tmap_1(A_236,B_237))
      | ~ v2_pre_topc(k8_tmap_1(A_236,B_237))
      | ~ v1_pre_topc(k8_tmap_1(A_236,B_237))
      | ~ v2_pre_topc(A_236)
      | v2_struct_0(A_236)
      | ~ m1_pre_topc(B_237,A_236)
      | ~ l1_pre_topc(A_236) ) ),
    inference(resolution,[status(thm)],[c_72,c_1828])).

tff(c_1990,plain,(
    ! [A_240,B_241] :
      ( k6_tmap_1(A_240,u1_struct_0(B_241)) = k8_tmap_1(A_240,B_241)
      | ~ l1_pre_topc(k8_tmap_1(A_240,B_241))
      | ~ v1_pre_topc(k8_tmap_1(A_240,B_241))
      | ~ m1_pre_topc(B_241,A_240)
      | ~ l1_pre_topc(A_240)
      | ~ v2_pre_topc(A_240)
      | v2_struct_0(A_240) ) ),
    inference(resolution,[status(thm)],[c_48,c_1914])).

tff(c_1995,plain,(
    ! [A_242,B_243] :
      ( k6_tmap_1(A_242,u1_struct_0(B_243)) = k8_tmap_1(A_242,B_243)
      | ~ l1_pre_topc(k8_tmap_1(A_242,B_243))
      | ~ m1_pre_topc(B_243,A_242)
      | ~ l1_pre_topc(A_242)
      | ~ v2_pre_topc(A_242)
      | v2_struct_0(A_242) ) ),
    inference(resolution,[status(thm)],[c_50,c_1990])).

tff(c_2000,plain,(
    ! [A_244,B_245] :
      ( k6_tmap_1(A_244,u1_struct_0(B_245)) = k8_tmap_1(A_244,B_245)
      | ~ m1_pre_topc(B_245,A_244)
      | ~ l1_pre_topc(A_244)
      | ~ v2_pre_topc(A_244)
      | v2_struct_0(A_244) ) ),
    inference(resolution,[status(thm)],[c_46,c_1995])).

tff(c_2078,plain,(
    ! [A_246] :
      ( k6_tmap_1(A_246,'#skF_4'('#skF_5','#skF_6')) = k8_tmap_1(A_246,'#skF_6')
      | ~ m1_pre_topc('#skF_6',A_246)
      | ~ l1_pre_topc(A_246)
      | ~ v2_pre_topc(A_246)
      | v2_struct_0(A_246) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_2000])).

tff(c_2126,plain,
    ( u1_struct_0(k8_tmap_1('#skF_5','#skF_6')) = u1_struct_0('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | v1_tsep_1('#skF_6','#skF_5')
    | ~ m1_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ m1_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2078,c_229])).

tff(c_2144,plain,
    ( u1_struct_0(k8_tmap_1('#skF_5','#skF_6')) = u1_struct_0('#skF_5')
    | v1_tsep_1('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_76,c_74,c_78,c_2126])).

tff(c_2145,plain,(
    u1_struct_0(k8_tmap_1('#skF_5','#skF_6')) = u1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_174,c_2144])).

tff(c_1651,plain,(
    ! [A_225,D_221,C_224,F_222,B_223] :
      ( r1_funct_2(A_225,B_223,C_224,D_221,F_222,F_222)
      | ~ m1_subset_1(F_222,k1_zfmisc_1(k2_zfmisc_1(C_224,D_221)))
      | ~ v1_funct_2(F_222,C_224,D_221)
      | ~ m1_subset_1(F_222,k1_zfmisc_1(k2_zfmisc_1(A_225,B_223)))
      | ~ v1_funct_2(F_222,A_225,B_223)
      | ~ v1_funct_1(F_222)
      | v1_xboole_0(D_221)
      | v1_xboole_0(B_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1657,plain,(
    ! [A_225,B_223] :
      ( r1_funct_2(A_225,B_223,u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5','#skF_6')),k9_tmap_1('#skF_5','#skF_6'),k9_tmap_1('#skF_5','#skF_6'))
      | ~ v1_funct_2(k9_tmap_1('#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5','#skF_6')))
      | ~ m1_subset_1(k9_tmap_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(A_225,B_223)))
      | ~ v1_funct_2(k9_tmap_1('#skF_5','#skF_6'),A_225,B_223)
      | ~ v1_funct_1(k9_tmap_1('#skF_5','#skF_6'))
      | v1_xboole_0(u1_struct_0(k8_tmap_1('#skF_5','#skF_6')))
      | v1_xboole_0(B_223) ) ),
    inference(resolution,[status(thm)],[c_129,c_1651])).

tff(c_1662,plain,(
    ! [A_225,B_223] :
      ( r1_funct_2(A_225,B_223,u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5','#skF_6')),k9_tmap_1('#skF_5','#skF_6'),k9_tmap_1('#skF_5','#skF_6'))
      | ~ m1_subset_1(k9_tmap_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(A_225,B_223)))
      | ~ v1_funct_2(k9_tmap_1('#skF_5','#skF_6'),A_225,B_223)
      | v1_xboole_0(u1_struct_0(k8_tmap_1('#skF_5','#skF_6')))
      | v1_xboole_0(B_223) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_125,c_1657])).

tff(c_1808,plain,(
    v1_xboole_0(u1_struct_0(k8_tmap_1('#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_1662])).

tff(c_2147,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2145,c_1808])).

tff(c_4,plain,(
    ! [A_2] :
      ( ~ v1_xboole_0(u1_struct_0(A_2))
      | ~ l1_struct_0(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2317,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_2147,c_4])).

tff(c_2320,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2317])).

tff(c_2323,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_2320])).

tff(c_2327,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2323])).

tff(c_2329,plain,(
    ~ v1_xboole_0(u1_struct_0(k8_tmap_1('#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_1662])).

tff(c_2712,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2709,c_2329])).

tff(c_2622,plain,(
    ! [A_278] :
      ( k6_tmap_1(A_278,'#skF_4'('#skF_5','#skF_6')) = k8_tmap_1(A_278,'#skF_6')
      | ~ m1_pre_topc('#skF_6',A_278)
      | ~ l1_pre_topc(A_278)
      | ~ v2_pre_topc(A_278)
      | v2_struct_0(A_278) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_2541])).

tff(c_196,plain,(
    ! [A_80] :
      ( m1_subset_1('#skF_4'('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ m1_pre_topc('#skF_6',A_80)
      | ~ l1_pre_topc(A_80) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_72])).

tff(c_146,plain,(
    ! [A_106,B_107] :
      ( k7_tmap_1(A_106,B_107) = k6_partfun1(u1_struct_0(A_106))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106)
      | v2_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_339,plain,(
    ! [A_119,B_120] :
      ( k7_tmap_1(A_119,u1_struct_0(B_120)) = k6_partfun1(u1_struct_0(A_119))
      | ~ v2_pre_topc(A_119)
      | v2_struct_0(A_119)
      | ~ m1_pre_topc(B_120,A_119)
      | ~ l1_pre_topc(A_119) ) ),
    inference(resolution,[status(thm)],[c_72,c_146])).

tff(c_357,plain,(
    ! [A_119] :
      ( k7_tmap_1(A_119,'#skF_4'('#skF_5','#skF_6')) = k6_partfun1(u1_struct_0(A_119))
      | ~ v2_pre_topc(A_119)
      | v2_struct_0(A_119)
      | ~ m1_pre_topc('#skF_6',A_119)
      | ~ l1_pre_topc(A_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_339])).

tff(c_133,plain,(
    ! [A_104,B_105] :
      ( v1_funct_1(k7_tmap_1(A_104,B_105))
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104)
      | ~ v2_pre_topc(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_555,plain,(
    ! [A_136,B_137] :
      ( v1_funct_1(k7_tmap_1(A_136,'#skF_4'(A_136,B_137)))
      | ~ v2_pre_topc(A_136)
      | v2_struct_0(A_136)
      | v1_tsep_1(B_137,A_136)
      | ~ m1_pre_topc(B_137,A_136)
      | ~ l1_pre_topc(A_136) ) ),
    inference(resolution,[status(thm)],[c_38,c_133])).

tff(c_559,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0('#skF_5')))
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | v1_tsep_1('#skF_6','#skF_5')
    | ~ m1_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_555])).

tff(c_561,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0('#skF_5')))
    | v1_tsep_1('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_78,c_76,c_74,c_78,c_559])).

tff(c_562,plain,(
    v1_funct_1(k6_partfun1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_174,c_561])).

tff(c_8,plain,(
    ! [A_3] :
      ( m1_subset_1('#skF_1'(A_3),k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2841,plain,
    ( m1_subset_1('#skF_1'(k8_tmap_1('#skF_5','#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc(k8_tmap_1('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2709,c_8])).

tff(c_2883,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_2841])).

tff(c_2886,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_2883])).

tff(c_2889,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_2886])).

tff(c_2891,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2889])).

tff(c_2892,plain,(
    m1_subset_1('#skF_1'(k8_tmap_1('#skF_5','#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_2841])).

tff(c_14,plain,(
    ! [A_11,B_13] :
      ( k7_tmap_1(A_11,B_13) = k6_partfun1(u1_struct_0(A_11))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2902,plain,
    ( k7_tmap_1('#skF_5','#skF_1'(k8_tmap_1('#skF_5','#skF_6'))) = k6_partfun1(u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_2892,c_14])).

tff(c_2916,plain,
    ( k7_tmap_1('#skF_5','#skF_1'(k8_tmap_1('#skF_5','#skF_6'))) = k6_partfun1(u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_2902])).

tff(c_2917,plain,(
    k7_tmap_1('#skF_5','#skF_1'(k8_tmap_1('#skF_5','#skF_6'))) = k6_partfun1(u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2916])).

tff(c_60,plain,(
    ! [A_74,B_76] :
      ( u1_struct_0(k6_tmap_1(A_74,B_76)) = u1_struct_0(A_74)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_2899,plain,
    ( u1_struct_0(k6_tmap_1('#skF_5','#skF_1'(k8_tmap_1('#skF_5','#skF_6')))) = u1_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_2892,c_60])).

tff(c_2912,plain,
    ( u1_struct_0(k6_tmap_1('#skF_5','#skF_1'(k8_tmap_1('#skF_5','#skF_6')))) = u1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_2899])).

tff(c_2913,plain,(
    u1_struct_0(k6_tmap_1('#skF_5','#skF_1'(k8_tmap_1('#skF_5','#skF_6')))) = u1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2912])).

tff(c_42,plain,(
    ! [A_68,B_69] :
      ( v1_funct_2(k7_tmap_1(A_68,B_69),u1_struct_0(A_68),u1_struct_0(k6_tmap_1(A_68,B_69)))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_3066,plain,
    ( v1_funct_2(k7_tmap_1('#skF_5','#skF_1'(k8_tmap_1('#skF_5','#skF_6'))),u1_struct_0('#skF_5'),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_1'(k8_tmap_1('#skF_5','#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2913,c_42])).

tff(c_3143,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_2892,c_2917,c_3066])).

tff(c_3144,plain,(
    v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_3143])).

tff(c_40,plain,(
    ! [A_68,B_69] :
      ( m1_subset_1(k7_tmap_1(A_68,B_69),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_68),u1_struct_0(k6_tmap_1(A_68,B_69)))))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_3057,plain,
    ( m1_subset_1(k7_tmap_1('#skF_5','#skF_1'(k8_tmap_1('#skF_5','#skF_6'))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5'))))
    | ~ m1_subset_1('#skF_1'(k8_tmap_1('#skF_5','#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2913,c_40])).

tff(c_3138,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5'))))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_2892,c_2917,c_3057])).

tff(c_3139,plain,(
    m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5')))) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_3138])).

tff(c_2922,plain,(
    ! [B_287,A_288,C_289] :
      ( u1_struct_0(B_287) = '#skF_3'(A_288,B_287,C_289)
      | k9_tmap_1(A_288,B_287) = C_289
      | ~ m1_subset_1(C_289,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_288),u1_struct_0(k8_tmap_1(A_288,B_287)))))
      | ~ v1_funct_2(C_289,u1_struct_0(A_288),u1_struct_0(k8_tmap_1(A_288,B_287)))
      | ~ v1_funct_1(C_289)
      | ~ m1_pre_topc(B_287,A_288)
      | ~ l1_pre_topc(A_288)
      | ~ v2_pre_topc(A_288)
      | v2_struct_0(A_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2928,plain,(
    ! [C_289] :
      ( u1_struct_0('#skF_6') = '#skF_3'('#skF_5','#skF_6',C_289)
      | k9_tmap_1('#skF_5','#skF_6') = C_289
      | ~ m1_subset_1(C_289,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5'))))
      | ~ v1_funct_2(C_289,u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5','#skF_6')))
      | ~ v1_funct_1(C_289)
      | ~ m1_pre_topc('#skF_6','#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2709,c_2922])).

tff(c_2962,plain,(
    ! [C_289] :
      ( '#skF_3'('#skF_5','#skF_6',C_289) = '#skF_4'('#skF_5','#skF_6')
      | k9_tmap_1('#skF_5','#skF_6') = C_289
      | ~ m1_subset_1(C_289,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5'))))
      | ~ v1_funct_2(C_289,u1_struct_0('#skF_5'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1(C_289)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_2709,c_180,c_2928])).

tff(c_9113,plain,(
    ! [C_443] :
      ( '#skF_3'('#skF_5','#skF_6',C_443) = '#skF_4'('#skF_5','#skF_6')
      | k9_tmap_1('#skF_5','#skF_6') = C_443
      | ~ m1_subset_1(C_443,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5'))))
      | ~ v1_funct_2(C_443,u1_struct_0('#skF_5'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1(C_443) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2962])).

tff(c_9123,plain,
    ( '#skF_3'('#skF_5','#skF_6',k6_partfun1(u1_struct_0('#skF_5'))) = '#skF_4'('#skF_5','#skF_6')
    | k6_partfun1(u1_struct_0('#skF_5')) = k9_tmap_1('#skF_5','#skF_6')
    | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1(k6_partfun1(u1_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_3139,c_9113])).

tff(c_9134,plain,
    ( '#skF_3'('#skF_5','#skF_6',k6_partfun1(u1_struct_0('#skF_5'))) = '#skF_4'('#skF_5','#skF_6')
    | k6_partfun1(u1_struct_0('#skF_5')) = k9_tmap_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_562,c_3144,c_9123])).

tff(c_9139,plain,(
    k6_partfun1(u1_struct_0('#skF_5')) = k9_tmap_1('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_9134])).

tff(c_157,plain,(
    ! [A_80,B_82] :
      ( k7_tmap_1(A_80,u1_struct_0(B_82)) = k6_partfun1(u1_struct_0(A_80))
      | ~ v2_pre_topc(A_80)
      | v2_struct_0(A_80)
      | ~ m1_pre_topc(B_82,A_80)
      | ~ l1_pre_topc(A_80) ) ),
    inference(resolution,[status(thm)],[c_72,c_146])).

tff(c_734,plain,(
    ! [A_150,B_151] :
      ( v1_funct_2(k7_tmap_1(A_150,B_151),u1_struct_0(A_150),u1_struct_0(k6_tmap_1(A_150,B_151)))
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ l1_pre_topc(A_150)
      | ~ v2_pre_topc(A_150)
      | v2_struct_0(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_10081,plain,(
    ! [A_452,B_453] :
      ( v1_funct_2(k6_partfun1(u1_struct_0(A_452)),u1_struct_0(A_452),u1_struct_0(k6_tmap_1(A_452,u1_struct_0(B_453))))
      | ~ m1_subset_1(u1_struct_0(B_453),k1_zfmisc_1(u1_struct_0(A_452)))
      | ~ l1_pre_topc(A_452)
      | ~ v2_pre_topc(A_452)
      | v2_struct_0(A_452)
      | ~ v2_pre_topc(A_452)
      | v2_struct_0(A_452)
      | ~ m1_pre_topc(B_453,A_452)
      | ~ l1_pre_topc(A_452) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_734])).

tff(c_10093,plain,(
    ! [B_453] :
      ( v1_funct_2(k9_tmap_1('#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0(k6_tmap_1('#skF_5',u1_struct_0(B_453))))
      | ~ m1_subset_1(u1_struct_0(B_453),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(B_453,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9139,c_10081])).

tff(c_10272,plain,(
    ! [B_453] :
      ( v1_funct_2(k9_tmap_1('#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0(k6_tmap_1('#skF_5',u1_struct_0(B_453))))
      | ~ m1_subset_1(u1_struct_0(B_453),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(B_453,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_78,c_78,c_76,c_10093])).

tff(c_10292,plain,(
    ! [B_454] :
      ( v1_funct_2(k9_tmap_1('#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0(k6_tmap_1('#skF_5',u1_struct_0(B_454))))
      | ~ m1_subset_1(u1_struct_0(B_454),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc(B_454,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_10272])).

tff(c_10364,plain,
    ( v1_funct_2(k9_tmap_1('#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0(k6_tmap_1('#skF_5','#skF_4'('#skF_5','#skF_6'))))
    | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_pre_topc('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_10292])).

tff(c_10379,plain,
    ( v1_funct_2(k9_tmap_1('#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0(k6_tmap_1('#skF_5','#skF_4'('#skF_5','#skF_6'))))
    | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_180,c_10364])).

tff(c_10425,plain,(
    ~ m1_subset_1('#skF_4'('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_10379])).

tff(c_10428,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_196,c_10425])).

tff(c_10435,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_10428])).

tff(c_10437,plain,(
    m1_subset_1('#skF_4'('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_10379])).

tff(c_10446,plain,
    ( k7_tmap_1('#skF_5','#skF_4'('#skF_5','#skF_6')) = k6_partfun1(u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_10437,c_14])).

tff(c_10460,plain,
    ( k7_tmap_1('#skF_5','#skF_4'('#skF_5','#skF_6')) = k9_tmap_1('#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_9139,c_10446])).

tff(c_10461,plain,(
    k7_tmap_1('#skF_5','#skF_4'('#skF_5','#skF_6')) = k9_tmap_1('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_10460])).

tff(c_66,plain,(
    ! [A_77,B_79] :
      ( v5_pre_topc(k7_tmap_1(A_77,B_79),A_77,k6_tmap_1(A_77,B_79))
      | ~ v3_pre_topc(B_79,A_77)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_10921,plain,
    ( v5_pre_topc(k9_tmap_1('#skF_5','#skF_6'),'#skF_5',k6_tmap_1('#skF_5','#skF_4'('#skF_5','#skF_6')))
    | ~ v3_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5')
    | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_10461,c_66])).

tff(c_10958,plain,
    ( v5_pre_topc(k9_tmap_1('#skF_5','#skF_6'),'#skF_5',k6_tmap_1('#skF_5','#skF_4'('#skF_5','#skF_6')))
    | ~ v3_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_10437,c_10921])).

tff(c_10959,plain,
    ( v5_pre_topc(k9_tmap_1('#skF_5','#skF_6'),'#skF_5',k6_tmap_1('#skF_5','#skF_4'('#skF_5','#skF_6')))
    | ~ v3_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_10958])).

tff(c_11106,plain,(
    ~ v3_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_10959])).

tff(c_3371,plain,(
    ! [B_296,A_297] :
      ( v3_pre_topc(B_296,A_297)
      | ~ m1_subset_1(k7_tmap_1(A_297,B_296),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_297),u1_struct_0(k6_tmap_1(A_297,B_296)))))
      | ~ v5_pre_topc(k7_tmap_1(A_297,B_296),A_297,k6_tmap_1(A_297,B_296))
      | ~ v1_funct_2(k7_tmap_1(A_297,B_296),u1_struct_0(A_297),u1_struct_0(k6_tmap_1(A_297,B_296)))
      | ~ v1_funct_1(k7_tmap_1(A_297,B_296))
      | ~ m1_subset_1(B_296,k1_zfmisc_1(u1_struct_0(A_297)))
      | ~ l1_pre_topc(A_297)
      | ~ v2_pre_topc(A_297)
      | v2_struct_0(A_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_4614,plain,(
    ! [B_324,A_325] :
      ( v3_pre_topc(B_324,A_325)
      | ~ v5_pre_topc(k7_tmap_1(A_325,B_324),A_325,k6_tmap_1(A_325,B_324))
      | ~ v1_funct_2(k7_tmap_1(A_325,B_324),u1_struct_0(A_325),u1_struct_0(k6_tmap_1(A_325,B_324)))
      | ~ v1_funct_1(k7_tmap_1(A_325,B_324))
      | ~ m1_subset_1(B_324,k1_zfmisc_1(u1_struct_0(A_325)))
      | ~ l1_pre_topc(A_325)
      | ~ v2_pre_topc(A_325)
      | v2_struct_0(A_325) ) ),
    inference(resolution,[status(thm)],[c_40,c_3371])).

tff(c_4735,plain,(
    ! [B_69,A_68] :
      ( v3_pre_topc(B_69,A_68)
      | ~ v5_pre_topc(k7_tmap_1(A_68,B_69),A_68,k6_tmap_1(A_68,B_69))
      | ~ v1_funct_1(k7_tmap_1(A_68,B_69))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68)
      | v2_struct_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_42,c_4614])).

tff(c_10909,plain,
    ( v3_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5')
    | ~ v5_pre_topc(k9_tmap_1('#skF_5','#skF_6'),'#skF_5',k6_tmap_1('#skF_5','#skF_4'('#skF_5','#skF_6')))
    | ~ v1_funct_1(k7_tmap_1('#skF_5','#skF_4'('#skF_5','#skF_6')))
    | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_10461,c_4735])).

tff(c_10946,plain,
    ( v3_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5')
    | ~ v5_pre_topc(k9_tmap_1('#skF_5','#skF_6'),'#skF_5',k6_tmap_1('#skF_5','#skF_4'('#skF_5','#skF_6')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_10437,c_120,c_10461,c_10909])).

tff(c_10947,plain,
    ( v3_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5')
    | ~ v5_pre_topc(k9_tmap_1('#skF_5','#skF_6'),'#skF_5',k6_tmap_1('#skF_5','#skF_4'('#skF_5','#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_10946])).

tff(c_11121,plain,(
    ~ v5_pre_topc(k9_tmap_1('#skF_5','#skF_6'),'#skF_5',k6_tmap_1('#skF_5','#skF_4'('#skF_5','#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_11106,c_10947])).

tff(c_11124,plain,
    ( ~ v5_pre_topc(k9_tmap_1('#skF_5','#skF_6'),'#skF_5',k8_tmap_1('#skF_5','#skF_6'))
    | ~ m1_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2622,c_11121])).

tff(c_11126,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_121,c_11124])).

tff(c_11128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_11126])).

tff(c_11130,plain,(
    v3_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_10959])).

tff(c_34,plain,(
    ! [A_58,B_64] :
      ( ~ v3_pre_topc('#skF_4'(A_58,B_64),A_58)
      | v1_tsep_1(B_64,A_58)
      | ~ m1_pre_topc(B_64,A_58)
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_11133,plain,
    ( v1_tsep_1('#skF_6','#skF_5')
    | ~ m1_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_11130,c_34])).

tff(c_11136,plain,(
    v1_tsep_1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_11133])).

tff(c_11138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_11136])).

tff(c_11140,plain,(
    k6_partfun1(u1_struct_0('#skF_5')) != k9_tmap_1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_9134])).

tff(c_2714,plain,(
    v1_funct_2(k9_tmap_1('#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2709,c_125])).

tff(c_2713,plain,(
    m1_subset_1(k9_tmap_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2709,c_129])).

tff(c_3935,plain,(
    ! [A_309,B_310] :
      ( r1_funct_2(u1_struct_0(A_309),u1_struct_0(k8_tmap_1(A_309,B_310)),u1_struct_0(A_309),u1_struct_0(k6_tmap_1(A_309,u1_struct_0(B_310))),k9_tmap_1(A_309,B_310),k7_tmap_1(A_309,u1_struct_0(B_310)))
      | ~ m1_subset_1(u1_struct_0(B_310),k1_zfmisc_1(u1_struct_0(A_309)))
      | ~ m1_subset_1(k9_tmap_1(A_309,B_310),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_309),u1_struct_0(k8_tmap_1(A_309,B_310)))))
      | ~ v1_funct_2(k9_tmap_1(A_309,B_310),u1_struct_0(A_309),u1_struct_0(k8_tmap_1(A_309,B_310)))
      | ~ v1_funct_1(k9_tmap_1(A_309,B_310))
      | ~ m1_pre_topc(B_310,A_309)
      | ~ l1_pre_topc(A_309)
      | ~ v2_pre_topc(A_309)
      | v2_struct_0(A_309) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_3970,plain,
    ( r1_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),u1_struct_0(k6_tmap_1('#skF_5',u1_struct_0('#skF_6'))),k9_tmap_1('#skF_5','#skF_6'),k7_tmap_1('#skF_5',u1_struct_0('#skF_6')))
    | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1(k9_tmap_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5','#skF_6')))))
    | ~ v1_funct_2(k9_tmap_1('#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5','#skF_6')))
    | ~ v1_funct_1(k9_tmap_1('#skF_5','#skF_6'))
    | ~ m1_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2709,c_3935])).

tff(c_4108,plain,
    ( r1_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),u1_struct_0(k6_tmap_1('#skF_5','#skF_4'('#skF_5','#skF_6'))),k9_tmap_1('#skF_5','#skF_6'),k7_tmap_1('#skF_5','#skF_4'('#skF_5','#skF_6')))
    | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_120,c_2714,c_2709,c_2713,c_2709,c_180,c_180,c_180,c_3970])).

tff(c_4109,plain,
    ( r1_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),u1_struct_0(k6_tmap_1('#skF_5','#skF_4'('#skF_5','#skF_6'))),k9_tmap_1('#skF_5','#skF_6'),k7_tmap_1('#skF_5','#skF_4'('#skF_5','#skF_6')))
    | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_4108])).

tff(c_12750,plain,(
    ~ m1_subset_1('#skF_4'('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_4109])).

tff(c_12753,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_196,c_12750])).

tff(c_12760,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_12753])).

tff(c_12762,plain,(
    m1_subset_1('#skF_4'('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_4109])).

tff(c_12768,plain,
    ( u1_struct_0(k6_tmap_1('#skF_5','#skF_4'('#skF_5','#skF_6'))) = u1_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_12762,c_60])).

tff(c_12781,plain,
    ( u1_struct_0(k6_tmap_1('#skF_5','#skF_4'('#skF_5','#skF_6'))) = u1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_12768])).

tff(c_12782,plain,(
    u1_struct_0(k6_tmap_1('#skF_5','#skF_4'('#skF_5','#skF_6'))) = u1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_12781])).

tff(c_12771,plain,
    ( k7_tmap_1('#skF_5','#skF_4'('#skF_5','#skF_6')) = k6_partfun1(u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_12762,c_14])).

tff(c_12785,plain,
    ( k7_tmap_1('#skF_5','#skF_4'('#skF_5','#skF_6')) = k6_partfun1(u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_12771])).

tff(c_12786,plain,(
    k7_tmap_1('#skF_5','#skF_4'('#skF_5','#skF_6')) = k6_partfun1(u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_12785])).

tff(c_12761,plain,(
    r1_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),u1_struct_0(k6_tmap_1('#skF_5','#skF_4'('#skF_5','#skF_6'))),k9_tmap_1('#skF_5','#skF_6'),k7_tmap_1('#skF_5','#skF_4'('#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_4109])).

tff(c_14690,plain,(
    r1_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),k9_tmap_1('#skF_5','#skF_6'),k6_partfun1(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12782,c_12786,c_12761])).

tff(c_12,plain,(
    ! [B_6,C_7,E_9,D_8,A_5,F_10] :
      ( F_10 = E_9
      | ~ r1_funct_2(A_5,B_6,C_7,D_8,E_9,F_10)
      | ~ m1_subset_1(F_10,k1_zfmisc_1(k2_zfmisc_1(C_7,D_8)))
      | ~ v1_funct_2(F_10,C_7,D_8)
      | ~ v1_funct_1(F_10)
      | ~ m1_subset_1(E_9,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6)))
      | ~ v1_funct_2(E_9,A_5,B_6)
      | ~ v1_funct_1(E_9)
      | v1_xboole_0(D_8)
      | v1_xboole_0(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_14692,plain,
    ( k6_partfun1(u1_struct_0('#skF_5')) = k9_tmap_1('#skF_5','#skF_6')
    | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5'))))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1(k6_partfun1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1(k9_tmap_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5'))))
    | ~ v1_funct_2(k9_tmap_1('#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1(k9_tmap_1('#skF_5','#skF_6'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_14690,c_12])).

tff(c_14695,plain,
    ( k6_partfun1(u1_struct_0('#skF_5')) = k9_tmap_1('#skF_5','#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_2714,c_2713,c_562,c_3144,c_3139,c_14692])).

tff(c_14697,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2712,c_11140,c_14695])).

tff(c_14699,plain,(
    ~ m1_subset_1(k9_tmap_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5','#skF_6'))))) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_15068,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_15065,c_14699])).

tff(c_15080,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_15068])).

tff(c_15082,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_15080])).

tff(c_15084,plain,(
    ~ v1_funct_2(k9_tmap_1('#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_15309,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_15306,c_15084])).

tff(c_15318,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_15309])).

tff(c_15320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_15318])).

tff(c_15321,plain,(
    v1_tsep_1('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_15488,plain,(
    ! [B_653,A_654] :
      ( v3_pre_topc(u1_struct_0(B_653),A_654)
      | ~ m1_subset_1(u1_struct_0(B_653),k1_zfmisc_1(u1_struct_0(A_654)))
      | ~ v1_tsep_1(B_653,A_654)
      | ~ m1_pre_topc(B_653,A_654)
      | ~ l1_pre_topc(A_654) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_15504,plain,(
    ! [B_82,A_80] :
      ( v3_pre_topc(u1_struct_0(B_82),A_80)
      | ~ v1_tsep_1(B_82,A_80)
      | ~ m1_pre_topc(B_82,A_80)
      | ~ l1_pre_topc(A_80) ) ),
    inference(resolution,[status(thm)],[c_72,c_15488])).

tff(c_15397,plain,(
    ! [A_646,B_647] :
      ( k7_tmap_1(A_646,B_647) = k6_partfun1(u1_struct_0(A_646))
      | ~ m1_subset_1(B_647,k1_zfmisc_1(u1_struct_0(A_646)))
      | ~ l1_pre_topc(A_646)
      | ~ v2_pre_topc(A_646)
      | v2_struct_0(A_646) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_15411,plain,(
    ! [A_80,B_82] :
      ( k7_tmap_1(A_80,u1_struct_0(B_82)) = k6_partfun1(u1_struct_0(A_80))
      | ~ v2_pre_topc(A_80)
      | v2_struct_0(A_80)
      | ~ m1_pre_topc(B_82,A_80)
      | ~ l1_pre_topc(A_80) ) ),
    inference(resolution,[status(thm)],[c_72,c_15397])).

tff(c_15351,plain,(
    ! [A_643,B_644] :
      ( u1_struct_0(k6_tmap_1(A_643,B_644)) = u1_struct_0(A_643)
      | ~ m1_subset_1(B_644,k1_zfmisc_1(u1_struct_0(A_643)))
      | ~ l1_pre_topc(A_643)
      | ~ v2_pre_topc(A_643)
      | v2_struct_0(A_643) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_15362,plain,(
    ! [A_80,B_82] :
      ( u1_struct_0(k6_tmap_1(A_80,u1_struct_0(B_82))) = u1_struct_0(A_80)
      | ~ v2_pre_topc(A_80)
      | v2_struct_0(A_80)
      | ~ m1_pre_topc(B_82,A_80)
      | ~ l1_pre_topc(A_80) ) ),
    inference(resolution,[status(thm)],[c_72,c_15351])).

tff(c_15678,plain,(
    ! [A_678,B_679] :
      ( v1_funct_2(k7_tmap_1(A_678,B_679),u1_struct_0(A_678),u1_struct_0(k6_tmap_1(A_678,B_679)))
      | ~ m1_subset_1(B_679,k1_zfmisc_1(u1_struct_0(A_678)))
      | ~ l1_pre_topc(A_678)
      | ~ v2_pre_topc(A_678)
      | v2_struct_0(A_678) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_17334,plain,(
    ! [A_814,B_815] :
      ( v1_funct_2(k7_tmap_1(A_814,u1_struct_0(B_815)),u1_struct_0(A_814),u1_struct_0(A_814))
      | ~ m1_subset_1(u1_struct_0(B_815),k1_zfmisc_1(u1_struct_0(A_814)))
      | ~ l1_pre_topc(A_814)
      | ~ v2_pre_topc(A_814)
      | v2_struct_0(A_814)
      | ~ v2_pre_topc(A_814)
      | v2_struct_0(A_814)
      | ~ m1_pre_topc(B_815,A_814)
      | ~ l1_pre_topc(A_814) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15362,c_15678])).

tff(c_25282,plain,(
    ! [A_1164,B_1165] :
      ( v1_funct_2(k6_partfun1(u1_struct_0(A_1164)),u1_struct_0(A_1164),u1_struct_0(A_1164))
      | ~ m1_subset_1(u1_struct_0(B_1165),k1_zfmisc_1(u1_struct_0(A_1164)))
      | ~ l1_pre_topc(A_1164)
      | ~ v2_pre_topc(A_1164)
      | v2_struct_0(A_1164)
      | ~ v2_pre_topc(A_1164)
      | v2_struct_0(A_1164)
      | ~ m1_pre_topc(B_1165,A_1164)
      | ~ l1_pre_topc(A_1164)
      | ~ v2_pre_topc(A_1164)
      | v2_struct_0(A_1164)
      | ~ m1_pre_topc(B_1165,A_1164)
      | ~ l1_pre_topc(A_1164) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15411,c_17334])).

tff(c_25358,plain,(
    ! [A_1166,B_1167] :
      ( v1_funct_2(k6_partfun1(u1_struct_0(A_1166)),u1_struct_0(A_1166),u1_struct_0(A_1166))
      | ~ v2_pre_topc(A_1166)
      | v2_struct_0(A_1166)
      | ~ m1_pre_topc(B_1167,A_1166)
      | ~ l1_pre_topc(A_1166) ) ),
    inference(resolution,[status(thm)],[c_72,c_25282])).

tff(c_25360,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_5'))
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_25358])).

tff(c_25363,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_78,c_25360])).

tff(c_25364,plain,(
    v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_25363])).

tff(c_16201,plain,(
    ! [A_741,B_742] :
      ( k6_tmap_1(A_741,u1_struct_0(B_742)) = k8_tmap_1(A_741,B_742)
      | ~ m1_subset_1(u1_struct_0(B_742),k1_zfmisc_1(u1_struct_0(A_741)))
      | ~ l1_pre_topc(k8_tmap_1(A_741,B_742))
      | ~ v2_pre_topc(k8_tmap_1(A_741,B_742))
      | ~ v1_pre_topc(k8_tmap_1(A_741,B_742))
      | ~ m1_pre_topc(B_742,A_741)
      | ~ l1_pre_topc(A_741)
      | ~ v2_pre_topc(A_741)
      | v2_struct_0(A_741) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_16399,plain,(
    ! [A_758,B_759] :
      ( k6_tmap_1(A_758,u1_struct_0(B_759)) = k8_tmap_1(A_758,B_759)
      | ~ l1_pre_topc(k8_tmap_1(A_758,B_759))
      | ~ v2_pre_topc(k8_tmap_1(A_758,B_759))
      | ~ v1_pre_topc(k8_tmap_1(A_758,B_759))
      | ~ v2_pre_topc(A_758)
      | v2_struct_0(A_758)
      | ~ m1_pre_topc(B_759,A_758)
      | ~ l1_pre_topc(A_758) ) ),
    inference(resolution,[status(thm)],[c_72,c_16201])).

tff(c_16404,plain,(
    ! [A_760,B_761] :
      ( k6_tmap_1(A_760,u1_struct_0(B_761)) = k8_tmap_1(A_760,B_761)
      | ~ l1_pre_topc(k8_tmap_1(A_760,B_761))
      | ~ v1_pre_topc(k8_tmap_1(A_760,B_761))
      | ~ m1_pre_topc(B_761,A_760)
      | ~ l1_pre_topc(A_760)
      | ~ v2_pre_topc(A_760)
      | v2_struct_0(A_760) ) ),
    inference(resolution,[status(thm)],[c_48,c_16399])).

tff(c_16409,plain,(
    ! [A_762,B_763] :
      ( k6_tmap_1(A_762,u1_struct_0(B_763)) = k8_tmap_1(A_762,B_763)
      | ~ l1_pre_topc(k8_tmap_1(A_762,B_763))
      | ~ m1_pre_topc(B_763,A_762)
      | ~ l1_pre_topc(A_762)
      | ~ v2_pre_topc(A_762)
      | v2_struct_0(A_762) ) ),
    inference(resolution,[status(thm)],[c_50,c_16404])).

tff(c_16414,plain,(
    ! [A_764,B_765] :
      ( k6_tmap_1(A_764,u1_struct_0(B_765)) = k8_tmap_1(A_764,B_765)
      | ~ m1_pre_topc(B_765,A_764)
      | ~ l1_pre_topc(A_764)
      | ~ v2_pre_topc(A_764)
      | v2_struct_0(A_764) ) ),
    inference(resolution,[status(thm)],[c_46,c_16409])).

tff(c_16457,plain,(
    ! [A_764,B_765] :
      ( u1_struct_0(k8_tmap_1(A_764,B_765)) = u1_struct_0(A_764)
      | ~ v2_pre_topc(A_764)
      | v2_struct_0(A_764)
      | ~ m1_pre_topc(B_765,A_764)
      | ~ l1_pre_topc(A_764)
      | ~ m1_pre_topc(B_765,A_764)
      | ~ l1_pre_topc(A_764)
      | ~ v2_pre_topc(A_764)
      | v2_struct_0(A_764) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16414,c_15362])).

tff(c_15816,plain,(
    ! [A_686,B_687] :
      ( m1_subset_1(k7_tmap_1(A_686,B_687),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_686),u1_struct_0(k6_tmap_1(A_686,B_687)))))
      | ~ m1_subset_1(B_687,k1_zfmisc_1(u1_struct_0(A_686)))
      | ~ l1_pre_topc(A_686)
      | ~ v2_pre_topc(A_686)
      | v2_struct_0(A_686) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_18515,plain,(
    ! [A_891,B_892] :
      ( m1_subset_1(k7_tmap_1(A_891,u1_struct_0(B_892)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_891),u1_struct_0(A_891))))
      | ~ m1_subset_1(u1_struct_0(B_892),k1_zfmisc_1(u1_struct_0(A_891)))
      | ~ l1_pre_topc(A_891)
      | ~ v2_pre_topc(A_891)
      | v2_struct_0(A_891)
      | ~ v2_pre_topc(A_891)
      | v2_struct_0(A_891)
      | ~ m1_pre_topc(B_892,A_891)
      | ~ l1_pre_topc(A_891) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15362,c_15816])).

tff(c_26963,plain,(
    ! [A_1263,B_1264] :
      ( m1_subset_1(k6_partfun1(u1_struct_0(A_1263)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1263),u1_struct_0(A_1263))))
      | ~ m1_subset_1(u1_struct_0(B_1264),k1_zfmisc_1(u1_struct_0(A_1263)))
      | ~ l1_pre_topc(A_1263)
      | ~ v2_pre_topc(A_1263)
      | v2_struct_0(A_1263)
      | ~ v2_pre_topc(A_1263)
      | v2_struct_0(A_1263)
      | ~ m1_pre_topc(B_1264,A_1263)
      | ~ l1_pre_topc(A_1263)
      | ~ v2_pre_topc(A_1263)
      | v2_struct_0(A_1263)
      | ~ m1_pre_topc(B_1264,A_1263)
      | ~ l1_pre_topc(A_1263) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15411,c_18515])).

tff(c_27843,plain,(
    ! [A_1268,B_1269] :
      ( m1_subset_1(k6_partfun1(u1_struct_0(A_1268)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1268),u1_struct_0(A_1268))))
      | ~ v2_pre_topc(A_1268)
      | v2_struct_0(A_1268)
      | ~ m1_pre_topc(B_1269,A_1268)
      | ~ l1_pre_topc(A_1268) ) ),
    inference(resolution,[status(thm)],[c_72,c_26963])).

tff(c_27845,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5'))))
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_27843])).

tff(c_27848,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5'))))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_78,c_27845])).

tff(c_27849,plain,(
    m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5')))) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_27848])).

tff(c_15413,plain,(
    ! [A_648] :
      ( k7_tmap_1(A_648,'#skF_1'(A_648)) = k6_partfun1(u1_struct_0(A_648))
      | ~ v2_pre_topc(A_648)
      | v2_struct_0(A_648)
      | ~ l1_pre_topc(A_648) ) ),
    inference(resolution,[status(thm)],[c_8,c_15397])).

tff(c_15336,plain,(
    ! [A_638,B_639] :
      ( v1_funct_1(k7_tmap_1(A_638,B_639))
      | ~ m1_subset_1(B_639,k1_zfmisc_1(u1_struct_0(A_638)))
      | ~ l1_pre_topc(A_638)
      | ~ v2_pre_topc(A_638)
      | v2_struct_0(A_638) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_15348,plain,(
    ! [A_3] :
      ( v1_funct_1(k7_tmap_1(A_3,'#skF_1'(A_3)))
      | ~ v2_pre_topc(A_3)
      | v2_struct_0(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(resolution,[status(thm)],[c_8,c_15336])).

tff(c_15419,plain,(
    ! [A_648] :
      ( v1_funct_1(k6_partfun1(u1_struct_0(A_648)))
      | ~ v2_pre_topc(A_648)
      | v2_struct_0(A_648)
      | ~ l1_pre_topc(A_648)
      | ~ v2_pre_topc(A_648)
      | v2_struct_0(A_648)
      | ~ l1_pre_topc(A_648) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15413,c_15348])).

tff(c_10,plain,(
    ! [B_6,C_7,D_8,A_5,F_10] :
      ( r1_funct_2(A_5,B_6,C_7,D_8,F_10,F_10)
      | ~ m1_subset_1(F_10,k1_zfmisc_1(k2_zfmisc_1(C_7,D_8)))
      | ~ v1_funct_2(F_10,C_7,D_8)
      | ~ m1_subset_1(F_10,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6)))
      | ~ v1_funct_2(F_10,A_5,B_6)
      | ~ v1_funct_1(F_10)
      | v1_xboole_0(D_8)
      | v1_xboole_0(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_27851,plain,(
    ! [A_5,B_6] :
      ( r1_funct_2(A_5,B_6,u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),k6_partfun1(u1_struct_0('#skF_5')),k6_partfun1(u1_struct_0('#skF_5')))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(A_5,B_6)))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')),A_5,B_6)
      | ~ v1_funct_1(k6_partfun1(u1_struct_0('#skF_5')))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | v1_xboole_0(B_6) ) ),
    inference(resolution,[status(thm)],[c_27849,c_10])).

tff(c_27854,plain,(
    ! [A_5,B_6] :
      ( r1_funct_2(A_5,B_6,u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),k6_partfun1(u1_struct_0('#skF_5')),k6_partfun1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(A_5,B_6)))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')),A_5,B_6)
      | ~ v1_funct_1(k6_partfun1(u1_struct_0('#skF_5')))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | v1_xboole_0(B_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25364,c_27851])).

tff(c_27855,plain,(
    ~ v1_funct_1(k6_partfun1(u1_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_27854])).

tff(c_27858,plain,
    ( ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_15419,c_27855])).

tff(c_27861,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_78,c_27858])).

tff(c_27863,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_27861])).

tff(c_27864,plain,(
    ! [A_5,B_6] :
      ( v1_xboole_0(u1_struct_0('#skF_5'))
      | r1_funct_2(A_5,B_6,u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),k6_partfun1(u1_struct_0('#skF_5')),k6_partfun1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(A_5,B_6)))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')),A_5,B_6)
      | v1_xboole_0(B_6) ) ),
    inference(splitRight,[status(thm)],[c_27854])).

tff(c_27866,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_27864])).

tff(c_27869,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_27866,c_4])).

tff(c_27872,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_27869])).

tff(c_27875,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_27872])).

tff(c_27879,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_27875])).

tff(c_27881,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_27864])).

tff(c_27880,plain,(
    ! [A_5,B_6] :
      ( r1_funct_2(A_5,B_6,u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),k6_partfun1(u1_struct_0('#skF_5')),k6_partfun1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(A_5,B_6)))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')),A_5,B_6)
      | v1_xboole_0(B_6) ) ),
    inference(splitRight,[status(thm)],[c_27864])).

tff(c_16413,plain,(
    ! [A_70,B_71] :
      ( k6_tmap_1(A_70,u1_struct_0(B_71)) = k8_tmap_1(A_70,B_71)
      | ~ m1_pre_topc(B_71,A_70)
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70)
      | v2_struct_0(A_70) ) ),
    inference(resolution,[status(thm)],[c_46,c_16409])).

tff(c_18417,plain,(
    ! [A_886,B_887] :
      ( v1_funct_2(k6_partfun1(u1_struct_0(A_886)),u1_struct_0(A_886),u1_struct_0(k6_tmap_1(A_886,u1_struct_0(B_887))))
      | ~ m1_subset_1(u1_struct_0(B_887),k1_zfmisc_1(u1_struct_0(A_886)))
      | ~ l1_pre_topc(A_886)
      | ~ v2_pre_topc(A_886)
      | v2_struct_0(A_886)
      | ~ v2_pre_topc(A_886)
      | v2_struct_0(A_886)
      | ~ m1_pre_topc(B_887,A_886)
      | ~ l1_pre_topc(A_886) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15411,c_15678])).

tff(c_18456,plain,(
    ! [A_70,B_71] :
      ( v1_funct_2(k6_partfun1(u1_struct_0(A_70)),u1_struct_0(A_70),u1_struct_0(k8_tmap_1(A_70,B_71)))
      | ~ m1_subset_1(u1_struct_0(B_71),k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70)
      | v2_struct_0(A_70)
      | ~ v2_pre_topc(A_70)
      | v2_struct_0(A_70)
      | ~ m1_pre_topc(B_71,A_70)
      | ~ l1_pre_topc(A_70)
      | ~ m1_pre_topc(B_71,A_70)
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70)
      | v2_struct_0(A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16413,c_18417])).

tff(c_19938,plain,(
    ! [A_953,B_954] :
      ( m1_subset_1(k6_partfun1(u1_struct_0(A_953)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_953),u1_struct_0(k6_tmap_1(A_953,u1_struct_0(B_954))))))
      | ~ m1_subset_1(u1_struct_0(B_954),k1_zfmisc_1(u1_struct_0(A_953)))
      | ~ l1_pre_topc(A_953)
      | ~ v2_pre_topc(A_953)
      | v2_struct_0(A_953)
      | ~ v2_pre_topc(A_953)
      | v2_struct_0(A_953)
      | ~ m1_pre_topc(B_954,A_953)
      | ~ l1_pre_topc(A_953) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15411,c_15816])).

tff(c_33636,plain,(
    ! [A_1464,B_1465] :
      ( m1_subset_1(k6_partfun1(u1_struct_0(A_1464)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1464),u1_struct_0(k8_tmap_1(A_1464,B_1465)))))
      | ~ m1_subset_1(u1_struct_0(B_1465),k1_zfmisc_1(u1_struct_0(A_1464)))
      | ~ l1_pre_topc(A_1464)
      | ~ v2_pre_topc(A_1464)
      | v2_struct_0(A_1464)
      | ~ v2_pre_topc(A_1464)
      | v2_struct_0(A_1464)
      | ~ m1_pre_topc(B_1465,A_1464)
      | ~ l1_pre_topc(A_1464)
      | ~ m1_pre_topc(B_1465,A_1464)
      | ~ l1_pre_topc(A_1464)
      | ~ v2_pre_topc(A_1464)
      | v2_struct_0(A_1464) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16413,c_19938])).

tff(c_28,plain,(
    ! [B_48,A_36,C_54] :
      ( u1_struct_0(B_48) = '#skF_3'(A_36,B_48,C_54)
      | k9_tmap_1(A_36,B_48) = C_54
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_36),u1_struct_0(k8_tmap_1(A_36,B_48)))))
      | ~ v1_funct_2(C_54,u1_struct_0(A_36),u1_struct_0(k8_tmap_1(A_36,B_48)))
      | ~ v1_funct_1(C_54)
      | ~ m1_pre_topc(B_48,A_36)
      | ~ l1_pre_topc(A_36)
      | ~ v2_pre_topc(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_37085,plain,(
    ! [A_1566,B_1567] :
      ( '#skF_3'(A_1566,B_1567,k6_partfun1(u1_struct_0(A_1566))) = u1_struct_0(B_1567)
      | k9_tmap_1(A_1566,B_1567) = k6_partfun1(u1_struct_0(A_1566))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0(A_1566)),u1_struct_0(A_1566),u1_struct_0(k8_tmap_1(A_1566,B_1567)))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0(A_1566)))
      | ~ m1_subset_1(u1_struct_0(B_1567),k1_zfmisc_1(u1_struct_0(A_1566)))
      | ~ m1_pre_topc(B_1567,A_1566)
      | ~ l1_pre_topc(A_1566)
      | ~ v2_pre_topc(A_1566)
      | v2_struct_0(A_1566) ) ),
    inference(resolution,[status(thm)],[c_33636,c_28])).

tff(c_37234,plain,(
    ! [A_1568,B_1569] :
      ( '#skF_3'(A_1568,B_1569,k6_partfun1(u1_struct_0(A_1568))) = u1_struct_0(B_1569)
      | k9_tmap_1(A_1568,B_1569) = k6_partfun1(u1_struct_0(A_1568))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0(A_1568)))
      | ~ m1_subset_1(u1_struct_0(B_1569),k1_zfmisc_1(u1_struct_0(A_1568)))
      | ~ m1_pre_topc(B_1569,A_1568)
      | ~ l1_pre_topc(A_1568)
      | ~ v2_pre_topc(A_1568)
      | v2_struct_0(A_1568) ) ),
    inference(resolution,[status(thm)],[c_18456,c_37085])).

tff(c_37330,plain,(
    ! [A_1570,B_1571] :
      ( '#skF_3'(A_1570,B_1571,k6_partfun1(u1_struct_0(A_1570))) = u1_struct_0(B_1571)
      | k9_tmap_1(A_1570,B_1571) = k6_partfun1(u1_struct_0(A_1570))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0(A_1570)))
      | ~ v2_pre_topc(A_1570)
      | v2_struct_0(A_1570)
      | ~ m1_pre_topc(B_1571,A_1570)
      | ~ l1_pre_topc(A_1570) ) ),
    inference(resolution,[status(thm)],[c_72,c_37234])).

tff(c_37515,plain,(
    ! [A_1574,B_1575] :
      ( '#skF_3'(A_1574,B_1575,k6_partfun1(u1_struct_0(A_1574))) = u1_struct_0(B_1575)
      | k9_tmap_1(A_1574,B_1575) = k6_partfun1(u1_struct_0(A_1574))
      | ~ m1_pre_topc(B_1575,A_1574)
      | ~ v2_pre_topc(A_1574)
      | v2_struct_0(A_1574)
      | ~ l1_pre_topc(A_1574) ) ),
    inference(resolution,[status(thm)],[c_15419,c_37330])).

tff(c_27865,plain,(
    v1_funct_1(k6_partfun1(u1_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_27854])).

tff(c_37340,plain,(
    ! [B_1571] :
      ( '#skF_3'('#skF_5',B_1571,k6_partfun1(u1_struct_0('#skF_5'))) = u1_struct_0(B_1571)
      | k9_tmap_1('#skF_5',B_1571) = k6_partfun1(u1_struct_0('#skF_5'))
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(B_1571,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_27865,c_37330])).

tff(c_37383,plain,(
    ! [B_1571] :
      ( '#skF_3'('#skF_5',B_1571,k6_partfun1(u1_struct_0('#skF_5'))) = u1_struct_0(B_1571)
      | k9_tmap_1('#skF_5',B_1571) = k6_partfun1(u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(B_1571,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_78,c_37340])).

tff(c_37386,plain,(
    ! [B_1572] :
      ( '#skF_3'('#skF_5',B_1572,k6_partfun1(u1_struct_0('#skF_5'))) = u1_struct_0(B_1572)
      | k9_tmap_1('#skF_5',B_1572) = k6_partfun1(u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_1572,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_37383])).

tff(c_26,plain,(
    ! [A_36,B_48,C_54] :
      ( ~ r1_funct_2(u1_struct_0(A_36),u1_struct_0(k8_tmap_1(A_36,B_48)),u1_struct_0(A_36),u1_struct_0(k6_tmap_1(A_36,'#skF_3'(A_36,B_48,C_54))),C_54,k7_tmap_1(A_36,'#skF_3'(A_36,B_48,C_54)))
      | k9_tmap_1(A_36,B_48) = C_54
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_36),u1_struct_0(k8_tmap_1(A_36,B_48)))))
      | ~ v1_funct_2(C_54,u1_struct_0(A_36),u1_struct_0(k8_tmap_1(A_36,B_48)))
      | ~ v1_funct_1(C_54)
      | ~ m1_pre_topc(B_48,A_36)
      | ~ l1_pre_topc(A_36)
      | ~ v2_pre_topc(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_37392,plain,(
    ! [B_1572] :
      ( ~ r1_funct_2(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_1572)),u1_struct_0('#skF_5'),u1_struct_0(k6_tmap_1('#skF_5',u1_struct_0(B_1572))),k6_partfun1(u1_struct_0('#skF_5')),k7_tmap_1('#skF_5','#skF_3'('#skF_5',B_1572,k6_partfun1(u1_struct_0('#skF_5')))))
      | k9_tmap_1('#skF_5',B_1572) = k6_partfun1(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_1572)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_1572)))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc(B_1572,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | k9_tmap_1('#skF_5',B_1572) = k6_partfun1(u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_1572,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37386,c_26])).

tff(c_37401,plain,(
    ! [B_1572] :
      ( ~ r1_funct_2(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_1572)),u1_struct_0('#skF_5'),u1_struct_0(k6_tmap_1('#skF_5',u1_struct_0(B_1572))),k6_partfun1(u1_struct_0('#skF_5')),k7_tmap_1('#skF_5','#skF_3'('#skF_5',B_1572,k6_partfun1(u1_struct_0('#skF_5')))))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_1572)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_1572)))
      | v2_struct_0('#skF_5')
      | k9_tmap_1('#skF_5',B_1572) = k6_partfun1(u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_1572,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_27865,c_37392])).

tff(c_37402,plain,(
    ! [B_1572] :
      ( ~ r1_funct_2(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_1572)),u1_struct_0('#skF_5'),u1_struct_0(k6_tmap_1('#skF_5',u1_struct_0(B_1572))),k6_partfun1(u1_struct_0('#skF_5')),k7_tmap_1('#skF_5','#skF_3'('#skF_5',B_1572,k6_partfun1(u1_struct_0('#skF_5')))))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_1572)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_1572)))
      | k9_tmap_1('#skF_5',B_1572) = k6_partfun1(u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_1572,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_37401])).

tff(c_37522,plain,(
    ! [B_1575] :
      ( ~ r1_funct_2(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_1575)),u1_struct_0('#skF_5'),u1_struct_0(k6_tmap_1('#skF_5',u1_struct_0(B_1575))),k6_partfun1(u1_struct_0('#skF_5')),k7_tmap_1('#skF_5',u1_struct_0(B_1575)))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_1575)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_1575)))
      | k9_tmap_1('#skF_5',B_1575) = k6_partfun1(u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_1575,'#skF_5')
      | k9_tmap_1('#skF_5',B_1575) = k6_partfun1(u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_1575,'#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37515,c_37402])).

tff(c_37610,plain,(
    ! [B_1575] :
      ( ~ r1_funct_2(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_1575)),u1_struct_0('#skF_5'),u1_struct_0(k6_tmap_1('#skF_5',u1_struct_0(B_1575))),k6_partfun1(u1_struct_0('#skF_5')),k7_tmap_1('#skF_5',u1_struct_0(B_1575)))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_1575)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_1575)))
      | k9_tmap_1('#skF_5',B_1575) = k6_partfun1(u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_1575,'#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_78,c_37522])).

tff(c_38329,plain,(
    ! [B_1594] :
      ( ~ r1_funct_2(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_1594)),u1_struct_0('#skF_5'),u1_struct_0(k6_tmap_1('#skF_5',u1_struct_0(B_1594))),k6_partfun1(u1_struct_0('#skF_5')),k7_tmap_1('#skF_5',u1_struct_0(B_1594)))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_1594)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_1594)))
      | k9_tmap_1('#skF_5',B_1594) = k6_partfun1(u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_1594,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_37610])).

tff(c_38486,plain,(
    ! [B_82] :
      ( ~ r1_funct_2(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_82)),u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),k6_partfun1(u1_struct_0('#skF_5')),k7_tmap_1('#skF_5',u1_struct_0(B_82)))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_82)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_82)))
      | k9_tmap_1('#skF_5',B_82) = k6_partfun1(u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_82,'#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(B_82,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15362,c_38329])).

tff(c_38515,plain,(
    ! [B_82] :
      ( ~ r1_funct_2(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_82)),u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),k6_partfun1(u1_struct_0('#skF_5')),k7_tmap_1('#skF_5',u1_struct_0(B_82)))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_82)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_82)))
      | k9_tmap_1('#skF_5',B_82) = k6_partfun1(u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(B_82,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_78,c_38486])).

tff(c_38822,plain,(
    ! [B_1624] :
      ( ~ r1_funct_2(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_1624)),u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),k6_partfun1(u1_struct_0('#skF_5')),k7_tmap_1('#skF_5',u1_struct_0(B_1624)))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_1624)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_1624)))
      | k9_tmap_1('#skF_5',B_1624) = k6_partfun1(u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_1624,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_38515])).

tff(c_38882,plain,(
    ! [B_765] :
      ( ~ r1_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),k6_partfun1(u1_struct_0('#skF_5')),k7_tmap_1('#skF_5',u1_struct_0(B_765)))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_765)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_765)))
      | k9_tmap_1('#skF_5',B_765) = k6_partfun1(u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_765,'#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(B_765,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ m1_pre_topc(B_765,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16457,c_38822])).

tff(c_38915,plain,(
    ! [B_765] :
      ( ~ r1_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),k6_partfun1(u1_struct_0('#skF_5')),k7_tmap_1('#skF_5',u1_struct_0(B_765)))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_765)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_765)))
      | k9_tmap_1('#skF_5',B_765) = k6_partfun1(u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_765,'#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_76,c_78,c_38882])).

tff(c_40231,plain,(
    ! [B_1651] :
      ( ~ r1_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),k6_partfun1(u1_struct_0('#skF_5')),k7_tmap_1('#skF_5',u1_struct_0(B_1651)))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_1651)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_1651)))
      | k9_tmap_1('#skF_5',B_1651) = k6_partfun1(u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_1651,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_38915])).

tff(c_40301,plain,(
    ! [B_82] :
      ( ~ r1_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),k6_partfun1(u1_struct_0('#skF_5')),k6_partfun1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_82)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_82)))
      | k9_tmap_1('#skF_5',B_82) = k6_partfun1(u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_82,'#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(B_82,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15411,c_40231])).

tff(c_40309,plain,(
    ! [B_82] :
      ( ~ r1_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),k6_partfun1(u1_struct_0('#skF_5')),k6_partfun1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_82)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_82)))
      | k9_tmap_1('#skF_5',B_82) = k6_partfun1(u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(B_82,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_78,c_40301])).

tff(c_40310,plain,(
    ! [B_82] :
      ( ~ r1_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),k6_partfun1(u1_struct_0('#skF_5')),k6_partfun1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_82)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_82)))
      | k9_tmap_1('#skF_5',B_82) = k6_partfun1(u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_82,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_40309])).

tff(c_40847,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_5'),k6_partfun1(u1_struct_0('#skF_5')),k6_partfun1(u1_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_40310])).

tff(c_40850,plain,
    ( ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5'))))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_27880,c_40847])).

tff(c_40853,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25364,c_27849,c_40850])).

tff(c_40855,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27881,c_40853])).

tff(c_40865,plain,(
    ! [B_1678] :
      ( ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_1678)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_1678)))
      | k9_tmap_1('#skF_5',B_1678) = k6_partfun1(u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_1678,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_40310])).

tff(c_40881,plain,(
    ! [B_765] :
      ( ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_5'))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_765)))
      | k9_tmap_1('#skF_5',B_765) = k6_partfun1(u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_765,'#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(B_765,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ m1_pre_topc(B_765,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16457,c_40865])).

tff(c_40893,plain,(
    ! [B_765] :
      ( ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_765)))
      | k9_tmap_1('#skF_5',B_765) = k6_partfun1(u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_765,'#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_76,c_78,c_27849,c_40881])).

tff(c_40895,plain,(
    ! [B_1679] :
      ( ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_5',B_1679)))
      | k9_tmap_1('#skF_5',B_1679) = k6_partfun1(u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_1679,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_40893])).

tff(c_40911,plain,(
    ! [B_765] :
      ( ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_5'))
      | k9_tmap_1('#skF_5',B_765) = k6_partfun1(u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_765,'#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(B_765,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ m1_pre_topc(B_765,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16457,c_40895])).

tff(c_40923,plain,(
    ! [B_765] :
      ( k9_tmap_1('#skF_5',B_765) = k6_partfun1(u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_765,'#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_76,c_78,c_25364,c_40911])).

tff(c_40925,plain,(
    ! [B_1680] :
      ( k9_tmap_1('#skF_5',B_1680) = k6_partfun1(u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_1680,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_40923])).

tff(c_40928,plain,(
    k6_partfun1(u1_struct_0('#skF_5')) = k9_tmap_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_40925])).

tff(c_15706,plain,(
    ! [A_680,B_681] :
      ( v5_pre_topc(k7_tmap_1(A_680,B_681),A_680,k6_tmap_1(A_680,B_681))
      | ~ v3_pre_topc(B_681,A_680)
      | ~ m1_subset_1(B_681,k1_zfmisc_1(u1_struct_0(A_680)))
      | ~ l1_pre_topc(A_680)
      | ~ v2_pre_topc(A_680)
      | v2_struct_0(A_680) ) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_20397,plain,(
    ! [A_962,B_963] :
      ( v5_pre_topc(k6_partfun1(u1_struct_0(A_962)),A_962,k6_tmap_1(A_962,u1_struct_0(B_963)))
      | ~ v3_pre_topc(u1_struct_0(B_963),A_962)
      | ~ m1_subset_1(u1_struct_0(B_963),k1_zfmisc_1(u1_struct_0(A_962)))
      | ~ l1_pre_topc(A_962)
      | ~ v2_pre_topc(A_962)
      | v2_struct_0(A_962)
      | ~ v2_pre_topc(A_962)
      | v2_struct_0(A_962)
      | ~ m1_pre_topc(B_963,A_962)
      | ~ l1_pre_topc(A_962) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15411,c_15706])).

tff(c_20442,plain,(
    ! [A_70,B_71] :
      ( v5_pre_topc(k6_partfun1(u1_struct_0(A_70)),A_70,k8_tmap_1(A_70,B_71))
      | ~ v3_pre_topc(u1_struct_0(B_71),A_70)
      | ~ m1_subset_1(u1_struct_0(B_71),k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70)
      | v2_struct_0(A_70)
      | ~ v2_pre_topc(A_70)
      | v2_struct_0(A_70)
      | ~ m1_pre_topc(B_71,A_70)
      | ~ l1_pre_topc(A_70)
      | ~ m1_pre_topc(B_71,A_70)
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70)
      | v2_struct_0(A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16413,c_20397])).

tff(c_40957,plain,(
    ! [B_71] :
      ( v5_pre_topc(k9_tmap_1('#skF_5','#skF_6'),'#skF_5',k8_tmap_1('#skF_5',B_71))
      | ~ v3_pre_topc(u1_struct_0(B_71),'#skF_5')
      | ~ m1_subset_1(u1_struct_0(B_71),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(B_71,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ m1_pre_topc(B_71,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40928,c_20442])).

tff(c_41030,plain,(
    ! [B_71] :
      ( v5_pre_topc(k9_tmap_1('#skF_5','#skF_6'),'#skF_5',k8_tmap_1('#skF_5',B_71))
      | ~ v3_pre_topc(u1_struct_0(B_71),'#skF_5')
      | ~ m1_subset_1(u1_struct_0(B_71),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc(B_71,'#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_76,c_78,c_78,c_76,c_40957])).

tff(c_44525,plain,(
    ! [B_1700] :
      ( v5_pre_topc(k9_tmap_1('#skF_5','#skF_6'),'#skF_5',k8_tmap_1('#skF_5',B_1700))
      | ~ v3_pre_topc(u1_struct_0(B_1700),'#skF_5')
      | ~ m1_subset_1(u1_struct_0(B_1700),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc(B_1700,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_41030])).

tff(c_44611,plain,(
    ! [B_82] :
      ( v5_pre_topc(k9_tmap_1('#skF_5','#skF_6'),'#skF_5',k8_tmap_1('#skF_5',B_82))
      | ~ v3_pre_topc(u1_struct_0(B_82),'#skF_5')
      | ~ m1_pre_topc(B_82,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_72,c_44525])).

tff(c_44619,plain,(
    ! [B_1701] :
      ( v5_pre_topc(k9_tmap_1('#skF_5','#skF_6'),'#skF_5',k8_tmap_1('#skF_5',B_1701))
      | ~ v3_pre_topc(u1_struct_0(B_1701),'#skF_5')
      | ~ m1_pre_topc(B_1701,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_44611])).

tff(c_15322,plain,(
    ~ v5_pre_topc(k9_tmap_1('#skF_5','#skF_6'),'#skF_5',k8_tmap_1('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_44622,plain,
    ( ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_5')
    | ~ m1_pre_topc('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_44619,c_15322])).

tff(c_44633,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_44622])).

tff(c_44642,plain,
    ( ~ v1_tsep_1('#skF_6','#skF_5')
    | ~ m1_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_15504,c_44633])).

tff(c_44646,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_15321,c_44642])).

tff(c_44648,plain,(
    ~ v1_funct_1(k9_tmap_1('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_44659,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_44656,c_44648])).

tff(c_44662,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_44659])).

tff(c_44664,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_44662])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:02:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 28.22/16.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 28.35/16.49  
% 28.35/16.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 28.35/16.49  %$ r1_funct_2 > v5_pre_topc > v1_funct_2 > v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k9_tmap_1 > k8_tmap_1 > k7_tmap_1 > k6_tmap_1 > k5_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_pre_topc > k6_partfun1 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 28.35/16.49  
% 28.35/16.49  %Foreground sorts:
% 28.35/16.49  
% 28.35/16.49  
% 28.35/16.49  %Background operators:
% 28.35/16.49  
% 28.35/16.49  
% 28.35/16.49  %Foreground operators:
% 28.35/16.49  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 28.35/16.49  tff(k7_tmap_1, type, k7_tmap_1: ($i * $i) > $i).
% 28.35/16.49  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 28.35/16.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 28.35/16.49  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 28.35/16.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 28.35/16.49  tff('#skF_1', type, '#skF_1': $i > $i).
% 28.35/16.49  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 28.35/16.49  tff('#skF_5', type, '#skF_5': $i).
% 28.35/16.49  tff(k9_tmap_1, type, k9_tmap_1: ($i * $i) > $i).
% 28.35/16.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 28.35/16.49  tff(k8_tmap_1, type, k8_tmap_1: ($i * $i) > $i).
% 28.35/16.49  tff('#skF_6', type, '#skF_6': $i).
% 28.35/16.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 28.35/16.49  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 28.35/16.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 28.35/16.49  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 28.35/16.49  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 28.35/16.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 28.35/16.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 28.35/16.49  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 28.35/16.49  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 28.35/16.49  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 28.35/16.49  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 28.35/16.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 28.35/16.49  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 28.35/16.49  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 28.35/16.49  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 28.35/16.49  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 28.35/16.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 28.35/16.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 28.35/16.49  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 28.35/16.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 28.35/16.49  
% 28.61/16.53  tff(f_253, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> (((v1_funct_1(k9_tmap_1(A, B)) & v1_funct_2(k9_tmap_1(A, B), u1_struct_0(A), u1_struct_0(k8_tmap_1(A, B)))) & v5_pre_topc(k9_tmap_1(A, B), A, k8_tmap_1(A, B))) & m1_subset_1(k9_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k8_tmap_1(A, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t122_tmap_1)).
% 28.61/16.53  tff(f_189, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_funct_1(k9_tmap_1(A, B)) & v1_funct_2(k9_tmap_1(A, B), u1_struct_0(A), u1_struct_0(k8_tmap_1(A, B)))) & m1_subset_1(k9_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k8_tmap_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_tmap_1)).
% 28.61/16.53  tff(f_144, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tsep_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tsep_1)).
% 28.61/16.53  tff(f_174, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_pre_topc(k8_tmap_1(A, B)) & v2_pre_topc(k8_tmap_1(A, B))) & l1_pre_topc(k8_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 28.61/16.53  tff(f_230, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 28.61/16.53  tff(f_104, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (((v1_pre_topc(C) & v2_pre_topc(C)) & l1_pre_topc(C)) => ((C = k8_tmap_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((D = u1_struct_0(B)) => (C = k6_tmap_1(A, D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_tmap_1)).
% 28.61/16.53  tff(f_203, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 28.61/16.53  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 28.61/16.53  tff(f_66, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 28.61/16.53  tff(f_37, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 28.61/16.53  tff(f_78, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k7_tmap_1(A, B) = k6_partfun1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_tmap_1)).
% 28.61/16.53  tff(f_159, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_funct_1(k7_tmap_1(A, B)) & v1_funct_2(k7_tmap_1(A, B), u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))) & m1_subset_1(k7_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 28.61/16.53  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_connsp_1)).
% 28.61/16.53  tff(f_130, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(k8_tmap_1(A, B)))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k8_tmap_1(A, B)))))) => ((C = k9_tmap_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((D = u1_struct_0(B)) => r1_funct_2(u1_struct_0(A), u1_struct_0(k8_tmap_1(A, B)), u1_struct_0(A), u1_struct_0(k6_tmap_1(A, D)), C, k7_tmap_1(A, D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_tmap_1)).
% 28.61/16.53  tff(f_223, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (((v1_funct_1(k7_tmap_1(A, B)) & v1_funct_2(k7_tmap_1(A, B), u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))) & v5_pre_topc(k7_tmap_1(A, B), A, k6_tmap_1(A, B))) & m1_subset_1(k7_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_tmap_1)).
% 28.61/16.53  tff(c_80, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_253])).
% 28.61/16.53  tff(c_78, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_253])).
% 28.61/16.53  tff(c_76, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_253])).
% 28.61/16.53  tff(c_74, plain, (m1_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_253])).
% 28.61/16.53  tff(c_44656, plain, (![A_1709, B_1710]: (v1_funct_1(k9_tmap_1(A_1709, B_1710)) | ~m1_pre_topc(B_1710, A_1709) | ~l1_pre_topc(A_1709) | ~v2_pre_topc(A_1709) | v2_struct_0(A_1709))), inference(cnfTransformation, [status(thm)], [f_189])).
% 28.61/16.53  tff(c_15306, plain, (![A_619, B_620]: (v1_funct_2(k9_tmap_1(A_619, B_620), u1_struct_0(A_619), u1_struct_0(k8_tmap_1(A_619, B_620))) | ~m1_pre_topc(B_620, A_619) | ~l1_pre_topc(A_619) | ~v2_pre_topc(A_619) | v2_struct_0(A_619))), inference(cnfTransformation, [status(thm)], [f_189])).
% 28.61/16.53  tff(c_15065, plain, (![A_580, B_581]: (m1_subset_1(k9_tmap_1(A_580, B_581), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_580), u1_struct_0(k8_tmap_1(A_580, B_581))))) | ~m1_pre_topc(B_581, A_580) | ~l1_pre_topc(A_580) | ~v2_pre_topc(A_580) | v2_struct_0(A_580))), inference(cnfTransformation, [status(thm)], [f_189])).
% 28.61/16.53  tff(c_110, plain, (v1_tsep_1('#skF_6', '#skF_5') | v1_funct_1(k9_tmap_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_253])).
% 28.61/16.53  tff(c_120, plain, (v1_funct_1(k9_tmap_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_110])).
% 28.61/16.53  tff(c_104, plain, (v1_tsep_1('#skF_6', '#skF_5') | v1_funct_2(k9_tmap_1('#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_253])).
% 28.61/16.53  tff(c_125, plain, (v1_funct_2(k9_tmap_1('#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_104])).
% 28.61/16.53  tff(c_98, plain, (v1_tsep_1('#skF_6', '#skF_5') | v5_pre_topc(k9_tmap_1('#skF_5', '#skF_6'), '#skF_5', k8_tmap_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_253])).
% 28.61/16.53  tff(c_121, plain, (v5_pre_topc(k9_tmap_1('#skF_5', '#skF_6'), '#skF_5', k8_tmap_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_98])).
% 28.61/16.53  tff(c_92, plain, (v1_tsep_1('#skF_6', '#skF_5') | m1_subset_1(k9_tmap_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', '#skF_6')))))), inference(cnfTransformation, [status(thm)], [f_253])).
% 28.61/16.53  tff(c_129, plain, (m1_subset_1(k9_tmap_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', '#skF_6')))))), inference(splitLeft, [status(thm)], [c_92])).
% 28.61/16.53  tff(c_82, plain, (~m1_subset_1(k9_tmap_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', '#skF_6'))))) | ~v5_pre_topc(k9_tmap_1('#skF_5', '#skF_6'), '#skF_5', k8_tmap_1('#skF_5', '#skF_6')) | ~v1_funct_2(k9_tmap_1('#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', '#skF_6'))) | ~v1_funct_1(k9_tmap_1('#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_6', '#skF_5') | ~v1_tsep_1('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_253])).
% 28.61/16.53  tff(c_115, plain, (~m1_subset_1(k9_tmap_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', '#skF_6'))))) | ~v5_pre_topc(k9_tmap_1('#skF_5', '#skF_6'), '#skF_5', k8_tmap_1('#skF_5', '#skF_6')) | ~v1_funct_2(k9_tmap_1('#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', '#skF_6'))) | ~v1_funct_1(k9_tmap_1('#skF_5', '#skF_6')) | ~v1_tsep_1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_82])).
% 28.61/16.53  tff(c_174, plain, (~v1_tsep_1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_125, c_121, c_129, c_115])).
% 28.61/16.53  tff(c_36, plain, (![B_64, A_58]: (u1_struct_0(B_64)='#skF_4'(A_58, B_64) | v1_tsep_1(B_64, A_58) | ~m1_pre_topc(B_64, A_58) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_144])).
% 28.61/16.53  tff(c_177, plain, (u1_struct_0('#skF_6')='#skF_4'('#skF_5', '#skF_6') | ~m1_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_36, c_174])).
% 28.61/16.53  tff(c_180, plain, (u1_struct_0('#skF_6')='#skF_4'('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_177])).
% 28.61/16.53  tff(c_46, plain, (![A_70, B_71]: (l1_pre_topc(k8_tmap_1(A_70, B_71)) | ~m1_pre_topc(B_71, A_70) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_174])).
% 28.61/16.53  tff(c_50, plain, (![A_70, B_71]: (v1_pre_topc(k8_tmap_1(A_70, B_71)) | ~m1_pre_topc(B_71, A_70) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_174])).
% 28.61/16.53  tff(c_48, plain, (![A_70, B_71]: (v2_pre_topc(k8_tmap_1(A_70, B_71)) | ~m1_pre_topc(B_71, A_70) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_174])).
% 28.61/16.53  tff(c_72, plain, (![B_82, A_80]: (m1_subset_1(u1_struct_0(B_82), k1_zfmisc_1(u1_struct_0(A_80))) | ~m1_pre_topc(B_82, A_80) | ~l1_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_230])).
% 28.61/16.53  tff(c_2461, plain, (![A_268, B_269]: (k6_tmap_1(A_268, u1_struct_0(B_269))=k8_tmap_1(A_268, B_269) | ~m1_subset_1(u1_struct_0(B_269), k1_zfmisc_1(u1_struct_0(A_268))) | ~l1_pre_topc(k8_tmap_1(A_268, B_269)) | ~v2_pre_topc(k8_tmap_1(A_268, B_269)) | ~v1_pre_topc(k8_tmap_1(A_268, B_269)) | ~m1_pre_topc(B_269, A_268) | ~l1_pre_topc(A_268) | ~v2_pre_topc(A_268) | v2_struct_0(A_268))), inference(cnfTransformation, [status(thm)], [f_104])).
% 28.61/16.53  tff(c_2525, plain, (![A_270, B_271]: (k6_tmap_1(A_270, u1_struct_0(B_271))=k8_tmap_1(A_270, B_271) | ~l1_pre_topc(k8_tmap_1(A_270, B_271)) | ~v2_pre_topc(k8_tmap_1(A_270, B_271)) | ~v1_pre_topc(k8_tmap_1(A_270, B_271)) | ~v2_pre_topc(A_270) | v2_struct_0(A_270) | ~m1_pre_topc(B_271, A_270) | ~l1_pre_topc(A_270))), inference(resolution, [status(thm)], [c_72, c_2461])).
% 28.61/16.53  tff(c_2530, plain, (![A_272, B_273]: (k6_tmap_1(A_272, u1_struct_0(B_273))=k8_tmap_1(A_272, B_273) | ~l1_pre_topc(k8_tmap_1(A_272, B_273)) | ~v1_pre_topc(k8_tmap_1(A_272, B_273)) | ~m1_pre_topc(B_273, A_272) | ~l1_pre_topc(A_272) | ~v2_pre_topc(A_272) | v2_struct_0(A_272))), inference(resolution, [status(thm)], [c_48, c_2525])).
% 28.61/16.53  tff(c_2535, plain, (![A_274, B_275]: (k6_tmap_1(A_274, u1_struct_0(B_275))=k8_tmap_1(A_274, B_275) | ~l1_pre_topc(k8_tmap_1(A_274, B_275)) | ~m1_pre_topc(B_275, A_274) | ~l1_pre_topc(A_274) | ~v2_pre_topc(A_274) | v2_struct_0(A_274))), inference(resolution, [status(thm)], [c_50, c_2530])).
% 28.61/16.53  tff(c_2541, plain, (![A_278, B_279]: (k6_tmap_1(A_278, u1_struct_0(B_279))=k8_tmap_1(A_278, B_279) | ~m1_pre_topc(B_279, A_278) | ~l1_pre_topc(A_278) | ~v2_pre_topc(A_278) | v2_struct_0(A_278))), inference(resolution, [status(thm)], [c_46, c_2535])).
% 28.61/16.53  tff(c_2625, plain, (![A_280]: (k6_tmap_1(A_280, '#skF_4'('#skF_5', '#skF_6'))=k8_tmap_1(A_280, '#skF_6') | ~m1_pre_topc('#skF_6', A_280) | ~l1_pre_topc(A_280) | ~v2_pre_topc(A_280) | v2_struct_0(A_280))), inference(superposition, [status(thm), theory('equality')], [c_180, c_2541])).
% 28.61/16.53  tff(c_38, plain, (![A_58, B_64]: (m1_subset_1('#skF_4'(A_58, B_64), k1_zfmisc_1(u1_struct_0(A_58))) | v1_tsep_1(B_64, A_58) | ~m1_pre_topc(B_64, A_58) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_144])).
% 28.61/16.53  tff(c_215, plain, (![A_112, B_113]: (u1_struct_0(k6_tmap_1(A_112, B_113))=u1_struct_0(A_112) | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_pre_topc(A_112) | ~v2_pre_topc(A_112) | v2_struct_0(A_112))), inference(cnfTransformation, [status(thm)], [f_203])).
% 28.61/16.53  tff(c_229, plain, (![A_58, B_64]: (u1_struct_0(k6_tmap_1(A_58, '#skF_4'(A_58, B_64)))=u1_struct_0(A_58) | ~v2_pre_topc(A_58) | v2_struct_0(A_58) | v1_tsep_1(B_64, A_58) | ~m1_pre_topc(B_64, A_58) | ~l1_pre_topc(A_58))), inference(resolution, [status(thm)], [c_38, c_215])).
% 28.61/16.53  tff(c_2684, plain, (u1_struct_0(k8_tmap_1('#skF_5', '#skF_6'))=u1_struct_0('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | v1_tsep_1('#skF_6', '#skF_5') | ~m1_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~m1_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2625, c_229])).
% 28.61/16.53  tff(c_2708, plain, (u1_struct_0(k8_tmap_1('#skF_5', '#skF_6'))=u1_struct_0('#skF_5') | v1_tsep_1('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_76, c_74, c_78, c_2684])).
% 28.61/16.53  tff(c_2709, plain, (u1_struct_0(k8_tmap_1('#skF_5', '#skF_6'))=u1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_80, c_174, c_2708])).
% 28.61/16.53  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 28.61/16.53  tff(c_1828, plain, (![A_231, B_232]: (k6_tmap_1(A_231, u1_struct_0(B_232))=k8_tmap_1(A_231, B_232) | ~m1_subset_1(u1_struct_0(B_232), k1_zfmisc_1(u1_struct_0(A_231))) | ~l1_pre_topc(k8_tmap_1(A_231, B_232)) | ~v2_pre_topc(k8_tmap_1(A_231, B_232)) | ~v1_pre_topc(k8_tmap_1(A_231, B_232)) | ~m1_pre_topc(B_232, A_231) | ~l1_pre_topc(A_231) | ~v2_pre_topc(A_231) | v2_struct_0(A_231))), inference(cnfTransformation, [status(thm)], [f_104])).
% 28.61/16.53  tff(c_1914, plain, (![A_236, B_237]: (k6_tmap_1(A_236, u1_struct_0(B_237))=k8_tmap_1(A_236, B_237) | ~l1_pre_topc(k8_tmap_1(A_236, B_237)) | ~v2_pre_topc(k8_tmap_1(A_236, B_237)) | ~v1_pre_topc(k8_tmap_1(A_236, B_237)) | ~v2_pre_topc(A_236) | v2_struct_0(A_236) | ~m1_pre_topc(B_237, A_236) | ~l1_pre_topc(A_236))), inference(resolution, [status(thm)], [c_72, c_1828])).
% 28.61/16.53  tff(c_1990, plain, (![A_240, B_241]: (k6_tmap_1(A_240, u1_struct_0(B_241))=k8_tmap_1(A_240, B_241) | ~l1_pre_topc(k8_tmap_1(A_240, B_241)) | ~v1_pre_topc(k8_tmap_1(A_240, B_241)) | ~m1_pre_topc(B_241, A_240) | ~l1_pre_topc(A_240) | ~v2_pre_topc(A_240) | v2_struct_0(A_240))), inference(resolution, [status(thm)], [c_48, c_1914])).
% 28.61/16.53  tff(c_1995, plain, (![A_242, B_243]: (k6_tmap_1(A_242, u1_struct_0(B_243))=k8_tmap_1(A_242, B_243) | ~l1_pre_topc(k8_tmap_1(A_242, B_243)) | ~m1_pre_topc(B_243, A_242) | ~l1_pre_topc(A_242) | ~v2_pre_topc(A_242) | v2_struct_0(A_242))), inference(resolution, [status(thm)], [c_50, c_1990])).
% 28.61/16.53  tff(c_2000, plain, (![A_244, B_245]: (k6_tmap_1(A_244, u1_struct_0(B_245))=k8_tmap_1(A_244, B_245) | ~m1_pre_topc(B_245, A_244) | ~l1_pre_topc(A_244) | ~v2_pre_topc(A_244) | v2_struct_0(A_244))), inference(resolution, [status(thm)], [c_46, c_1995])).
% 28.61/16.53  tff(c_2078, plain, (![A_246]: (k6_tmap_1(A_246, '#skF_4'('#skF_5', '#skF_6'))=k8_tmap_1(A_246, '#skF_6') | ~m1_pre_topc('#skF_6', A_246) | ~l1_pre_topc(A_246) | ~v2_pre_topc(A_246) | v2_struct_0(A_246))), inference(superposition, [status(thm), theory('equality')], [c_180, c_2000])).
% 28.61/16.53  tff(c_2126, plain, (u1_struct_0(k8_tmap_1('#skF_5', '#skF_6'))=u1_struct_0('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | v1_tsep_1('#skF_6', '#skF_5') | ~m1_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~m1_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2078, c_229])).
% 28.61/16.53  tff(c_2144, plain, (u1_struct_0(k8_tmap_1('#skF_5', '#skF_6'))=u1_struct_0('#skF_5') | v1_tsep_1('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_76, c_74, c_78, c_2126])).
% 28.61/16.53  tff(c_2145, plain, (u1_struct_0(k8_tmap_1('#skF_5', '#skF_6'))=u1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_80, c_174, c_2144])).
% 28.61/16.53  tff(c_1651, plain, (![A_225, D_221, C_224, F_222, B_223]: (r1_funct_2(A_225, B_223, C_224, D_221, F_222, F_222) | ~m1_subset_1(F_222, k1_zfmisc_1(k2_zfmisc_1(C_224, D_221))) | ~v1_funct_2(F_222, C_224, D_221) | ~m1_subset_1(F_222, k1_zfmisc_1(k2_zfmisc_1(A_225, B_223))) | ~v1_funct_2(F_222, A_225, B_223) | ~v1_funct_1(F_222) | v1_xboole_0(D_221) | v1_xboole_0(B_223))), inference(cnfTransformation, [status(thm)], [f_66])).
% 28.61/16.53  tff(c_1657, plain, (![A_225, B_223]: (r1_funct_2(A_225, B_223, u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', '#skF_6')), k9_tmap_1('#skF_5', '#skF_6'), k9_tmap_1('#skF_5', '#skF_6')) | ~v1_funct_2(k9_tmap_1('#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', '#skF_6'))) | ~m1_subset_1(k9_tmap_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(A_225, B_223))) | ~v1_funct_2(k9_tmap_1('#skF_5', '#skF_6'), A_225, B_223) | ~v1_funct_1(k9_tmap_1('#skF_5', '#skF_6')) | v1_xboole_0(u1_struct_0(k8_tmap_1('#skF_5', '#skF_6'))) | v1_xboole_0(B_223))), inference(resolution, [status(thm)], [c_129, c_1651])).
% 28.61/16.53  tff(c_1662, plain, (![A_225, B_223]: (r1_funct_2(A_225, B_223, u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', '#skF_6')), k9_tmap_1('#skF_5', '#skF_6'), k9_tmap_1('#skF_5', '#skF_6')) | ~m1_subset_1(k9_tmap_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(A_225, B_223))) | ~v1_funct_2(k9_tmap_1('#skF_5', '#skF_6'), A_225, B_223) | v1_xboole_0(u1_struct_0(k8_tmap_1('#skF_5', '#skF_6'))) | v1_xboole_0(B_223))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_125, c_1657])).
% 28.61/16.53  tff(c_1808, plain, (v1_xboole_0(u1_struct_0(k8_tmap_1('#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_1662])).
% 28.61/16.53  tff(c_2147, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2145, c_1808])).
% 28.61/16.53  tff(c_4, plain, (![A_2]: (~v1_xboole_0(u1_struct_0(A_2)) | ~l1_struct_0(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_37])).
% 28.61/16.53  tff(c_2317, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_2147, c_4])).
% 28.61/16.53  tff(c_2320, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_80, c_2317])).
% 28.61/16.53  tff(c_2323, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_2, c_2320])).
% 28.61/16.53  tff(c_2327, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_2323])).
% 28.61/16.53  tff(c_2329, plain, (~v1_xboole_0(u1_struct_0(k8_tmap_1('#skF_5', '#skF_6')))), inference(splitRight, [status(thm)], [c_1662])).
% 28.61/16.53  tff(c_2712, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2709, c_2329])).
% 28.61/16.53  tff(c_2622, plain, (![A_278]: (k6_tmap_1(A_278, '#skF_4'('#skF_5', '#skF_6'))=k8_tmap_1(A_278, '#skF_6') | ~m1_pre_topc('#skF_6', A_278) | ~l1_pre_topc(A_278) | ~v2_pre_topc(A_278) | v2_struct_0(A_278))), inference(superposition, [status(thm), theory('equality')], [c_180, c_2541])).
% 28.61/16.53  tff(c_196, plain, (![A_80]: (m1_subset_1('#skF_4'('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0(A_80))) | ~m1_pre_topc('#skF_6', A_80) | ~l1_pre_topc(A_80))), inference(superposition, [status(thm), theory('equality')], [c_180, c_72])).
% 28.61/16.53  tff(c_146, plain, (![A_106, B_107]: (k7_tmap_1(A_106, B_107)=k6_partfun1(u1_struct_0(A_106)) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106) | ~v2_pre_topc(A_106) | v2_struct_0(A_106))), inference(cnfTransformation, [status(thm)], [f_78])).
% 28.61/16.53  tff(c_339, plain, (![A_119, B_120]: (k7_tmap_1(A_119, u1_struct_0(B_120))=k6_partfun1(u1_struct_0(A_119)) | ~v2_pre_topc(A_119) | v2_struct_0(A_119) | ~m1_pre_topc(B_120, A_119) | ~l1_pre_topc(A_119))), inference(resolution, [status(thm)], [c_72, c_146])).
% 28.61/16.53  tff(c_357, plain, (![A_119]: (k7_tmap_1(A_119, '#skF_4'('#skF_5', '#skF_6'))=k6_partfun1(u1_struct_0(A_119)) | ~v2_pre_topc(A_119) | v2_struct_0(A_119) | ~m1_pre_topc('#skF_6', A_119) | ~l1_pre_topc(A_119))), inference(superposition, [status(thm), theory('equality')], [c_180, c_339])).
% 28.61/16.53  tff(c_133, plain, (![A_104, B_105]: (v1_funct_1(k7_tmap_1(A_104, B_105)) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104) | ~v2_pre_topc(A_104) | v2_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_159])).
% 28.61/16.53  tff(c_555, plain, (![A_136, B_137]: (v1_funct_1(k7_tmap_1(A_136, '#skF_4'(A_136, B_137))) | ~v2_pre_topc(A_136) | v2_struct_0(A_136) | v1_tsep_1(B_137, A_136) | ~m1_pre_topc(B_137, A_136) | ~l1_pre_topc(A_136))), inference(resolution, [status(thm)], [c_38, c_133])).
% 28.61/16.53  tff(c_559, plain, (v1_funct_1(k6_partfun1(u1_struct_0('#skF_5'))) | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | v1_tsep_1('#skF_6', '#skF_5') | ~m1_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_357, c_555])).
% 28.61/16.53  tff(c_561, plain, (v1_funct_1(k6_partfun1(u1_struct_0('#skF_5'))) | v1_tsep_1('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_78, c_76, c_74, c_78, c_559])).
% 28.61/16.53  tff(c_562, plain, (v1_funct_1(k6_partfun1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_80, c_174, c_561])).
% 28.61/16.53  tff(c_8, plain, (![A_3]: (m1_subset_1('#skF_1'(A_3), k1_zfmisc_1(u1_struct_0(A_3))) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_44])).
% 28.61/16.53  tff(c_2841, plain, (m1_subset_1('#skF_1'(k8_tmap_1('#skF_5', '#skF_6')), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc(k8_tmap_1('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2709, c_8])).
% 28.61/16.53  tff(c_2883, plain, (~l1_pre_topc(k8_tmap_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_2841])).
% 28.61/16.53  tff(c_2886, plain, (~m1_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_46, c_2883])).
% 28.61/16.53  tff(c_2889, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_2886])).
% 28.61/16.53  tff(c_2891, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_2889])).
% 28.61/16.53  tff(c_2892, plain, (m1_subset_1('#skF_1'(k8_tmap_1('#skF_5', '#skF_6')), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_2841])).
% 28.61/16.53  tff(c_14, plain, (![A_11, B_13]: (k7_tmap_1(A_11, B_13)=k6_partfun1(u1_struct_0(A_11)) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_78])).
% 28.61/16.53  tff(c_2902, plain, (k7_tmap_1('#skF_5', '#skF_1'(k8_tmap_1('#skF_5', '#skF_6')))=k6_partfun1(u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_2892, c_14])).
% 28.61/16.53  tff(c_2916, plain, (k7_tmap_1('#skF_5', '#skF_1'(k8_tmap_1('#skF_5', '#skF_6')))=k6_partfun1(u1_struct_0('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_2902])).
% 28.61/16.53  tff(c_2917, plain, (k7_tmap_1('#skF_5', '#skF_1'(k8_tmap_1('#skF_5', '#skF_6')))=k6_partfun1(u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_80, c_2916])).
% 28.61/16.53  tff(c_60, plain, (![A_74, B_76]: (u1_struct_0(k6_tmap_1(A_74, B_76))=u1_struct_0(A_74) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_203])).
% 28.61/16.53  tff(c_2899, plain, (u1_struct_0(k6_tmap_1('#skF_5', '#skF_1'(k8_tmap_1('#skF_5', '#skF_6'))))=u1_struct_0('#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_2892, c_60])).
% 28.61/16.53  tff(c_2912, plain, (u1_struct_0(k6_tmap_1('#skF_5', '#skF_1'(k8_tmap_1('#skF_5', '#skF_6'))))=u1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_2899])).
% 28.61/16.53  tff(c_2913, plain, (u1_struct_0(k6_tmap_1('#skF_5', '#skF_1'(k8_tmap_1('#skF_5', '#skF_6'))))=u1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_80, c_2912])).
% 28.61/16.53  tff(c_42, plain, (![A_68, B_69]: (v1_funct_2(k7_tmap_1(A_68, B_69), u1_struct_0(A_68), u1_struct_0(k6_tmap_1(A_68, B_69))) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68) | ~v2_pre_topc(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_159])).
% 28.61/16.53  tff(c_3066, plain, (v1_funct_2(k7_tmap_1('#skF_5', '#skF_1'(k8_tmap_1('#skF_5', '#skF_6'))), u1_struct_0('#skF_5'), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_1'(k8_tmap_1('#skF_5', '#skF_6')), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2913, c_42])).
% 28.61/16.53  tff(c_3143, plain, (v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_2892, c_2917, c_3066])).
% 28.61/16.53  tff(c_3144, plain, (v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_80, c_3143])).
% 28.61/16.53  tff(c_40, plain, (![A_68, B_69]: (m1_subset_1(k7_tmap_1(A_68, B_69), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_68), u1_struct_0(k6_tmap_1(A_68, B_69))))) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68) | ~v2_pre_topc(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_159])).
% 28.61/16.53  tff(c_3057, plain, (m1_subset_1(k7_tmap_1('#skF_5', '#skF_1'(k8_tmap_1('#skF_5', '#skF_6'))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_5')))) | ~m1_subset_1('#skF_1'(k8_tmap_1('#skF_5', '#skF_6')), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2913, c_40])).
% 28.61/16.53  tff(c_3138, plain, (m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_5')))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_2892, c_2917, c_3057])).
% 28.61/16.53  tff(c_3139, plain, (m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_80, c_3138])).
% 28.61/16.53  tff(c_2922, plain, (![B_287, A_288, C_289]: (u1_struct_0(B_287)='#skF_3'(A_288, B_287, C_289) | k9_tmap_1(A_288, B_287)=C_289 | ~m1_subset_1(C_289, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_288), u1_struct_0(k8_tmap_1(A_288, B_287))))) | ~v1_funct_2(C_289, u1_struct_0(A_288), u1_struct_0(k8_tmap_1(A_288, B_287))) | ~v1_funct_1(C_289) | ~m1_pre_topc(B_287, A_288) | ~l1_pre_topc(A_288) | ~v2_pre_topc(A_288) | v2_struct_0(A_288))), inference(cnfTransformation, [status(thm)], [f_130])).
% 28.61/16.53  tff(c_2928, plain, (![C_289]: (u1_struct_0('#skF_6')='#skF_3'('#skF_5', '#skF_6', C_289) | k9_tmap_1('#skF_5', '#skF_6')=C_289 | ~m1_subset_1(C_289, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_5')))) | ~v1_funct_2(C_289, u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', '#skF_6'))) | ~v1_funct_1(C_289) | ~m1_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2709, c_2922])).
% 28.61/16.53  tff(c_2962, plain, (![C_289]: ('#skF_3'('#skF_5', '#skF_6', C_289)='#skF_4'('#skF_5', '#skF_6') | k9_tmap_1('#skF_5', '#skF_6')=C_289 | ~m1_subset_1(C_289, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_5')))) | ~v1_funct_2(C_289, u1_struct_0('#skF_5'), u1_struct_0('#skF_5')) | ~v1_funct_1(C_289) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_2709, c_180, c_2928])).
% 28.61/16.53  tff(c_9113, plain, (![C_443]: ('#skF_3'('#skF_5', '#skF_6', C_443)='#skF_4'('#skF_5', '#skF_6') | k9_tmap_1('#skF_5', '#skF_6')=C_443 | ~m1_subset_1(C_443, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_5')))) | ~v1_funct_2(C_443, u1_struct_0('#skF_5'), u1_struct_0('#skF_5')) | ~v1_funct_1(C_443))), inference(negUnitSimplification, [status(thm)], [c_80, c_2962])).
% 28.61/16.53  tff(c_9123, plain, ('#skF_3'('#skF_5', '#skF_6', k6_partfun1(u1_struct_0('#skF_5')))='#skF_4'('#skF_5', '#skF_6') | k6_partfun1(u1_struct_0('#skF_5'))=k9_tmap_1('#skF_5', '#skF_6') | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_5')) | ~v1_funct_1(k6_partfun1(u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_3139, c_9113])).
% 28.61/16.53  tff(c_9134, plain, ('#skF_3'('#skF_5', '#skF_6', k6_partfun1(u1_struct_0('#skF_5')))='#skF_4'('#skF_5', '#skF_6') | k6_partfun1(u1_struct_0('#skF_5'))=k9_tmap_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_562, c_3144, c_9123])).
% 28.61/16.53  tff(c_9139, plain, (k6_partfun1(u1_struct_0('#skF_5'))=k9_tmap_1('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_9134])).
% 28.61/16.53  tff(c_157, plain, (![A_80, B_82]: (k7_tmap_1(A_80, u1_struct_0(B_82))=k6_partfun1(u1_struct_0(A_80)) | ~v2_pre_topc(A_80) | v2_struct_0(A_80) | ~m1_pre_topc(B_82, A_80) | ~l1_pre_topc(A_80))), inference(resolution, [status(thm)], [c_72, c_146])).
% 28.61/16.53  tff(c_734, plain, (![A_150, B_151]: (v1_funct_2(k7_tmap_1(A_150, B_151), u1_struct_0(A_150), u1_struct_0(k6_tmap_1(A_150, B_151))) | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0(A_150))) | ~l1_pre_topc(A_150) | ~v2_pre_topc(A_150) | v2_struct_0(A_150))), inference(cnfTransformation, [status(thm)], [f_159])).
% 28.61/16.53  tff(c_10081, plain, (![A_452, B_453]: (v1_funct_2(k6_partfun1(u1_struct_0(A_452)), u1_struct_0(A_452), u1_struct_0(k6_tmap_1(A_452, u1_struct_0(B_453)))) | ~m1_subset_1(u1_struct_0(B_453), k1_zfmisc_1(u1_struct_0(A_452))) | ~l1_pre_topc(A_452) | ~v2_pre_topc(A_452) | v2_struct_0(A_452) | ~v2_pre_topc(A_452) | v2_struct_0(A_452) | ~m1_pre_topc(B_453, A_452) | ~l1_pre_topc(A_452))), inference(superposition, [status(thm), theory('equality')], [c_157, c_734])).
% 28.61/16.53  tff(c_10093, plain, (![B_453]: (v1_funct_2(k9_tmap_1('#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0(k6_tmap_1('#skF_5', u1_struct_0(B_453)))) | ~m1_subset_1(u1_struct_0(B_453), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~m1_pre_topc(B_453, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_9139, c_10081])).
% 28.61/16.53  tff(c_10272, plain, (![B_453]: (v1_funct_2(k9_tmap_1('#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0(k6_tmap_1('#skF_5', u1_struct_0(B_453)))) | ~m1_subset_1(u1_struct_0(B_453), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5') | ~m1_pre_topc(B_453, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_78, c_78, c_76, c_10093])).
% 28.61/16.53  tff(c_10292, plain, (![B_454]: (v1_funct_2(k9_tmap_1('#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0(k6_tmap_1('#skF_5', u1_struct_0(B_454)))) | ~m1_subset_1(u1_struct_0(B_454), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc(B_454, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_80, c_10272])).
% 28.61/16.53  tff(c_10364, plain, (v1_funct_2(k9_tmap_1('#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0(k6_tmap_1('#skF_5', '#skF_4'('#skF_5', '#skF_6')))) | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_180, c_10292])).
% 28.61/16.53  tff(c_10379, plain, (v1_funct_2(k9_tmap_1('#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0(k6_tmap_1('#skF_5', '#skF_4'('#skF_5', '#skF_6')))) | ~m1_subset_1('#skF_4'('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_180, c_10364])).
% 28.61/16.53  tff(c_10425, plain, (~m1_subset_1('#skF_4'('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_10379])).
% 28.61/16.53  tff(c_10428, plain, (~m1_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_196, c_10425])).
% 28.61/16.53  tff(c_10435, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_10428])).
% 28.61/16.53  tff(c_10437, plain, (m1_subset_1('#skF_4'('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_10379])).
% 28.61/16.53  tff(c_10446, plain, (k7_tmap_1('#skF_5', '#skF_4'('#skF_5', '#skF_6'))=k6_partfun1(u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_10437, c_14])).
% 28.61/16.53  tff(c_10460, plain, (k7_tmap_1('#skF_5', '#skF_4'('#skF_5', '#skF_6'))=k9_tmap_1('#skF_5', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_9139, c_10446])).
% 28.61/16.53  tff(c_10461, plain, (k7_tmap_1('#skF_5', '#skF_4'('#skF_5', '#skF_6'))=k9_tmap_1('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_80, c_10460])).
% 28.61/16.53  tff(c_66, plain, (![A_77, B_79]: (v5_pre_topc(k7_tmap_1(A_77, B_79), A_77, k6_tmap_1(A_77, B_79)) | ~v3_pre_topc(B_79, A_77) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_223])).
% 28.61/16.53  tff(c_10921, plain, (v5_pre_topc(k9_tmap_1('#skF_5', '#skF_6'), '#skF_5', k6_tmap_1('#skF_5', '#skF_4'('#skF_5', '#skF_6'))) | ~v3_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5') | ~m1_subset_1('#skF_4'('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_10461, c_66])).
% 28.61/16.53  tff(c_10958, plain, (v5_pre_topc(k9_tmap_1('#skF_5', '#skF_6'), '#skF_5', k6_tmap_1('#skF_5', '#skF_4'('#skF_5', '#skF_6'))) | ~v3_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_10437, c_10921])).
% 28.61/16.53  tff(c_10959, plain, (v5_pre_topc(k9_tmap_1('#skF_5', '#skF_6'), '#skF_5', k6_tmap_1('#skF_5', '#skF_4'('#skF_5', '#skF_6'))) | ~v3_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_80, c_10958])).
% 28.61/16.53  tff(c_11106, plain, (~v3_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_10959])).
% 28.61/16.53  tff(c_3371, plain, (![B_296, A_297]: (v3_pre_topc(B_296, A_297) | ~m1_subset_1(k7_tmap_1(A_297, B_296), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_297), u1_struct_0(k6_tmap_1(A_297, B_296))))) | ~v5_pre_topc(k7_tmap_1(A_297, B_296), A_297, k6_tmap_1(A_297, B_296)) | ~v1_funct_2(k7_tmap_1(A_297, B_296), u1_struct_0(A_297), u1_struct_0(k6_tmap_1(A_297, B_296))) | ~v1_funct_1(k7_tmap_1(A_297, B_296)) | ~m1_subset_1(B_296, k1_zfmisc_1(u1_struct_0(A_297))) | ~l1_pre_topc(A_297) | ~v2_pre_topc(A_297) | v2_struct_0(A_297))), inference(cnfTransformation, [status(thm)], [f_223])).
% 28.61/16.53  tff(c_4614, plain, (![B_324, A_325]: (v3_pre_topc(B_324, A_325) | ~v5_pre_topc(k7_tmap_1(A_325, B_324), A_325, k6_tmap_1(A_325, B_324)) | ~v1_funct_2(k7_tmap_1(A_325, B_324), u1_struct_0(A_325), u1_struct_0(k6_tmap_1(A_325, B_324))) | ~v1_funct_1(k7_tmap_1(A_325, B_324)) | ~m1_subset_1(B_324, k1_zfmisc_1(u1_struct_0(A_325))) | ~l1_pre_topc(A_325) | ~v2_pre_topc(A_325) | v2_struct_0(A_325))), inference(resolution, [status(thm)], [c_40, c_3371])).
% 28.61/16.53  tff(c_4735, plain, (![B_69, A_68]: (v3_pre_topc(B_69, A_68) | ~v5_pre_topc(k7_tmap_1(A_68, B_69), A_68, k6_tmap_1(A_68, B_69)) | ~v1_funct_1(k7_tmap_1(A_68, B_69)) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68) | ~v2_pre_topc(A_68) | v2_struct_0(A_68))), inference(resolution, [status(thm)], [c_42, c_4614])).
% 28.61/16.53  tff(c_10909, plain, (v3_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5') | ~v5_pre_topc(k9_tmap_1('#skF_5', '#skF_6'), '#skF_5', k6_tmap_1('#skF_5', '#skF_4'('#skF_5', '#skF_6'))) | ~v1_funct_1(k7_tmap_1('#skF_5', '#skF_4'('#skF_5', '#skF_6'))) | ~m1_subset_1('#skF_4'('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_10461, c_4735])).
% 28.61/16.53  tff(c_10946, plain, (v3_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5') | ~v5_pre_topc(k9_tmap_1('#skF_5', '#skF_6'), '#skF_5', k6_tmap_1('#skF_5', '#skF_4'('#skF_5', '#skF_6'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_10437, c_120, c_10461, c_10909])).
% 28.61/16.53  tff(c_10947, plain, (v3_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5') | ~v5_pre_topc(k9_tmap_1('#skF_5', '#skF_6'), '#skF_5', k6_tmap_1('#skF_5', '#skF_4'('#skF_5', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_80, c_10946])).
% 28.61/16.53  tff(c_11121, plain, (~v5_pre_topc(k9_tmap_1('#skF_5', '#skF_6'), '#skF_5', k6_tmap_1('#skF_5', '#skF_4'('#skF_5', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_11106, c_10947])).
% 28.61/16.53  tff(c_11124, plain, (~v5_pre_topc(k9_tmap_1('#skF_5', '#skF_6'), '#skF_5', k8_tmap_1('#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2622, c_11121])).
% 28.61/16.53  tff(c_11126, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_121, c_11124])).
% 28.61/16.53  tff(c_11128, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_11126])).
% 28.61/16.53  tff(c_11130, plain, (v3_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5')), inference(splitRight, [status(thm)], [c_10959])).
% 28.61/16.53  tff(c_34, plain, (![A_58, B_64]: (~v3_pre_topc('#skF_4'(A_58, B_64), A_58) | v1_tsep_1(B_64, A_58) | ~m1_pre_topc(B_64, A_58) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_144])).
% 28.61/16.53  tff(c_11133, plain, (v1_tsep_1('#skF_6', '#skF_5') | ~m1_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_11130, c_34])).
% 28.61/16.53  tff(c_11136, plain, (v1_tsep_1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_11133])).
% 28.61/16.53  tff(c_11138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_174, c_11136])).
% 28.61/16.53  tff(c_11140, plain, (k6_partfun1(u1_struct_0('#skF_5'))!=k9_tmap_1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_9134])).
% 28.61/16.53  tff(c_2714, plain, (v1_funct_2(k9_tmap_1('#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2709, c_125])).
% 28.61/16.53  tff(c_2713, plain, (m1_subset_1(k9_tmap_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_2709, c_129])).
% 28.61/16.53  tff(c_3935, plain, (![A_309, B_310]: (r1_funct_2(u1_struct_0(A_309), u1_struct_0(k8_tmap_1(A_309, B_310)), u1_struct_0(A_309), u1_struct_0(k6_tmap_1(A_309, u1_struct_0(B_310))), k9_tmap_1(A_309, B_310), k7_tmap_1(A_309, u1_struct_0(B_310))) | ~m1_subset_1(u1_struct_0(B_310), k1_zfmisc_1(u1_struct_0(A_309))) | ~m1_subset_1(k9_tmap_1(A_309, B_310), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_309), u1_struct_0(k8_tmap_1(A_309, B_310))))) | ~v1_funct_2(k9_tmap_1(A_309, B_310), u1_struct_0(A_309), u1_struct_0(k8_tmap_1(A_309, B_310))) | ~v1_funct_1(k9_tmap_1(A_309, B_310)) | ~m1_pre_topc(B_310, A_309) | ~l1_pre_topc(A_309) | ~v2_pre_topc(A_309) | v2_struct_0(A_309))), inference(cnfTransformation, [status(thm)], [f_130])).
% 28.61/16.53  tff(c_3970, plain, (r1_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), u1_struct_0(k6_tmap_1('#skF_5', u1_struct_0('#skF_6'))), k9_tmap_1('#skF_5', '#skF_6'), k7_tmap_1('#skF_5', u1_struct_0('#skF_6'))) | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(k9_tmap_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', '#skF_6'))))) | ~v1_funct_2(k9_tmap_1('#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', '#skF_6'))) | ~v1_funct_1(k9_tmap_1('#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2709, c_3935])).
% 28.61/16.53  tff(c_4108, plain, (r1_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), u1_struct_0(k6_tmap_1('#skF_5', '#skF_4'('#skF_5', '#skF_6'))), k9_tmap_1('#skF_5', '#skF_6'), k7_tmap_1('#skF_5', '#skF_4'('#skF_5', '#skF_6'))) | ~m1_subset_1('#skF_4'('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_120, c_2714, c_2709, c_2713, c_2709, c_180, c_180, c_180, c_3970])).
% 28.61/16.53  tff(c_4109, plain, (r1_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), u1_struct_0(k6_tmap_1('#skF_5', '#skF_4'('#skF_5', '#skF_6'))), k9_tmap_1('#skF_5', '#skF_6'), k7_tmap_1('#skF_5', '#skF_4'('#skF_5', '#skF_6'))) | ~m1_subset_1('#skF_4'('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_80, c_4108])).
% 28.61/16.53  tff(c_12750, plain, (~m1_subset_1('#skF_4'('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_4109])).
% 28.61/16.53  tff(c_12753, plain, (~m1_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_196, c_12750])).
% 28.61/16.53  tff(c_12760, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_12753])).
% 28.61/16.53  tff(c_12762, plain, (m1_subset_1('#skF_4'('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_4109])).
% 28.61/16.53  tff(c_12768, plain, (u1_struct_0(k6_tmap_1('#skF_5', '#skF_4'('#skF_5', '#skF_6')))=u1_struct_0('#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_12762, c_60])).
% 28.61/16.53  tff(c_12781, plain, (u1_struct_0(k6_tmap_1('#skF_5', '#skF_4'('#skF_5', '#skF_6')))=u1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_12768])).
% 28.61/16.53  tff(c_12782, plain, (u1_struct_0(k6_tmap_1('#skF_5', '#skF_4'('#skF_5', '#skF_6')))=u1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_80, c_12781])).
% 28.61/16.53  tff(c_12771, plain, (k7_tmap_1('#skF_5', '#skF_4'('#skF_5', '#skF_6'))=k6_partfun1(u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_12762, c_14])).
% 28.61/16.53  tff(c_12785, plain, (k7_tmap_1('#skF_5', '#skF_4'('#skF_5', '#skF_6'))=k6_partfun1(u1_struct_0('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_12771])).
% 28.61/16.53  tff(c_12786, plain, (k7_tmap_1('#skF_5', '#skF_4'('#skF_5', '#skF_6'))=k6_partfun1(u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_80, c_12785])).
% 28.61/16.53  tff(c_12761, plain, (r1_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), u1_struct_0(k6_tmap_1('#skF_5', '#skF_4'('#skF_5', '#skF_6'))), k9_tmap_1('#skF_5', '#skF_6'), k7_tmap_1('#skF_5', '#skF_4'('#skF_5', '#skF_6')))), inference(splitRight, [status(thm)], [c_4109])).
% 28.61/16.53  tff(c_14690, plain, (r1_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), k9_tmap_1('#skF_5', '#skF_6'), k6_partfun1(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_12782, c_12786, c_12761])).
% 28.61/16.53  tff(c_12, plain, (![B_6, C_7, E_9, D_8, A_5, F_10]: (F_10=E_9 | ~r1_funct_2(A_5, B_6, C_7, D_8, E_9, F_10) | ~m1_subset_1(F_10, k1_zfmisc_1(k2_zfmisc_1(C_7, D_8))) | ~v1_funct_2(F_10, C_7, D_8) | ~v1_funct_1(F_10) | ~m1_subset_1(E_9, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))) | ~v1_funct_2(E_9, A_5, B_6) | ~v1_funct_1(E_9) | v1_xboole_0(D_8) | v1_xboole_0(B_6))), inference(cnfTransformation, [status(thm)], [f_66])).
% 28.61/16.53  tff(c_14692, plain, (k6_partfun1(u1_struct_0('#skF_5'))=k9_tmap_1('#skF_5', '#skF_6') | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_5')))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_5')) | ~v1_funct_1(k6_partfun1(u1_struct_0('#skF_5'))) | ~m1_subset_1(k9_tmap_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_5')))) | ~v1_funct_2(k9_tmap_1('#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0('#skF_5')) | ~v1_funct_1(k9_tmap_1('#skF_5', '#skF_6')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_14690, c_12])).
% 28.61/16.53  tff(c_14695, plain, (k6_partfun1(u1_struct_0('#skF_5'))=k9_tmap_1('#skF_5', '#skF_6') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_2714, c_2713, c_562, c_3144, c_3139, c_14692])).
% 28.61/16.53  tff(c_14697, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2712, c_11140, c_14695])).
% 28.61/16.53  tff(c_14699, plain, (~m1_subset_1(k9_tmap_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', '#skF_6')))))), inference(splitRight, [status(thm)], [c_92])).
% 28.61/16.53  tff(c_15068, plain, (~m1_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_15065, c_14699])).
% 28.61/16.53  tff(c_15080, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_15068])).
% 28.61/16.53  tff(c_15082, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_15080])).
% 28.61/16.53  tff(c_15084, plain, (~v1_funct_2(k9_tmap_1('#skF_5', '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', '#skF_6')))), inference(splitRight, [status(thm)], [c_104])).
% 28.61/16.53  tff(c_15309, plain, (~m1_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_15306, c_15084])).
% 28.61/16.53  tff(c_15318, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_15309])).
% 28.61/16.53  tff(c_15320, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_15318])).
% 28.61/16.53  tff(c_15321, plain, (v1_tsep_1('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_98])).
% 28.61/16.53  tff(c_15488, plain, (![B_653, A_654]: (v3_pre_topc(u1_struct_0(B_653), A_654) | ~m1_subset_1(u1_struct_0(B_653), k1_zfmisc_1(u1_struct_0(A_654))) | ~v1_tsep_1(B_653, A_654) | ~m1_pre_topc(B_653, A_654) | ~l1_pre_topc(A_654))), inference(cnfTransformation, [status(thm)], [f_144])).
% 28.61/16.53  tff(c_15504, plain, (![B_82, A_80]: (v3_pre_topc(u1_struct_0(B_82), A_80) | ~v1_tsep_1(B_82, A_80) | ~m1_pre_topc(B_82, A_80) | ~l1_pre_topc(A_80))), inference(resolution, [status(thm)], [c_72, c_15488])).
% 28.61/16.53  tff(c_15397, plain, (![A_646, B_647]: (k7_tmap_1(A_646, B_647)=k6_partfun1(u1_struct_0(A_646)) | ~m1_subset_1(B_647, k1_zfmisc_1(u1_struct_0(A_646))) | ~l1_pre_topc(A_646) | ~v2_pre_topc(A_646) | v2_struct_0(A_646))), inference(cnfTransformation, [status(thm)], [f_78])).
% 28.61/16.53  tff(c_15411, plain, (![A_80, B_82]: (k7_tmap_1(A_80, u1_struct_0(B_82))=k6_partfun1(u1_struct_0(A_80)) | ~v2_pre_topc(A_80) | v2_struct_0(A_80) | ~m1_pre_topc(B_82, A_80) | ~l1_pre_topc(A_80))), inference(resolution, [status(thm)], [c_72, c_15397])).
% 28.61/16.53  tff(c_15351, plain, (![A_643, B_644]: (u1_struct_0(k6_tmap_1(A_643, B_644))=u1_struct_0(A_643) | ~m1_subset_1(B_644, k1_zfmisc_1(u1_struct_0(A_643))) | ~l1_pre_topc(A_643) | ~v2_pre_topc(A_643) | v2_struct_0(A_643))), inference(cnfTransformation, [status(thm)], [f_203])).
% 28.61/16.53  tff(c_15362, plain, (![A_80, B_82]: (u1_struct_0(k6_tmap_1(A_80, u1_struct_0(B_82)))=u1_struct_0(A_80) | ~v2_pre_topc(A_80) | v2_struct_0(A_80) | ~m1_pre_topc(B_82, A_80) | ~l1_pre_topc(A_80))), inference(resolution, [status(thm)], [c_72, c_15351])).
% 28.61/16.53  tff(c_15678, plain, (![A_678, B_679]: (v1_funct_2(k7_tmap_1(A_678, B_679), u1_struct_0(A_678), u1_struct_0(k6_tmap_1(A_678, B_679))) | ~m1_subset_1(B_679, k1_zfmisc_1(u1_struct_0(A_678))) | ~l1_pre_topc(A_678) | ~v2_pre_topc(A_678) | v2_struct_0(A_678))), inference(cnfTransformation, [status(thm)], [f_159])).
% 28.61/16.53  tff(c_17334, plain, (![A_814, B_815]: (v1_funct_2(k7_tmap_1(A_814, u1_struct_0(B_815)), u1_struct_0(A_814), u1_struct_0(A_814)) | ~m1_subset_1(u1_struct_0(B_815), k1_zfmisc_1(u1_struct_0(A_814))) | ~l1_pre_topc(A_814) | ~v2_pre_topc(A_814) | v2_struct_0(A_814) | ~v2_pre_topc(A_814) | v2_struct_0(A_814) | ~m1_pre_topc(B_815, A_814) | ~l1_pre_topc(A_814))), inference(superposition, [status(thm), theory('equality')], [c_15362, c_15678])).
% 28.61/16.53  tff(c_25282, plain, (![A_1164, B_1165]: (v1_funct_2(k6_partfun1(u1_struct_0(A_1164)), u1_struct_0(A_1164), u1_struct_0(A_1164)) | ~m1_subset_1(u1_struct_0(B_1165), k1_zfmisc_1(u1_struct_0(A_1164))) | ~l1_pre_topc(A_1164) | ~v2_pre_topc(A_1164) | v2_struct_0(A_1164) | ~v2_pre_topc(A_1164) | v2_struct_0(A_1164) | ~m1_pre_topc(B_1165, A_1164) | ~l1_pre_topc(A_1164) | ~v2_pre_topc(A_1164) | v2_struct_0(A_1164) | ~m1_pre_topc(B_1165, A_1164) | ~l1_pre_topc(A_1164))), inference(superposition, [status(thm), theory('equality')], [c_15411, c_17334])).
% 28.61/16.53  tff(c_25358, plain, (![A_1166, B_1167]: (v1_funct_2(k6_partfun1(u1_struct_0(A_1166)), u1_struct_0(A_1166), u1_struct_0(A_1166)) | ~v2_pre_topc(A_1166) | v2_struct_0(A_1166) | ~m1_pre_topc(B_1167, A_1166) | ~l1_pre_topc(A_1166))), inference(resolution, [status(thm)], [c_72, c_25282])).
% 28.61/16.53  tff(c_25360, plain, (v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_5')) | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_74, c_25358])).
% 28.61/16.53  tff(c_25363, plain, (v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_78, c_25360])).
% 28.61/16.53  tff(c_25364, plain, (v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_80, c_25363])).
% 28.61/16.53  tff(c_16201, plain, (![A_741, B_742]: (k6_tmap_1(A_741, u1_struct_0(B_742))=k8_tmap_1(A_741, B_742) | ~m1_subset_1(u1_struct_0(B_742), k1_zfmisc_1(u1_struct_0(A_741))) | ~l1_pre_topc(k8_tmap_1(A_741, B_742)) | ~v2_pre_topc(k8_tmap_1(A_741, B_742)) | ~v1_pre_topc(k8_tmap_1(A_741, B_742)) | ~m1_pre_topc(B_742, A_741) | ~l1_pre_topc(A_741) | ~v2_pre_topc(A_741) | v2_struct_0(A_741))), inference(cnfTransformation, [status(thm)], [f_104])).
% 28.61/16.53  tff(c_16399, plain, (![A_758, B_759]: (k6_tmap_1(A_758, u1_struct_0(B_759))=k8_tmap_1(A_758, B_759) | ~l1_pre_topc(k8_tmap_1(A_758, B_759)) | ~v2_pre_topc(k8_tmap_1(A_758, B_759)) | ~v1_pre_topc(k8_tmap_1(A_758, B_759)) | ~v2_pre_topc(A_758) | v2_struct_0(A_758) | ~m1_pre_topc(B_759, A_758) | ~l1_pre_topc(A_758))), inference(resolution, [status(thm)], [c_72, c_16201])).
% 28.61/16.53  tff(c_16404, plain, (![A_760, B_761]: (k6_tmap_1(A_760, u1_struct_0(B_761))=k8_tmap_1(A_760, B_761) | ~l1_pre_topc(k8_tmap_1(A_760, B_761)) | ~v1_pre_topc(k8_tmap_1(A_760, B_761)) | ~m1_pre_topc(B_761, A_760) | ~l1_pre_topc(A_760) | ~v2_pre_topc(A_760) | v2_struct_0(A_760))), inference(resolution, [status(thm)], [c_48, c_16399])).
% 28.61/16.53  tff(c_16409, plain, (![A_762, B_763]: (k6_tmap_1(A_762, u1_struct_0(B_763))=k8_tmap_1(A_762, B_763) | ~l1_pre_topc(k8_tmap_1(A_762, B_763)) | ~m1_pre_topc(B_763, A_762) | ~l1_pre_topc(A_762) | ~v2_pre_topc(A_762) | v2_struct_0(A_762))), inference(resolution, [status(thm)], [c_50, c_16404])).
% 28.61/16.53  tff(c_16414, plain, (![A_764, B_765]: (k6_tmap_1(A_764, u1_struct_0(B_765))=k8_tmap_1(A_764, B_765) | ~m1_pre_topc(B_765, A_764) | ~l1_pre_topc(A_764) | ~v2_pre_topc(A_764) | v2_struct_0(A_764))), inference(resolution, [status(thm)], [c_46, c_16409])).
% 28.61/16.53  tff(c_16457, plain, (![A_764, B_765]: (u1_struct_0(k8_tmap_1(A_764, B_765))=u1_struct_0(A_764) | ~v2_pre_topc(A_764) | v2_struct_0(A_764) | ~m1_pre_topc(B_765, A_764) | ~l1_pre_topc(A_764) | ~m1_pre_topc(B_765, A_764) | ~l1_pre_topc(A_764) | ~v2_pre_topc(A_764) | v2_struct_0(A_764))), inference(superposition, [status(thm), theory('equality')], [c_16414, c_15362])).
% 28.61/16.53  tff(c_15816, plain, (![A_686, B_687]: (m1_subset_1(k7_tmap_1(A_686, B_687), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_686), u1_struct_0(k6_tmap_1(A_686, B_687))))) | ~m1_subset_1(B_687, k1_zfmisc_1(u1_struct_0(A_686))) | ~l1_pre_topc(A_686) | ~v2_pre_topc(A_686) | v2_struct_0(A_686))), inference(cnfTransformation, [status(thm)], [f_159])).
% 28.61/16.53  tff(c_18515, plain, (![A_891, B_892]: (m1_subset_1(k7_tmap_1(A_891, u1_struct_0(B_892)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_891), u1_struct_0(A_891)))) | ~m1_subset_1(u1_struct_0(B_892), k1_zfmisc_1(u1_struct_0(A_891))) | ~l1_pre_topc(A_891) | ~v2_pre_topc(A_891) | v2_struct_0(A_891) | ~v2_pre_topc(A_891) | v2_struct_0(A_891) | ~m1_pre_topc(B_892, A_891) | ~l1_pre_topc(A_891))), inference(superposition, [status(thm), theory('equality')], [c_15362, c_15816])).
% 28.61/16.53  tff(c_26963, plain, (![A_1263, B_1264]: (m1_subset_1(k6_partfun1(u1_struct_0(A_1263)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1263), u1_struct_0(A_1263)))) | ~m1_subset_1(u1_struct_0(B_1264), k1_zfmisc_1(u1_struct_0(A_1263))) | ~l1_pre_topc(A_1263) | ~v2_pre_topc(A_1263) | v2_struct_0(A_1263) | ~v2_pre_topc(A_1263) | v2_struct_0(A_1263) | ~m1_pre_topc(B_1264, A_1263) | ~l1_pre_topc(A_1263) | ~v2_pre_topc(A_1263) | v2_struct_0(A_1263) | ~m1_pre_topc(B_1264, A_1263) | ~l1_pre_topc(A_1263))), inference(superposition, [status(thm), theory('equality')], [c_15411, c_18515])).
% 28.61/16.53  tff(c_27843, plain, (![A_1268, B_1269]: (m1_subset_1(k6_partfun1(u1_struct_0(A_1268)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1268), u1_struct_0(A_1268)))) | ~v2_pre_topc(A_1268) | v2_struct_0(A_1268) | ~m1_pre_topc(B_1269, A_1268) | ~l1_pre_topc(A_1268))), inference(resolution, [status(thm)], [c_72, c_26963])).
% 28.61/16.53  tff(c_27845, plain, (m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_5')))) | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_74, c_27843])).
% 28.61/16.53  tff(c_27848, plain, (m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_5')))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_78, c_27845])).
% 28.61/16.53  tff(c_27849, plain, (m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_80, c_27848])).
% 28.61/16.53  tff(c_15413, plain, (![A_648]: (k7_tmap_1(A_648, '#skF_1'(A_648))=k6_partfun1(u1_struct_0(A_648)) | ~v2_pre_topc(A_648) | v2_struct_0(A_648) | ~l1_pre_topc(A_648))), inference(resolution, [status(thm)], [c_8, c_15397])).
% 28.61/16.53  tff(c_15336, plain, (![A_638, B_639]: (v1_funct_1(k7_tmap_1(A_638, B_639)) | ~m1_subset_1(B_639, k1_zfmisc_1(u1_struct_0(A_638))) | ~l1_pre_topc(A_638) | ~v2_pre_topc(A_638) | v2_struct_0(A_638))), inference(cnfTransformation, [status(thm)], [f_159])).
% 28.61/16.53  tff(c_15348, plain, (![A_3]: (v1_funct_1(k7_tmap_1(A_3, '#skF_1'(A_3))) | ~v2_pre_topc(A_3) | v2_struct_0(A_3) | ~l1_pre_topc(A_3))), inference(resolution, [status(thm)], [c_8, c_15336])).
% 28.61/16.53  tff(c_15419, plain, (![A_648]: (v1_funct_1(k6_partfun1(u1_struct_0(A_648))) | ~v2_pre_topc(A_648) | v2_struct_0(A_648) | ~l1_pre_topc(A_648) | ~v2_pre_topc(A_648) | v2_struct_0(A_648) | ~l1_pre_topc(A_648))), inference(superposition, [status(thm), theory('equality')], [c_15413, c_15348])).
% 28.61/16.53  tff(c_10, plain, (![B_6, C_7, D_8, A_5, F_10]: (r1_funct_2(A_5, B_6, C_7, D_8, F_10, F_10) | ~m1_subset_1(F_10, k1_zfmisc_1(k2_zfmisc_1(C_7, D_8))) | ~v1_funct_2(F_10, C_7, D_8) | ~m1_subset_1(F_10, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))) | ~v1_funct_2(F_10, A_5, B_6) | ~v1_funct_1(F_10) | v1_xboole_0(D_8) | v1_xboole_0(B_6))), inference(cnfTransformation, [status(thm)], [f_66])).
% 28.61/16.53  tff(c_27851, plain, (![A_5, B_6]: (r1_funct_2(A_5, B_6, u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), k6_partfun1(u1_struct_0('#skF_5')), k6_partfun1(u1_struct_0('#skF_5'))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_5')) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')), k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')), A_5, B_6) | ~v1_funct_1(k6_partfun1(u1_struct_0('#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_5')) | v1_xboole_0(B_6))), inference(resolution, [status(thm)], [c_27849, c_10])).
% 28.61/16.53  tff(c_27854, plain, (![A_5, B_6]: (r1_funct_2(A_5, B_6, u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), k6_partfun1(u1_struct_0('#skF_5')), k6_partfun1(u1_struct_0('#skF_5'))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')), k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')), A_5, B_6) | ~v1_funct_1(k6_partfun1(u1_struct_0('#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_5')) | v1_xboole_0(B_6))), inference(demodulation, [status(thm), theory('equality')], [c_25364, c_27851])).
% 28.61/16.53  tff(c_27855, plain, (~v1_funct_1(k6_partfun1(u1_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_27854])).
% 28.61/16.53  tff(c_27858, plain, (~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_15419, c_27855])).
% 28.61/16.53  tff(c_27861, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_78, c_27858])).
% 28.61/16.53  tff(c_27863, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_27861])).
% 28.61/16.53  tff(c_27864, plain, (![A_5, B_6]: (v1_xboole_0(u1_struct_0('#skF_5')) | r1_funct_2(A_5, B_6, u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), k6_partfun1(u1_struct_0('#skF_5')), k6_partfun1(u1_struct_0('#skF_5'))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')), k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')), A_5, B_6) | v1_xboole_0(B_6))), inference(splitRight, [status(thm)], [c_27854])).
% 28.61/16.53  tff(c_27866, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_27864])).
% 28.61/16.53  tff(c_27869, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_27866, c_4])).
% 28.61/16.53  tff(c_27872, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_80, c_27869])).
% 28.61/16.53  tff(c_27875, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_2, c_27872])).
% 28.61/16.53  tff(c_27879, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_27875])).
% 28.61/16.53  tff(c_27881, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_27864])).
% 28.61/16.53  tff(c_27880, plain, (![A_5, B_6]: (r1_funct_2(A_5, B_6, u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), k6_partfun1(u1_struct_0('#skF_5')), k6_partfun1(u1_struct_0('#skF_5'))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')), k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')), A_5, B_6) | v1_xboole_0(B_6))), inference(splitRight, [status(thm)], [c_27864])).
% 28.61/16.53  tff(c_16413, plain, (![A_70, B_71]: (k6_tmap_1(A_70, u1_struct_0(B_71))=k8_tmap_1(A_70, B_71) | ~m1_pre_topc(B_71, A_70) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70) | v2_struct_0(A_70))), inference(resolution, [status(thm)], [c_46, c_16409])).
% 28.61/16.53  tff(c_18417, plain, (![A_886, B_887]: (v1_funct_2(k6_partfun1(u1_struct_0(A_886)), u1_struct_0(A_886), u1_struct_0(k6_tmap_1(A_886, u1_struct_0(B_887)))) | ~m1_subset_1(u1_struct_0(B_887), k1_zfmisc_1(u1_struct_0(A_886))) | ~l1_pre_topc(A_886) | ~v2_pre_topc(A_886) | v2_struct_0(A_886) | ~v2_pre_topc(A_886) | v2_struct_0(A_886) | ~m1_pre_topc(B_887, A_886) | ~l1_pre_topc(A_886))), inference(superposition, [status(thm), theory('equality')], [c_15411, c_15678])).
% 28.61/16.53  tff(c_18456, plain, (![A_70, B_71]: (v1_funct_2(k6_partfun1(u1_struct_0(A_70)), u1_struct_0(A_70), u1_struct_0(k8_tmap_1(A_70, B_71))) | ~m1_subset_1(u1_struct_0(B_71), k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70) | v2_struct_0(A_70) | ~v2_pre_topc(A_70) | v2_struct_0(A_70) | ~m1_pre_topc(B_71, A_70) | ~l1_pre_topc(A_70) | ~m1_pre_topc(B_71, A_70) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70) | v2_struct_0(A_70))), inference(superposition, [status(thm), theory('equality')], [c_16413, c_18417])).
% 28.61/16.53  tff(c_19938, plain, (![A_953, B_954]: (m1_subset_1(k6_partfun1(u1_struct_0(A_953)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_953), u1_struct_0(k6_tmap_1(A_953, u1_struct_0(B_954)))))) | ~m1_subset_1(u1_struct_0(B_954), k1_zfmisc_1(u1_struct_0(A_953))) | ~l1_pre_topc(A_953) | ~v2_pre_topc(A_953) | v2_struct_0(A_953) | ~v2_pre_topc(A_953) | v2_struct_0(A_953) | ~m1_pre_topc(B_954, A_953) | ~l1_pre_topc(A_953))), inference(superposition, [status(thm), theory('equality')], [c_15411, c_15816])).
% 28.61/16.53  tff(c_33636, plain, (![A_1464, B_1465]: (m1_subset_1(k6_partfun1(u1_struct_0(A_1464)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1464), u1_struct_0(k8_tmap_1(A_1464, B_1465))))) | ~m1_subset_1(u1_struct_0(B_1465), k1_zfmisc_1(u1_struct_0(A_1464))) | ~l1_pre_topc(A_1464) | ~v2_pre_topc(A_1464) | v2_struct_0(A_1464) | ~v2_pre_topc(A_1464) | v2_struct_0(A_1464) | ~m1_pre_topc(B_1465, A_1464) | ~l1_pre_topc(A_1464) | ~m1_pre_topc(B_1465, A_1464) | ~l1_pre_topc(A_1464) | ~v2_pre_topc(A_1464) | v2_struct_0(A_1464))), inference(superposition, [status(thm), theory('equality')], [c_16413, c_19938])).
% 28.61/16.53  tff(c_28, plain, (![B_48, A_36, C_54]: (u1_struct_0(B_48)='#skF_3'(A_36, B_48, C_54) | k9_tmap_1(A_36, B_48)=C_54 | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_36), u1_struct_0(k8_tmap_1(A_36, B_48))))) | ~v1_funct_2(C_54, u1_struct_0(A_36), u1_struct_0(k8_tmap_1(A_36, B_48))) | ~v1_funct_1(C_54) | ~m1_pre_topc(B_48, A_36) | ~l1_pre_topc(A_36) | ~v2_pre_topc(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_130])).
% 28.61/16.53  tff(c_37085, plain, (![A_1566, B_1567]: ('#skF_3'(A_1566, B_1567, k6_partfun1(u1_struct_0(A_1566)))=u1_struct_0(B_1567) | k9_tmap_1(A_1566, B_1567)=k6_partfun1(u1_struct_0(A_1566)) | ~v1_funct_2(k6_partfun1(u1_struct_0(A_1566)), u1_struct_0(A_1566), u1_struct_0(k8_tmap_1(A_1566, B_1567))) | ~v1_funct_1(k6_partfun1(u1_struct_0(A_1566))) | ~m1_subset_1(u1_struct_0(B_1567), k1_zfmisc_1(u1_struct_0(A_1566))) | ~m1_pre_topc(B_1567, A_1566) | ~l1_pre_topc(A_1566) | ~v2_pre_topc(A_1566) | v2_struct_0(A_1566))), inference(resolution, [status(thm)], [c_33636, c_28])).
% 28.61/16.53  tff(c_37234, plain, (![A_1568, B_1569]: ('#skF_3'(A_1568, B_1569, k6_partfun1(u1_struct_0(A_1568)))=u1_struct_0(B_1569) | k9_tmap_1(A_1568, B_1569)=k6_partfun1(u1_struct_0(A_1568)) | ~v1_funct_1(k6_partfun1(u1_struct_0(A_1568))) | ~m1_subset_1(u1_struct_0(B_1569), k1_zfmisc_1(u1_struct_0(A_1568))) | ~m1_pre_topc(B_1569, A_1568) | ~l1_pre_topc(A_1568) | ~v2_pre_topc(A_1568) | v2_struct_0(A_1568))), inference(resolution, [status(thm)], [c_18456, c_37085])).
% 28.61/16.53  tff(c_37330, plain, (![A_1570, B_1571]: ('#skF_3'(A_1570, B_1571, k6_partfun1(u1_struct_0(A_1570)))=u1_struct_0(B_1571) | k9_tmap_1(A_1570, B_1571)=k6_partfun1(u1_struct_0(A_1570)) | ~v1_funct_1(k6_partfun1(u1_struct_0(A_1570))) | ~v2_pre_topc(A_1570) | v2_struct_0(A_1570) | ~m1_pre_topc(B_1571, A_1570) | ~l1_pre_topc(A_1570))), inference(resolution, [status(thm)], [c_72, c_37234])).
% 28.61/16.53  tff(c_37515, plain, (![A_1574, B_1575]: ('#skF_3'(A_1574, B_1575, k6_partfun1(u1_struct_0(A_1574)))=u1_struct_0(B_1575) | k9_tmap_1(A_1574, B_1575)=k6_partfun1(u1_struct_0(A_1574)) | ~m1_pre_topc(B_1575, A_1574) | ~v2_pre_topc(A_1574) | v2_struct_0(A_1574) | ~l1_pre_topc(A_1574))), inference(resolution, [status(thm)], [c_15419, c_37330])).
% 28.61/16.53  tff(c_27865, plain, (v1_funct_1(k6_partfun1(u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_27854])).
% 28.61/16.53  tff(c_37340, plain, (![B_1571]: ('#skF_3'('#skF_5', B_1571, k6_partfun1(u1_struct_0('#skF_5')))=u1_struct_0(B_1571) | k9_tmap_1('#skF_5', B_1571)=k6_partfun1(u1_struct_0('#skF_5')) | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~m1_pre_topc(B_1571, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_27865, c_37330])).
% 28.61/16.53  tff(c_37383, plain, (![B_1571]: ('#skF_3'('#skF_5', B_1571, k6_partfun1(u1_struct_0('#skF_5')))=u1_struct_0(B_1571) | k9_tmap_1('#skF_5', B_1571)=k6_partfun1(u1_struct_0('#skF_5')) | v2_struct_0('#skF_5') | ~m1_pre_topc(B_1571, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_78, c_37340])).
% 28.61/16.53  tff(c_37386, plain, (![B_1572]: ('#skF_3'('#skF_5', B_1572, k6_partfun1(u1_struct_0('#skF_5')))=u1_struct_0(B_1572) | k9_tmap_1('#skF_5', B_1572)=k6_partfun1(u1_struct_0('#skF_5')) | ~m1_pre_topc(B_1572, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_80, c_37383])).
% 28.61/16.53  tff(c_26, plain, (![A_36, B_48, C_54]: (~r1_funct_2(u1_struct_0(A_36), u1_struct_0(k8_tmap_1(A_36, B_48)), u1_struct_0(A_36), u1_struct_0(k6_tmap_1(A_36, '#skF_3'(A_36, B_48, C_54))), C_54, k7_tmap_1(A_36, '#skF_3'(A_36, B_48, C_54))) | k9_tmap_1(A_36, B_48)=C_54 | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_36), u1_struct_0(k8_tmap_1(A_36, B_48))))) | ~v1_funct_2(C_54, u1_struct_0(A_36), u1_struct_0(k8_tmap_1(A_36, B_48))) | ~v1_funct_1(C_54) | ~m1_pre_topc(B_48, A_36) | ~l1_pre_topc(A_36) | ~v2_pre_topc(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_130])).
% 28.61/16.53  tff(c_37392, plain, (![B_1572]: (~r1_funct_2(u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_1572)), u1_struct_0('#skF_5'), u1_struct_0(k6_tmap_1('#skF_5', u1_struct_0(B_1572))), k6_partfun1(u1_struct_0('#skF_5')), k7_tmap_1('#skF_5', '#skF_3'('#skF_5', B_1572, k6_partfun1(u1_struct_0('#skF_5'))))) | k9_tmap_1('#skF_5', B_1572)=k6_partfun1(u1_struct_0('#skF_5')) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_1572))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')), u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_1572))) | ~v1_funct_1(k6_partfun1(u1_struct_0('#skF_5'))) | ~m1_pre_topc(B_1572, '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | k9_tmap_1('#skF_5', B_1572)=k6_partfun1(u1_struct_0('#skF_5')) | ~m1_pre_topc(B_1572, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_37386, c_26])).
% 28.61/16.53  tff(c_37401, plain, (![B_1572]: (~r1_funct_2(u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_1572)), u1_struct_0('#skF_5'), u1_struct_0(k6_tmap_1('#skF_5', u1_struct_0(B_1572))), k6_partfun1(u1_struct_0('#skF_5')), k7_tmap_1('#skF_5', '#skF_3'('#skF_5', B_1572, k6_partfun1(u1_struct_0('#skF_5'))))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_1572))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')), u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_1572))) | v2_struct_0('#skF_5') | k9_tmap_1('#skF_5', B_1572)=k6_partfun1(u1_struct_0('#skF_5')) | ~m1_pre_topc(B_1572, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_27865, c_37392])).
% 28.61/16.53  tff(c_37402, plain, (![B_1572]: (~r1_funct_2(u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_1572)), u1_struct_0('#skF_5'), u1_struct_0(k6_tmap_1('#skF_5', u1_struct_0(B_1572))), k6_partfun1(u1_struct_0('#skF_5')), k7_tmap_1('#skF_5', '#skF_3'('#skF_5', B_1572, k6_partfun1(u1_struct_0('#skF_5'))))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_1572))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')), u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_1572))) | k9_tmap_1('#skF_5', B_1572)=k6_partfun1(u1_struct_0('#skF_5')) | ~m1_pre_topc(B_1572, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_80, c_37401])).
% 28.61/16.53  tff(c_37522, plain, (![B_1575]: (~r1_funct_2(u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_1575)), u1_struct_0('#skF_5'), u1_struct_0(k6_tmap_1('#skF_5', u1_struct_0(B_1575))), k6_partfun1(u1_struct_0('#skF_5')), k7_tmap_1('#skF_5', u1_struct_0(B_1575))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_1575))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')), u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_1575))) | k9_tmap_1('#skF_5', B_1575)=k6_partfun1(u1_struct_0('#skF_5')) | ~m1_pre_topc(B_1575, '#skF_5') | k9_tmap_1('#skF_5', B_1575)=k6_partfun1(u1_struct_0('#skF_5')) | ~m1_pre_topc(B_1575, '#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_37515, c_37402])).
% 28.61/16.53  tff(c_37610, plain, (![B_1575]: (~r1_funct_2(u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_1575)), u1_struct_0('#skF_5'), u1_struct_0(k6_tmap_1('#skF_5', u1_struct_0(B_1575))), k6_partfun1(u1_struct_0('#skF_5')), k7_tmap_1('#skF_5', u1_struct_0(B_1575))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_1575))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')), u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_1575))) | k9_tmap_1('#skF_5', B_1575)=k6_partfun1(u1_struct_0('#skF_5')) | ~m1_pre_topc(B_1575, '#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_78, c_37522])).
% 28.61/16.53  tff(c_38329, plain, (![B_1594]: (~r1_funct_2(u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_1594)), u1_struct_0('#skF_5'), u1_struct_0(k6_tmap_1('#skF_5', u1_struct_0(B_1594))), k6_partfun1(u1_struct_0('#skF_5')), k7_tmap_1('#skF_5', u1_struct_0(B_1594))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_1594))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')), u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_1594))) | k9_tmap_1('#skF_5', B_1594)=k6_partfun1(u1_struct_0('#skF_5')) | ~m1_pre_topc(B_1594, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_80, c_37610])).
% 28.61/16.53  tff(c_38486, plain, (![B_82]: (~r1_funct_2(u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_82)), u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), k6_partfun1(u1_struct_0('#skF_5')), k7_tmap_1('#skF_5', u1_struct_0(B_82))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_82))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')), u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_82))) | k9_tmap_1('#skF_5', B_82)=k6_partfun1(u1_struct_0('#skF_5')) | ~m1_pre_topc(B_82, '#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~m1_pre_topc(B_82, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_15362, c_38329])).
% 28.61/16.53  tff(c_38515, plain, (![B_82]: (~r1_funct_2(u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_82)), u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), k6_partfun1(u1_struct_0('#skF_5')), k7_tmap_1('#skF_5', u1_struct_0(B_82))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_82))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')), u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_82))) | k9_tmap_1('#skF_5', B_82)=k6_partfun1(u1_struct_0('#skF_5')) | v2_struct_0('#skF_5') | ~m1_pre_topc(B_82, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_78, c_38486])).
% 28.61/16.53  tff(c_38822, plain, (![B_1624]: (~r1_funct_2(u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_1624)), u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), k6_partfun1(u1_struct_0('#skF_5')), k7_tmap_1('#skF_5', u1_struct_0(B_1624))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_1624))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')), u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_1624))) | k9_tmap_1('#skF_5', B_1624)=k6_partfun1(u1_struct_0('#skF_5')) | ~m1_pre_topc(B_1624, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_80, c_38515])).
% 28.61/16.53  tff(c_38882, plain, (![B_765]: (~r1_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), k6_partfun1(u1_struct_0('#skF_5')), k7_tmap_1('#skF_5', u1_struct_0(B_765))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_765))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')), u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_765))) | k9_tmap_1('#skF_5', B_765)=k6_partfun1(u1_struct_0('#skF_5')) | ~m1_pre_topc(B_765, '#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~m1_pre_topc(B_765, '#skF_5') | ~l1_pre_topc('#skF_5') | ~m1_pre_topc(B_765, '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_16457, c_38822])).
% 28.61/16.54  tff(c_38915, plain, (![B_765]: (~r1_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), k6_partfun1(u1_struct_0('#skF_5')), k7_tmap_1('#skF_5', u1_struct_0(B_765))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_765))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')), u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_765))) | k9_tmap_1('#skF_5', B_765)=k6_partfun1(u1_struct_0('#skF_5')) | ~m1_pre_topc(B_765, '#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_76, c_78, c_38882])).
% 28.61/16.54  tff(c_40231, plain, (![B_1651]: (~r1_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), k6_partfun1(u1_struct_0('#skF_5')), k7_tmap_1('#skF_5', u1_struct_0(B_1651))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_1651))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')), u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_1651))) | k9_tmap_1('#skF_5', B_1651)=k6_partfun1(u1_struct_0('#skF_5')) | ~m1_pre_topc(B_1651, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_80, c_38915])).
% 28.61/16.54  tff(c_40301, plain, (![B_82]: (~r1_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), k6_partfun1(u1_struct_0('#skF_5')), k6_partfun1(u1_struct_0('#skF_5'))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_82))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')), u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_82))) | k9_tmap_1('#skF_5', B_82)=k6_partfun1(u1_struct_0('#skF_5')) | ~m1_pre_topc(B_82, '#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~m1_pre_topc(B_82, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_15411, c_40231])).
% 28.61/16.54  tff(c_40309, plain, (![B_82]: (~r1_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), k6_partfun1(u1_struct_0('#skF_5')), k6_partfun1(u1_struct_0('#skF_5'))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_82))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')), u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_82))) | k9_tmap_1('#skF_5', B_82)=k6_partfun1(u1_struct_0('#skF_5')) | v2_struct_0('#skF_5') | ~m1_pre_topc(B_82, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_78, c_40301])).
% 28.61/16.54  tff(c_40310, plain, (![B_82]: (~r1_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), k6_partfun1(u1_struct_0('#skF_5')), k6_partfun1(u1_struct_0('#skF_5'))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_82))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')), u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_82))) | k9_tmap_1('#skF_5', B_82)=k6_partfun1(u1_struct_0('#skF_5')) | ~m1_pre_topc(B_82, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_80, c_40309])).
% 28.61/16.54  tff(c_40847, plain, (~r1_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), u1_struct_0('#skF_5'), k6_partfun1(u1_struct_0('#skF_5')), k6_partfun1(u1_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_40310])).
% 28.61/16.54  tff(c_40850, plain, (~m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_5')))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_27880, c_40847])).
% 28.61/16.54  tff(c_40853, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_25364, c_27849, c_40850])).
% 28.61/16.54  tff(c_40855, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27881, c_40853])).
% 28.61/16.54  tff(c_40865, plain, (![B_1678]: (~m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_1678))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')), u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_1678))) | k9_tmap_1('#skF_5', B_1678)=k6_partfun1(u1_struct_0('#skF_5')) | ~m1_pre_topc(B_1678, '#skF_5'))), inference(splitRight, [status(thm)], [c_40310])).
% 28.61/16.54  tff(c_40881, plain, (![B_765]: (~m1_subset_1(k6_partfun1(u1_struct_0('#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_5')))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')), u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_765))) | k9_tmap_1('#skF_5', B_765)=k6_partfun1(u1_struct_0('#skF_5')) | ~m1_pre_topc(B_765, '#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~m1_pre_topc(B_765, '#skF_5') | ~l1_pre_topc('#skF_5') | ~m1_pre_topc(B_765, '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_16457, c_40865])).
% 28.61/16.54  tff(c_40893, plain, (![B_765]: (~v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')), u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_765))) | k9_tmap_1('#skF_5', B_765)=k6_partfun1(u1_struct_0('#skF_5')) | ~m1_pre_topc(B_765, '#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_76, c_78, c_27849, c_40881])).
% 28.61/16.54  tff(c_40895, plain, (![B_1679]: (~v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')), u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_5', B_1679))) | k9_tmap_1('#skF_5', B_1679)=k6_partfun1(u1_struct_0('#skF_5')) | ~m1_pre_topc(B_1679, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_80, c_40893])).
% 28.61/16.54  tff(c_40911, plain, (![B_765]: (~v1_funct_2(k6_partfun1(u1_struct_0('#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_5')) | k9_tmap_1('#skF_5', B_765)=k6_partfun1(u1_struct_0('#skF_5')) | ~m1_pre_topc(B_765, '#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~m1_pre_topc(B_765, '#skF_5') | ~l1_pre_topc('#skF_5') | ~m1_pre_topc(B_765, '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_16457, c_40895])).
% 28.61/16.54  tff(c_40923, plain, (![B_765]: (k9_tmap_1('#skF_5', B_765)=k6_partfun1(u1_struct_0('#skF_5')) | ~m1_pre_topc(B_765, '#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_76, c_78, c_25364, c_40911])).
% 28.61/16.54  tff(c_40925, plain, (![B_1680]: (k9_tmap_1('#skF_5', B_1680)=k6_partfun1(u1_struct_0('#skF_5')) | ~m1_pre_topc(B_1680, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_80, c_40923])).
% 28.61/16.54  tff(c_40928, plain, (k6_partfun1(u1_struct_0('#skF_5'))=k9_tmap_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_74, c_40925])).
% 28.61/16.54  tff(c_15706, plain, (![A_680, B_681]: (v5_pre_topc(k7_tmap_1(A_680, B_681), A_680, k6_tmap_1(A_680, B_681)) | ~v3_pre_topc(B_681, A_680) | ~m1_subset_1(B_681, k1_zfmisc_1(u1_struct_0(A_680))) | ~l1_pre_topc(A_680) | ~v2_pre_topc(A_680) | v2_struct_0(A_680))), inference(cnfTransformation, [status(thm)], [f_223])).
% 28.61/16.54  tff(c_20397, plain, (![A_962, B_963]: (v5_pre_topc(k6_partfun1(u1_struct_0(A_962)), A_962, k6_tmap_1(A_962, u1_struct_0(B_963))) | ~v3_pre_topc(u1_struct_0(B_963), A_962) | ~m1_subset_1(u1_struct_0(B_963), k1_zfmisc_1(u1_struct_0(A_962))) | ~l1_pre_topc(A_962) | ~v2_pre_topc(A_962) | v2_struct_0(A_962) | ~v2_pre_topc(A_962) | v2_struct_0(A_962) | ~m1_pre_topc(B_963, A_962) | ~l1_pre_topc(A_962))), inference(superposition, [status(thm), theory('equality')], [c_15411, c_15706])).
% 28.61/16.54  tff(c_20442, plain, (![A_70, B_71]: (v5_pre_topc(k6_partfun1(u1_struct_0(A_70)), A_70, k8_tmap_1(A_70, B_71)) | ~v3_pre_topc(u1_struct_0(B_71), A_70) | ~m1_subset_1(u1_struct_0(B_71), k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70) | v2_struct_0(A_70) | ~v2_pre_topc(A_70) | v2_struct_0(A_70) | ~m1_pre_topc(B_71, A_70) | ~l1_pre_topc(A_70) | ~m1_pre_topc(B_71, A_70) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70) | v2_struct_0(A_70))), inference(superposition, [status(thm), theory('equality')], [c_16413, c_20397])).
% 28.61/16.54  tff(c_40957, plain, (![B_71]: (v5_pre_topc(k9_tmap_1('#skF_5', '#skF_6'), '#skF_5', k8_tmap_1('#skF_5', B_71)) | ~v3_pre_topc(u1_struct_0(B_71), '#skF_5') | ~m1_subset_1(u1_struct_0(B_71), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~m1_pre_topc(B_71, '#skF_5') | ~l1_pre_topc('#skF_5') | ~m1_pre_topc(B_71, '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_40928, c_20442])).
% 28.61/16.54  tff(c_41030, plain, (![B_71]: (v5_pre_topc(k9_tmap_1('#skF_5', '#skF_6'), '#skF_5', k8_tmap_1('#skF_5', B_71)) | ~v3_pre_topc(u1_struct_0(B_71), '#skF_5') | ~m1_subset_1(u1_struct_0(B_71), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc(B_71, '#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_76, c_78, c_78, c_76, c_40957])).
% 28.61/16.54  tff(c_44525, plain, (![B_1700]: (v5_pre_topc(k9_tmap_1('#skF_5', '#skF_6'), '#skF_5', k8_tmap_1('#skF_5', B_1700)) | ~v3_pre_topc(u1_struct_0(B_1700), '#skF_5') | ~m1_subset_1(u1_struct_0(B_1700), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc(B_1700, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_80, c_41030])).
% 28.61/16.54  tff(c_44611, plain, (![B_82]: (v5_pre_topc(k9_tmap_1('#skF_5', '#skF_6'), '#skF_5', k8_tmap_1('#skF_5', B_82)) | ~v3_pre_topc(u1_struct_0(B_82), '#skF_5') | ~m1_pre_topc(B_82, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_72, c_44525])).
% 28.61/16.54  tff(c_44619, plain, (![B_1701]: (v5_pre_topc(k9_tmap_1('#skF_5', '#skF_6'), '#skF_5', k8_tmap_1('#skF_5', B_1701)) | ~v3_pre_topc(u1_struct_0(B_1701), '#skF_5') | ~m1_pre_topc(B_1701, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_44611])).
% 28.61/16.54  tff(c_15322, plain, (~v5_pre_topc(k9_tmap_1('#skF_5', '#skF_6'), '#skF_5', k8_tmap_1('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_98])).
% 28.61/16.54  tff(c_44622, plain, (~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_5') | ~m1_pre_topc('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_44619, c_15322])).
% 28.61/16.54  tff(c_44633, plain, (~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_44622])).
% 28.61/16.54  tff(c_44642, plain, (~v1_tsep_1('#skF_6', '#skF_5') | ~m1_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_15504, c_44633])).
% 28.61/16.54  tff(c_44646, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_15321, c_44642])).
% 28.61/16.54  tff(c_44648, plain, (~v1_funct_1(k9_tmap_1('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_110])).
% 28.61/16.54  tff(c_44659, plain, (~m1_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_44656, c_44648])).
% 28.61/16.54  tff(c_44662, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_44659])).
% 28.61/16.54  tff(c_44664, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_44662])).
% 28.61/16.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 28.61/16.54  
% 28.61/16.54  Inference rules
% 28.61/16.54  ----------------------
% 28.61/16.54  #Ref     : 0
% 28.61/16.54  #Sup     : 13593
% 28.61/16.54  #Fact    : 4
% 28.61/16.54  #Define  : 0
% 28.61/16.54  #Split   : 48
% 28.61/16.54  #Chain   : 0
% 28.61/16.54  #Close   : 0
% 28.61/16.54  
% 28.61/16.54  Ordering : KBO
% 28.61/16.54  
% 28.61/16.54  Simplification rules
% 28.61/16.54  ----------------------
% 28.61/16.54  #Subsume      : 790
% 28.61/16.54  #Demod        : 3785
% 28.61/16.54  #Tautology    : 947
% 28.61/16.54  #SimpNegUnit  : 531
% 28.61/16.54  #BackRed      : 36
% 28.61/16.54  
% 28.61/16.54  #Partial instantiations: 0
% 28.61/16.54  #Strategies tried      : 1
% 28.61/16.54  
% 28.61/16.54  Timing (in seconds)
% 28.61/16.54  ----------------------
% 28.61/16.54  Preprocessing        : 0.40
% 28.61/16.54  Parsing              : 0.20
% 28.61/16.54  CNF conversion       : 0.03
% 28.61/16.54  Main loop            : 15.28
% 28.61/16.54  Inferencing          : 2.90
% 28.61/16.54  Reduction            : 3.34
% 28.61/16.54  Demodulation         : 2.33
% 28.61/16.54  BG Simplification    : 0.51
% 28.61/16.54  Subsumption          : 7.76
% 28.61/16.54  Abstraction          : 0.52
% 28.61/16.54  MUC search           : 0.00
% 28.61/16.54  Cooper               : 0.00
% 28.61/16.54  Total                : 15.78
% 28.61/16.54  Index Insertion      : 0.00
% 28.61/16.54  Index Deletion       : 0.00
% 28.61/16.54  Index Matching       : 0.00
% 28.61/16.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
