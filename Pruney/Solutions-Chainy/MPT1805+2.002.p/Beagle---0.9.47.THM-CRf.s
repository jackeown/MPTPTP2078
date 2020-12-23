%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:03 EST 2020

% Result     : Theorem 9.78s
% Output     : CNFRefutation 10.04s
% Verified   : 
% Statistics : Number of formulae       :  240 ( 837 expanded)
%              Number of leaves         :   42 ( 301 expanded)
%              Depth                    :   27
%              Number of atoms          : 1324 (4674 expanded)
%              Number of equality atoms :  103 ( 245 expanded)
%              Maximal formula depth    :   22 (   8 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > v5_pre_topc > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k9_tmap_1 > k8_tmap_1 > k7_tmap_1 > k6_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_partfun1 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k7_tmap_1,type,(
    k7_tmap_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_246,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ( v1_funct_1(k2_tmap_1(A,k8_tmap_1(A,B),k9_tmap_1(A,B),B))
              & v1_funct_2(k2_tmap_1(A,k8_tmap_1(A,B),k9_tmap_1(A,B),B),u1_struct_0(B),u1_struct_0(k8_tmap_1(A,B)))
              & v5_pre_topc(k2_tmap_1(A,k8_tmap_1(A,B),k9_tmap_1(A,B),B),B,k8_tmap_1(A,B))
              & m1_subset_1(k2_tmap_1(A,k8_tmap_1(A,B),k9_tmap_1(A,B),B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(k8_tmap_1(A,B))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_tmap_1)).

tff(f_224,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_160,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_pre_topc(k8_tmap_1(A,B))
        & v2_pre_topc(k8_tmap_1(A,B))
        & l1_pre_topc(k8_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_175,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_funct_1(k9_tmap_1(A,B))
        & v1_funct_2(k9_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k8_tmap_1(A,B)))
        & m1_subset_1(k9_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k8_tmap_1(A,B))))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_tmap_1)).

tff(f_145,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_funct_1(k7_tmap_1(A,B))
        & v1_funct_2(k7_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B)))
        & m1_subset_1(k7_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B))))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).

tff(f_191,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( ~ v2_struct_0(k8_tmap_1(A,B))
        & v1_pre_topc(k8_tmap_1(A,B))
        & v2_pre_topc(k8_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_tmap_1)).

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

tff(f_217,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( u1_struct_0(C) = B
               => ( v1_funct_1(k2_tmap_1(A,k6_tmap_1(A,B),k7_tmap_1(A,B),C))
                  & v1_funct_2(k2_tmap_1(A,k6_tmap_1(A,B),k7_tmap_1(A,B),C),u1_struct_0(C),u1_struct_0(k6_tmap_1(A,B)))
                  & v5_pre_topc(k2_tmap_1(A,k6_tmap_1(A,B),k7_tmap_1(A,B),C),C,k6_tmap_1(A,B))
                  & m1_subset_1(k2_tmap_1(A,k6_tmap_1(A,B),k7_tmap_1(A,B),C),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(k6_tmap_1(A,B))))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_tmap_1)).

tff(c_72,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_68,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_64,plain,(
    ! [B_75,A_73] :
      ( m1_subset_1(u1_struct_0(B_75),k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ m1_pre_topc(B_75,A_73)
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_74,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_38,plain,(
    ! [A_60,B_61] :
      ( l1_pre_topc(k8_tmap_1(A_60,B_61))
      | ~ m1_pre_topc(B_61,A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    ! [A_62,B_63] :
      ( v1_funct_1(k9_tmap_1(A_62,B_63))
      | ~ m1_pre_topc(B_63,A_62)
      | ~ l1_pre_topc(A_62)
      | ~ v2_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_3492,plain,(
    ! [A_708,B_709] :
      ( v1_funct_1(k7_tmap_1(A_708,B_709))
      | ~ m1_subset_1(B_709,k1_zfmisc_1(u1_struct_0(A_708)))
      | ~ l1_pre_topc(A_708)
      | ~ v2_pre_topc(A_708)
      | v2_struct_0(A_708) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_3499,plain,(
    ! [A_73,B_75] :
      ( v1_funct_1(k7_tmap_1(A_73,u1_struct_0(B_75)))
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73)
      | ~ m1_pre_topc(B_75,A_73)
      | ~ l1_pre_topc(A_73) ) ),
    inference(resolution,[status(thm)],[c_64,c_3492])).

tff(c_52,plain,(
    ! [A_64,B_65] :
      ( v1_pre_topc(k8_tmap_1(A_64,B_65))
      | ~ m1_pre_topc(B_65,A_64)
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_50,plain,(
    ! [A_64,B_65] :
      ( v2_pre_topc(k8_tmap_1(A_64,B_65))
      | ~ m1_pre_topc(B_65,A_64)
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_3620,plain,(
    ! [A_755,B_756] :
      ( k6_tmap_1(A_755,u1_struct_0(B_756)) = k8_tmap_1(A_755,B_756)
      | ~ m1_subset_1(u1_struct_0(B_756),k1_zfmisc_1(u1_struct_0(A_755)))
      | ~ l1_pre_topc(k8_tmap_1(A_755,B_756))
      | ~ v2_pre_topc(k8_tmap_1(A_755,B_756))
      | ~ v1_pre_topc(k8_tmap_1(A_755,B_756))
      | ~ m1_pre_topc(B_756,A_755)
      | ~ l1_pre_topc(A_755)
      | ~ v2_pre_topc(A_755)
      | v2_struct_0(A_755) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_3625,plain,(
    ! [A_757,B_758] :
      ( k6_tmap_1(A_757,u1_struct_0(B_758)) = k8_tmap_1(A_757,B_758)
      | ~ l1_pre_topc(k8_tmap_1(A_757,B_758))
      | ~ v2_pre_topc(k8_tmap_1(A_757,B_758))
      | ~ v1_pre_topc(k8_tmap_1(A_757,B_758))
      | ~ v2_pre_topc(A_757)
      | v2_struct_0(A_757)
      | ~ m1_pre_topc(B_758,A_757)
      | ~ l1_pre_topc(A_757) ) ),
    inference(resolution,[status(thm)],[c_64,c_3620])).

tff(c_3630,plain,(
    ! [A_759,B_760] :
      ( k6_tmap_1(A_759,u1_struct_0(B_760)) = k8_tmap_1(A_759,B_760)
      | ~ l1_pre_topc(k8_tmap_1(A_759,B_760))
      | ~ v1_pre_topc(k8_tmap_1(A_759,B_760))
      | ~ m1_pre_topc(B_760,A_759)
      | ~ l1_pre_topc(A_759)
      | ~ v2_pre_topc(A_759)
      | v2_struct_0(A_759) ) ),
    inference(resolution,[status(thm)],[c_50,c_3625])).

tff(c_3639,plain,(
    ! [A_763,B_764] :
      ( k6_tmap_1(A_763,u1_struct_0(B_764)) = k8_tmap_1(A_763,B_764)
      | ~ l1_pre_topc(k8_tmap_1(A_763,B_764))
      | ~ m1_pre_topc(B_764,A_763)
      | ~ l1_pre_topc(A_763)
      | ~ v2_pre_topc(A_763)
      | v2_struct_0(A_763) ) ),
    inference(resolution,[status(thm)],[c_52,c_3630])).

tff(c_3643,plain,(
    ! [A_60,B_61] :
      ( k6_tmap_1(A_60,u1_struct_0(B_61)) = k8_tmap_1(A_60,B_61)
      | ~ m1_pre_topc(B_61,A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_38,c_3639])).

tff(c_46,plain,(
    ! [A_62,B_63] :
      ( v1_funct_2(k9_tmap_1(A_62,B_63),u1_struct_0(A_62),u1_struct_0(k8_tmap_1(A_62,B_63)))
      | ~ m1_pre_topc(B_63,A_62)
      | ~ l1_pre_topc(A_62)
      | ~ v2_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_44,plain,(
    ! [A_62,B_63] :
      ( m1_subset_1(k9_tmap_1(A_62,B_63),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_62),u1_struct_0(k8_tmap_1(A_62,B_63)))))
      | ~ m1_pre_topc(B_63,A_62)
      | ~ l1_pre_topc(A_62)
      | ~ v2_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_34,plain,(
    ! [A_58,B_59] :
      ( v1_funct_2(k7_tmap_1(A_58,B_59),u1_struct_0(A_58),u1_struct_0(k6_tmap_1(A_58,B_59)))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_32,plain,(
    ! [A_58,B_59] :
      ( m1_subset_1(k7_tmap_1(A_58,B_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_58),u1_struct_0(k6_tmap_1(A_58,B_59)))))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_3806,plain,(
    ! [A_818,B_819] :
      ( r1_funct_2(u1_struct_0(A_818),u1_struct_0(k8_tmap_1(A_818,B_819)),u1_struct_0(A_818),u1_struct_0(k6_tmap_1(A_818,u1_struct_0(B_819))),k9_tmap_1(A_818,B_819),k7_tmap_1(A_818,u1_struct_0(B_819)))
      | ~ m1_subset_1(u1_struct_0(B_819),k1_zfmisc_1(u1_struct_0(A_818)))
      | ~ m1_subset_1(k9_tmap_1(A_818,B_819),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_818),u1_struct_0(k8_tmap_1(A_818,B_819)))))
      | ~ v1_funct_2(k9_tmap_1(A_818,B_819),u1_struct_0(A_818),u1_struct_0(k8_tmap_1(A_818,B_819)))
      | ~ v1_funct_1(k9_tmap_1(A_818,B_819))
      | ~ m1_pre_topc(B_819,A_818)
      | ~ l1_pre_topc(A_818)
      | ~ v2_pre_topc(A_818)
      | v2_struct_0(A_818) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

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

tff(c_4059,plain,(
    ! [A_871,B_872] :
      ( k7_tmap_1(A_871,u1_struct_0(B_872)) = k9_tmap_1(A_871,B_872)
      | ~ m1_subset_1(k7_tmap_1(A_871,u1_struct_0(B_872)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_871),u1_struct_0(k6_tmap_1(A_871,u1_struct_0(B_872))))))
      | ~ v1_funct_2(k7_tmap_1(A_871,u1_struct_0(B_872)),u1_struct_0(A_871),u1_struct_0(k6_tmap_1(A_871,u1_struct_0(B_872))))
      | ~ v1_funct_1(k7_tmap_1(A_871,u1_struct_0(B_872)))
      | v1_xboole_0(u1_struct_0(k6_tmap_1(A_871,u1_struct_0(B_872))))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_871,B_872)))
      | ~ m1_subset_1(u1_struct_0(B_872),k1_zfmisc_1(u1_struct_0(A_871)))
      | ~ m1_subset_1(k9_tmap_1(A_871,B_872),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_871),u1_struct_0(k8_tmap_1(A_871,B_872)))))
      | ~ v1_funct_2(k9_tmap_1(A_871,B_872),u1_struct_0(A_871),u1_struct_0(k8_tmap_1(A_871,B_872)))
      | ~ v1_funct_1(k9_tmap_1(A_871,B_872))
      | ~ m1_pre_topc(B_872,A_871)
      | ~ l1_pre_topc(A_871)
      | ~ v2_pre_topc(A_871)
      | v2_struct_0(A_871) ) ),
    inference(resolution,[status(thm)],[c_3806,c_12])).

tff(c_4384,plain,(
    ! [A_944,B_945] :
      ( k7_tmap_1(A_944,u1_struct_0(B_945)) = k9_tmap_1(A_944,B_945)
      | ~ v1_funct_2(k7_tmap_1(A_944,u1_struct_0(B_945)),u1_struct_0(A_944),u1_struct_0(k6_tmap_1(A_944,u1_struct_0(B_945))))
      | ~ v1_funct_1(k7_tmap_1(A_944,u1_struct_0(B_945)))
      | v1_xboole_0(u1_struct_0(k6_tmap_1(A_944,u1_struct_0(B_945))))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_944,B_945)))
      | ~ m1_subset_1(k9_tmap_1(A_944,B_945),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_944),u1_struct_0(k8_tmap_1(A_944,B_945)))))
      | ~ v1_funct_2(k9_tmap_1(A_944,B_945),u1_struct_0(A_944),u1_struct_0(k8_tmap_1(A_944,B_945)))
      | ~ v1_funct_1(k9_tmap_1(A_944,B_945))
      | ~ m1_pre_topc(B_945,A_944)
      | ~ m1_subset_1(u1_struct_0(B_945),k1_zfmisc_1(u1_struct_0(A_944)))
      | ~ l1_pre_topc(A_944)
      | ~ v2_pre_topc(A_944)
      | v2_struct_0(A_944) ) ),
    inference(resolution,[status(thm)],[c_32,c_4059])).

tff(c_4428,plain,(
    ! [A_954,B_955] :
      ( k7_tmap_1(A_954,u1_struct_0(B_955)) = k9_tmap_1(A_954,B_955)
      | ~ v1_funct_1(k7_tmap_1(A_954,u1_struct_0(B_955)))
      | v1_xboole_0(u1_struct_0(k6_tmap_1(A_954,u1_struct_0(B_955))))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_954,B_955)))
      | ~ m1_subset_1(k9_tmap_1(A_954,B_955),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_954),u1_struct_0(k8_tmap_1(A_954,B_955)))))
      | ~ v1_funct_2(k9_tmap_1(A_954,B_955),u1_struct_0(A_954),u1_struct_0(k8_tmap_1(A_954,B_955)))
      | ~ v1_funct_1(k9_tmap_1(A_954,B_955))
      | ~ m1_pre_topc(B_955,A_954)
      | ~ m1_subset_1(u1_struct_0(B_955),k1_zfmisc_1(u1_struct_0(A_954)))
      | ~ l1_pre_topc(A_954)
      | ~ v2_pre_topc(A_954)
      | v2_struct_0(A_954) ) ),
    inference(resolution,[status(thm)],[c_34,c_4384])).

tff(c_4433,plain,(
    ! [A_956,B_957] :
      ( k7_tmap_1(A_956,u1_struct_0(B_957)) = k9_tmap_1(A_956,B_957)
      | ~ v1_funct_1(k7_tmap_1(A_956,u1_struct_0(B_957)))
      | v1_xboole_0(u1_struct_0(k6_tmap_1(A_956,u1_struct_0(B_957))))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_956,B_957)))
      | ~ v1_funct_2(k9_tmap_1(A_956,B_957),u1_struct_0(A_956),u1_struct_0(k8_tmap_1(A_956,B_957)))
      | ~ v1_funct_1(k9_tmap_1(A_956,B_957))
      | ~ m1_subset_1(u1_struct_0(B_957),k1_zfmisc_1(u1_struct_0(A_956)))
      | ~ m1_pre_topc(B_957,A_956)
      | ~ l1_pre_topc(A_956)
      | ~ v2_pre_topc(A_956)
      | v2_struct_0(A_956) ) ),
    inference(resolution,[status(thm)],[c_44,c_4428])).

tff(c_4438,plain,(
    ! [A_958,B_959] :
      ( k7_tmap_1(A_958,u1_struct_0(B_959)) = k9_tmap_1(A_958,B_959)
      | ~ v1_funct_1(k7_tmap_1(A_958,u1_struct_0(B_959)))
      | v1_xboole_0(u1_struct_0(k6_tmap_1(A_958,u1_struct_0(B_959))))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_958,B_959)))
      | ~ v1_funct_1(k9_tmap_1(A_958,B_959))
      | ~ m1_subset_1(u1_struct_0(B_959),k1_zfmisc_1(u1_struct_0(A_958)))
      | ~ m1_pre_topc(B_959,A_958)
      | ~ l1_pre_topc(A_958)
      | ~ v2_pre_topc(A_958)
      | v2_struct_0(A_958) ) ),
    inference(resolution,[status(thm)],[c_46,c_4433])).

tff(c_4443,plain,(
    ! [A_960,B_961] :
      ( k7_tmap_1(A_960,u1_struct_0(B_961)) = k9_tmap_1(A_960,B_961)
      | ~ v1_funct_1(k7_tmap_1(A_960,u1_struct_0(B_961)))
      | v1_xboole_0(u1_struct_0(k6_tmap_1(A_960,u1_struct_0(B_961))))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_960,B_961)))
      | ~ v1_funct_1(k9_tmap_1(A_960,B_961))
      | ~ v2_pre_topc(A_960)
      | v2_struct_0(A_960)
      | ~ m1_pre_topc(B_961,A_960)
      | ~ l1_pre_topc(A_960) ) ),
    inference(resolution,[status(thm)],[c_64,c_4438])).

tff(c_4449,plain,(
    ! [A_60,B_61] :
      ( k7_tmap_1(A_60,u1_struct_0(B_61)) = k9_tmap_1(A_60,B_61)
      | ~ v1_funct_1(k7_tmap_1(A_60,u1_struct_0(B_61)))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_60,B_61)))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_60,B_61)))
      | ~ v1_funct_1(k9_tmap_1(A_60,B_61))
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60)
      | ~ m1_pre_topc(B_61,A_60)
      | ~ l1_pre_topc(A_60)
      | ~ m1_pre_topc(B_61,A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3643,c_4443])).

tff(c_4478,plain,(
    ! [A_970,B_971] :
      ( k7_tmap_1(A_970,u1_struct_0(B_971)) = k9_tmap_1(A_970,B_971)
      | ~ v1_funct_1(k7_tmap_1(A_970,u1_struct_0(B_971)))
      | ~ v1_funct_1(k9_tmap_1(A_970,B_971))
      | ~ m1_pre_topc(B_971,A_970)
      | ~ l1_pre_topc(A_970)
      | ~ v2_pre_topc(A_970)
      | v2_struct_0(A_970)
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_970,B_971))) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_4449])).

tff(c_4,plain,(
    ! [A_2] :
      ( ~ v1_xboole_0(u1_struct_0(A_2))
      | ~ l1_struct_0(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4483,plain,(
    ! [A_972,B_973] :
      ( ~ l1_struct_0(k8_tmap_1(A_972,B_973))
      | v2_struct_0(k8_tmap_1(A_972,B_973))
      | k7_tmap_1(A_972,u1_struct_0(B_973)) = k9_tmap_1(A_972,B_973)
      | ~ v1_funct_1(k7_tmap_1(A_972,u1_struct_0(B_973)))
      | ~ v1_funct_1(k9_tmap_1(A_972,B_973))
      | ~ m1_pre_topc(B_973,A_972)
      | ~ l1_pre_topc(A_972)
      | ~ v2_pre_topc(A_972)
      | v2_struct_0(A_972) ) ),
    inference(resolution,[status(thm)],[c_4478,c_4])).

tff(c_4491,plain,(
    ! [A_974,B_975] :
      ( ~ l1_struct_0(k8_tmap_1(A_974,B_975))
      | v2_struct_0(k8_tmap_1(A_974,B_975))
      | k7_tmap_1(A_974,u1_struct_0(B_975)) = k9_tmap_1(A_974,B_975)
      | ~ v1_funct_1(k9_tmap_1(A_974,B_975))
      | ~ v2_pre_topc(A_974)
      | v2_struct_0(A_974)
      | ~ m1_pre_topc(B_975,A_974)
      | ~ l1_pre_topc(A_974) ) ),
    inference(resolution,[status(thm)],[c_3499,c_4483])).

tff(c_54,plain,(
    ! [A_64,B_65] :
      ( ~ v2_struct_0(k8_tmap_1(A_64,B_65))
      | ~ m1_pre_topc(B_65,A_64)
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_4496,plain,(
    ! [A_976,B_977] :
      ( ~ l1_struct_0(k8_tmap_1(A_976,B_977))
      | k7_tmap_1(A_976,u1_struct_0(B_977)) = k9_tmap_1(A_976,B_977)
      | ~ v1_funct_1(k9_tmap_1(A_976,B_977))
      | ~ v2_pre_topc(A_976)
      | v2_struct_0(A_976)
      | ~ m1_pre_topc(B_977,A_976)
      | ~ l1_pre_topc(A_976) ) ),
    inference(resolution,[status(thm)],[c_4491,c_54])).

tff(c_4501,plain,(
    ! [A_978,B_979] :
      ( ~ l1_struct_0(k8_tmap_1(A_978,B_979))
      | k7_tmap_1(A_978,u1_struct_0(B_979)) = k9_tmap_1(A_978,B_979)
      | ~ m1_pre_topc(B_979,A_978)
      | ~ l1_pre_topc(A_978)
      | ~ v2_pre_topc(A_978)
      | v2_struct_0(A_978) ) ),
    inference(resolution,[status(thm)],[c_48,c_4496])).

tff(c_4506,plain,(
    ! [A_980,B_981] :
      ( k7_tmap_1(A_980,u1_struct_0(B_981)) = k9_tmap_1(A_980,B_981)
      | ~ m1_pre_topc(B_981,A_980)
      | ~ l1_pre_topc(A_980)
      | ~ v2_pre_topc(A_980)
      | v2_struct_0(A_980)
      | ~ l1_pre_topc(k8_tmap_1(A_980,B_981)) ) ),
    inference(resolution,[status(thm)],[c_2,c_4501])).

tff(c_4511,plain,(
    ! [A_982,B_983] :
      ( k7_tmap_1(A_982,u1_struct_0(B_983)) = k9_tmap_1(A_982,B_983)
      | ~ m1_pre_topc(B_983,A_982)
      | ~ l1_pre_topc(A_982)
      | ~ v2_pre_topc(A_982)
      | v2_struct_0(A_982) ) ),
    inference(resolution,[status(thm)],[c_38,c_4506])).

tff(c_3501,plain,(
    ! [A_710,B_711] :
      ( k7_tmap_1(A_710,B_711) = k6_partfun1(u1_struct_0(A_710))
      | ~ m1_subset_1(B_711,k1_zfmisc_1(u1_struct_0(A_710)))
      | ~ l1_pre_topc(A_710)
      | ~ v2_pre_topc(A_710)
      | v2_struct_0(A_710) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3508,plain,(
    ! [A_73,B_75] :
      ( k7_tmap_1(A_73,u1_struct_0(B_75)) = k6_partfun1(u1_struct_0(A_73))
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73)
      | ~ m1_pre_topc(B_75,A_73)
      | ~ l1_pre_topc(A_73) ) ),
    inference(resolution,[status(thm)],[c_64,c_3501])).

tff(c_4614,plain,(
    ! [A_988,B_989] :
      ( k9_tmap_1(A_988,B_989) = k6_partfun1(u1_struct_0(A_988))
      | ~ v2_pre_topc(A_988)
      | v2_struct_0(A_988)
      | ~ m1_pre_topc(B_989,A_988)
      | ~ l1_pre_topc(A_988)
      | ~ m1_pre_topc(B_989,A_988)
      | ~ l1_pre_topc(A_988)
      | ~ v2_pre_topc(A_988)
      | v2_struct_0(A_988) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4511,c_3508])).

tff(c_4616,plain,
    ( k6_partfun1(u1_struct_0('#skF_4')) = k9_tmap_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_4614])).

tff(c_4619,plain,
    ( k6_partfun1(u1_struct_0('#skF_4')) = k9_tmap_1('#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_4616])).

tff(c_4620,plain,(
    k6_partfun1(u1_struct_0('#skF_4')) = k9_tmap_1('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_4619])).

tff(c_3635,plain,(
    ! [A_761,C_762] :
      ( v1_funct_2(k2_tmap_1(A_761,k6_tmap_1(A_761,u1_struct_0(C_762)),k7_tmap_1(A_761,u1_struct_0(C_762)),C_762),u1_struct_0(C_762),u1_struct_0(k6_tmap_1(A_761,u1_struct_0(C_762))))
      | ~ m1_pre_topc(C_762,A_761)
      | v2_struct_0(C_762)
      | ~ m1_subset_1(u1_struct_0(C_762),k1_zfmisc_1(u1_struct_0(A_761)))
      | ~ l1_pre_topc(A_761)
      | ~ v2_pre_topc(A_761)
      | v2_struct_0(A_761) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_3839,plain,(
    ! [A_826,B_827] :
      ( v1_funct_2(k2_tmap_1(A_826,k6_tmap_1(A_826,u1_struct_0(B_827)),k6_partfun1(u1_struct_0(A_826)),B_827),u1_struct_0(B_827),u1_struct_0(k6_tmap_1(A_826,u1_struct_0(B_827))))
      | ~ m1_pre_topc(B_827,A_826)
      | v2_struct_0(B_827)
      | ~ m1_subset_1(u1_struct_0(B_827),k1_zfmisc_1(u1_struct_0(A_826)))
      | ~ l1_pre_topc(A_826)
      | ~ v2_pre_topc(A_826)
      | v2_struct_0(A_826)
      | ~ v2_pre_topc(A_826)
      | v2_struct_0(A_826)
      | ~ m1_pre_topc(B_827,A_826)
      | ~ l1_pre_topc(A_826) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3508,c_3635])).

tff(c_4253,plain,(
    ! [A_904,B_905] :
      ( v1_funct_2(k2_tmap_1(A_904,k8_tmap_1(A_904,B_905),k6_partfun1(u1_struct_0(A_904)),B_905),u1_struct_0(B_905),u1_struct_0(k6_tmap_1(A_904,u1_struct_0(B_905))))
      | ~ m1_pre_topc(B_905,A_904)
      | v2_struct_0(B_905)
      | ~ m1_subset_1(u1_struct_0(B_905),k1_zfmisc_1(u1_struct_0(A_904)))
      | ~ l1_pre_topc(A_904)
      | ~ v2_pre_topc(A_904)
      | v2_struct_0(A_904)
      | ~ v2_pre_topc(A_904)
      | v2_struct_0(A_904)
      | ~ m1_pre_topc(B_905,A_904)
      | ~ l1_pre_topc(A_904)
      | ~ m1_pre_topc(B_905,A_904)
      | ~ l1_pre_topc(A_904)
      | ~ v2_pre_topc(A_904)
      | v2_struct_0(A_904) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3643,c_3839])).

tff(c_4256,plain,(
    ! [A_60,B_61] :
      ( v1_funct_2(k2_tmap_1(A_60,k8_tmap_1(A_60,B_61),k6_partfun1(u1_struct_0(A_60)),B_61),u1_struct_0(B_61),u1_struct_0(k8_tmap_1(A_60,B_61)))
      | ~ m1_pre_topc(B_61,A_60)
      | v2_struct_0(B_61)
      | ~ m1_subset_1(u1_struct_0(B_61),k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60)
      | ~ m1_pre_topc(B_61,A_60)
      | ~ l1_pre_topc(A_60)
      | ~ m1_pre_topc(B_61,A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60)
      | ~ m1_pre_topc(B_61,A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3643,c_4253])).

tff(c_4633,plain,(
    ! [B_61] :
      ( v1_funct_2(k2_tmap_1('#skF_4',k8_tmap_1('#skF_4',B_61),k9_tmap_1('#skF_4','#skF_5'),B_61),u1_struct_0(B_61),u1_struct_0(k8_tmap_1('#skF_4',B_61)))
      | ~ m1_pre_topc(B_61,'#skF_4')
      | v2_struct_0(B_61)
      | ~ m1_subset_1(u1_struct_0(B_61),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_61,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ m1_pre_topc(B_61,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_61,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4620,c_4256])).

tff(c_4742,plain,(
    ! [B_61] :
      ( v1_funct_2(k2_tmap_1('#skF_4',k8_tmap_1('#skF_4',B_61),k9_tmap_1('#skF_4','#skF_5'),B_61),u1_struct_0(B_61),u1_struct_0(k8_tmap_1('#skF_4',B_61)))
      | v2_struct_0(B_61)
      | ~ m1_subset_1(u1_struct_0(B_61),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_61,'#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_74,c_72,c_72,c_74,c_74,c_72,c_4633])).

tff(c_5332,plain,(
    ! [B_1015] :
      ( v1_funct_2(k2_tmap_1('#skF_4',k8_tmap_1('#skF_4',B_1015),k9_tmap_1('#skF_4','#skF_5'),B_1015),u1_struct_0(B_1015),u1_struct_0(k8_tmap_1('#skF_4',B_1015)))
      | v2_struct_0(B_1015)
      | ~ m1_subset_1(u1_struct_0(B_1015),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_1015,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_4742])).

tff(c_1584,plain,(
    ! [A_392,B_393] :
      ( v1_funct_1(k7_tmap_1(A_392,B_393))
      | ~ m1_subset_1(B_393,k1_zfmisc_1(u1_struct_0(A_392)))
      | ~ l1_pre_topc(A_392)
      | ~ v2_pre_topc(A_392)
      | v2_struct_0(A_392) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1591,plain,(
    ! [A_73,B_75] :
      ( v1_funct_1(k7_tmap_1(A_73,u1_struct_0(B_75)))
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73)
      | ~ m1_pre_topc(B_75,A_73)
      | ~ l1_pre_topc(A_73) ) ),
    inference(resolution,[status(thm)],[c_64,c_1584])).

tff(c_1702,plain,(
    ! [A_437,B_438] :
      ( k6_tmap_1(A_437,u1_struct_0(B_438)) = k8_tmap_1(A_437,B_438)
      | ~ m1_subset_1(u1_struct_0(B_438),k1_zfmisc_1(u1_struct_0(A_437)))
      | ~ l1_pre_topc(k8_tmap_1(A_437,B_438))
      | ~ v2_pre_topc(k8_tmap_1(A_437,B_438))
      | ~ v1_pre_topc(k8_tmap_1(A_437,B_438))
      | ~ m1_pre_topc(B_438,A_437)
      | ~ l1_pre_topc(A_437)
      | ~ v2_pre_topc(A_437)
      | v2_struct_0(A_437) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1707,plain,(
    ! [A_439,B_440] :
      ( k6_tmap_1(A_439,u1_struct_0(B_440)) = k8_tmap_1(A_439,B_440)
      | ~ l1_pre_topc(k8_tmap_1(A_439,B_440))
      | ~ v2_pre_topc(k8_tmap_1(A_439,B_440))
      | ~ v1_pre_topc(k8_tmap_1(A_439,B_440))
      | ~ v2_pre_topc(A_439)
      | v2_struct_0(A_439)
      | ~ m1_pre_topc(B_440,A_439)
      | ~ l1_pre_topc(A_439) ) ),
    inference(resolution,[status(thm)],[c_64,c_1702])).

tff(c_1716,plain,(
    ! [A_443,B_444] :
      ( k6_tmap_1(A_443,u1_struct_0(B_444)) = k8_tmap_1(A_443,B_444)
      | ~ l1_pre_topc(k8_tmap_1(A_443,B_444))
      | ~ v1_pre_topc(k8_tmap_1(A_443,B_444))
      | ~ m1_pre_topc(B_444,A_443)
      | ~ l1_pre_topc(A_443)
      | ~ v2_pre_topc(A_443)
      | v2_struct_0(A_443) ) ),
    inference(resolution,[status(thm)],[c_50,c_1707])).

tff(c_1721,plain,(
    ! [A_445,B_446] :
      ( k6_tmap_1(A_445,u1_struct_0(B_446)) = k8_tmap_1(A_445,B_446)
      | ~ l1_pre_topc(k8_tmap_1(A_445,B_446))
      | ~ m1_pre_topc(B_446,A_445)
      | ~ l1_pre_topc(A_445)
      | ~ v2_pre_topc(A_445)
      | v2_struct_0(A_445) ) ),
    inference(resolution,[status(thm)],[c_52,c_1716])).

tff(c_1725,plain,(
    ! [A_60,B_61] :
      ( k6_tmap_1(A_60,u1_struct_0(B_61)) = k8_tmap_1(A_60,B_61)
      | ~ m1_pre_topc(B_61,A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_38,c_1721])).

tff(c_1892,plain,(
    ! [A_502,B_503] :
      ( r1_funct_2(u1_struct_0(A_502),u1_struct_0(k8_tmap_1(A_502,B_503)),u1_struct_0(A_502),u1_struct_0(k6_tmap_1(A_502,u1_struct_0(B_503))),k9_tmap_1(A_502,B_503),k7_tmap_1(A_502,u1_struct_0(B_503)))
      | ~ m1_subset_1(u1_struct_0(B_503),k1_zfmisc_1(u1_struct_0(A_502)))
      | ~ m1_subset_1(k9_tmap_1(A_502,B_503),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_502),u1_struct_0(k8_tmap_1(A_502,B_503)))))
      | ~ v1_funct_2(k9_tmap_1(A_502,B_503),u1_struct_0(A_502),u1_struct_0(k8_tmap_1(A_502,B_503)))
      | ~ v1_funct_1(k9_tmap_1(A_502,B_503))
      | ~ m1_pre_topc(B_503,A_502)
      | ~ l1_pre_topc(A_502)
      | ~ v2_pre_topc(A_502)
      | v2_struct_0(A_502) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2182,plain,(
    ! [A_564,B_565] :
      ( k7_tmap_1(A_564,u1_struct_0(B_565)) = k9_tmap_1(A_564,B_565)
      | ~ m1_subset_1(k7_tmap_1(A_564,u1_struct_0(B_565)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_564),u1_struct_0(k6_tmap_1(A_564,u1_struct_0(B_565))))))
      | ~ v1_funct_2(k7_tmap_1(A_564,u1_struct_0(B_565)),u1_struct_0(A_564),u1_struct_0(k6_tmap_1(A_564,u1_struct_0(B_565))))
      | ~ v1_funct_1(k7_tmap_1(A_564,u1_struct_0(B_565)))
      | v1_xboole_0(u1_struct_0(k6_tmap_1(A_564,u1_struct_0(B_565))))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_564,B_565)))
      | ~ m1_subset_1(u1_struct_0(B_565),k1_zfmisc_1(u1_struct_0(A_564)))
      | ~ m1_subset_1(k9_tmap_1(A_564,B_565),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_564),u1_struct_0(k8_tmap_1(A_564,B_565)))))
      | ~ v1_funct_2(k9_tmap_1(A_564,B_565),u1_struct_0(A_564),u1_struct_0(k8_tmap_1(A_564,B_565)))
      | ~ v1_funct_1(k9_tmap_1(A_564,B_565))
      | ~ m1_pre_topc(B_565,A_564)
      | ~ l1_pre_topc(A_564)
      | ~ v2_pre_topc(A_564)
      | v2_struct_0(A_564) ) ),
    inference(resolution,[status(thm)],[c_1892,c_12])).

tff(c_2445,plain,(
    ! [A_621,B_622] :
      ( k7_tmap_1(A_621,u1_struct_0(B_622)) = k9_tmap_1(A_621,B_622)
      | ~ v1_funct_2(k7_tmap_1(A_621,u1_struct_0(B_622)),u1_struct_0(A_621),u1_struct_0(k6_tmap_1(A_621,u1_struct_0(B_622))))
      | ~ v1_funct_1(k7_tmap_1(A_621,u1_struct_0(B_622)))
      | v1_xboole_0(u1_struct_0(k6_tmap_1(A_621,u1_struct_0(B_622))))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_621,B_622)))
      | ~ m1_subset_1(k9_tmap_1(A_621,B_622),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_621),u1_struct_0(k8_tmap_1(A_621,B_622)))))
      | ~ v1_funct_2(k9_tmap_1(A_621,B_622),u1_struct_0(A_621),u1_struct_0(k8_tmap_1(A_621,B_622)))
      | ~ v1_funct_1(k9_tmap_1(A_621,B_622))
      | ~ m1_pre_topc(B_622,A_621)
      | ~ m1_subset_1(u1_struct_0(B_622),k1_zfmisc_1(u1_struct_0(A_621)))
      | ~ l1_pre_topc(A_621)
      | ~ v2_pre_topc(A_621)
      | v2_struct_0(A_621) ) ),
    inference(resolution,[status(thm)],[c_32,c_2182])).

tff(c_2514,plain,(
    ! [A_638,B_639] :
      ( k7_tmap_1(A_638,u1_struct_0(B_639)) = k9_tmap_1(A_638,B_639)
      | ~ v1_funct_1(k7_tmap_1(A_638,u1_struct_0(B_639)))
      | v1_xboole_0(u1_struct_0(k6_tmap_1(A_638,u1_struct_0(B_639))))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_638,B_639)))
      | ~ m1_subset_1(k9_tmap_1(A_638,B_639),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_638),u1_struct_0(k8_tmap_1(A_638,B_639)))))
      | ~ v1_funct_2(k9_tmap_1(A_638,B_639),u1_struct_0(A_638),u1_struct_0(k8_tmap_1(A_638,B_639)))
      | ~ v1_funct_1(k9_tmap_1(A_638,B_639))
      | ~ m1_pre_topc(B_639,A_638)
      | ~ m1_subset_1(u1_struct_0(B_639),k1_zfmisc_1(u1_struct_0(A_638)))
      | ~ l1_pre_topc(A_638)
      | ~ v2_pre_topc(A_638)
      | v2_struct_0(A_638) ) ),
    inference(resolution,[status(thm)],[c_34,c_2445])).

tff(c_2519,plain,(
    ! [A_640,B_641] :
      ( k7_tmap_1(A_640,u1_struct_0(B_641)) = k9_tmap_1(A_640,B_641)
      | ~ v1_funct_1(k7_tmap_1(A_640,u1_struct_0(B_641)))
      | v1_xboole_0(u1_struct_0(k6_tmap_1(A_640,u1_struct_0(B_641))))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_640,B_641)))
      | ~ v1_funct_2(k9_tmap_1(A_640,B_641),u1_struct_0(A_640),u1_struct_0(k8_tmap_1(A_640,B_641)))
      | ~ v1_funct_1(k9_tmap_1(A_640,B_641))
      | ~ m1_subset_1(u1_struct_0(B_641),k1_zfmisc_1(u1_struct_0(A_640)))
      | ~ m1_pre_topc(B_641,A_640)
      | ~ l1_pre_topc(A_640)
      | ~ v2_pre_topc(A_640)
      | v2_struct_0(A_640) ) ),
    inference(resolution,[status(thm)],[c_44,c_2514])).

tff(c_2524,plain,(
    ! [A_642,B_643] :
      ( k7_tmap_1(A_642,u1_struct_0(B_643)) = k9_tmap_1(A_642,B_643)
      | ~ v1_funct_1(k7_tmap_1(A_642,u1_struct_0(B_643)))
      | v1_xboole_0(u1_struct_0(k6_tmap_1(A_642,u1_struct_0(B_643))))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_642,B_643)))
      | ~ v1_funct_1(k9_tmap_1(A_642,B_643))
      | ~ m1_subset_1(u1_struct_0(B_643),k1_zfmisc_1(u1_struct_0(A_642)))
      | ~ m1_pre_topc(B_643,A_642)
      | ~ l1_pre_topc(A_642)
      | ~ v2_pre_topc(A_642)
      | v2_struct_0(A_642) ) ),
    inference(resolution,[status(thm)],[c_46,c_2519])).

tff(c_2529,plain,(
    ! [A_644,B_645] :
      ( k7_tmap_1(A_644,u1_struct_0(B_645)) = k9_tmap_1(A_644,B_645)
      | ~ v1_funct_1(k7_tmap_1(A_644,u1_struct_0(B_645)))
      | v1_xboole_0(u1_struct_0(k6_tmap_1(A_644,u1_struct_0(B_645))))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_644,B_645)))
      | ~ v1_funct_1(k9_tmap_1(A_644,B_645))
      | ~ v2_pre_topc(A_644)
      | v2_struct_0(A_644)
      | ~ m1_pre_topc(B_645,A_644)
      | ~ l1_pre_topc(A_644) ) ),
    inference(resolution,[status(thm)],[c_64,c_2524])).

tff(c_2535,plain,(
    ! [A_60,B_61] :
      ( k7_tmap_1(A_60,u1_struct_0(B_61)) = k9_tmap_1(A_60,B_61)
      | ~ v1_funct_1(k7_tmap_1(A_60,u1_struct_0(B_61)))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_60,B_61)))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_60,B_61)))
      | ~ v1_funct_1(k9_tmap_1(A_60,B_61))
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60)
      | ~ m1_pre_topc(B_61,A_60)
      | ~ l1_pre_topc(A_60)
      | ~ m1_pre_topc(B_61,A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1725,c_2529])).

tff(c_2554,plain,(
    ! [A_650,B_651] :
      ( k7_tmap_1(A_650,u1_struct_0(B_651)) = k9_tmap_1(A_650,B_651)
      | ~ v1_funct_1(k7_tmap_1(A_650,u1_struct_0(B_651)))
      | ~ v1_funct_1(k9_tmap_1(A_650,B_651))
      | ~ m1_pre_topc(B_651,A_650)
      | ~ l1_pre_topc(A_650)
      | ~ v2_pre_topc(A_650)
      | v2_struct_0(A_650)
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_650,B_651))) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_2535])).

tff(c_2559,plain,(
    ! [A_652,B_653] :
      ( ~ l1_struct_0(k8_tmap_1(A_652,B_653))
      | v2_struct_0(k8_tmap_1(A_652,B_653))
      | k7_tmap_1(A_652,u1_struct_0(B_653)) = k9_tmap_1(A_652,B_653)
      | ~ v1_funct_1(k7_tmap_1(A_652,u1_struct_0(B_653)))
      | ~ v1_funct_1(k9_tmap_1(A_652,B_653))
      | ~ m1_pre_topc(B_653,A_652)
      | ~ l1_pre_topc(A_652)
      | ~ v2_pre_topc(A_652)
      | v2_struct_0(A_652) ) ),
    inference(resolution,[status(thm)],[c_2554,c_4])).

tff(c_2577,plain,(
    ! [A_658,B_659] :
      ( ~ l1_struct_0(k8_tmap_1(A_658,B_659))
      | v2_struct_0(k8_tmap_1(A_658,B_659))
      | k7_tmap_1(A_658,u1_struct_0(B_659)) = k9_tmap_1(A_658,B_659)
      | ~ v1_funct_1(k9_tmap_1(A_658,B_659))
      | ~ v2_pre_topc(A_658)
      | v2_struct_0(A_658)
      | ~ m1_pre_topc(B_659,A_658)
      | ~ l1_pre_topc(A_658) ) ),
    inference(resolution,[status(thm)],[c_1591,c_2559])).

tff(c_2582,plain,(
    ! [A_660,B_661] :
      ( ~ l1_struct_0(k8_tmap_1(A_660,B_661))
      | k7_tmap_1(A_660,u1_struct_0(B_661)) = k9_tmap_1(A_660,B_661)
      | ~ v1_funct_1(k9_tmap_1(A_660,B_661))
      | ~ v2_pre_topc(A_660)
      | v2_struct_0(A_660)
      | ~ m1_pre_topc(B_661,A_660)
      | ~ l1_pre_topc(A_660) ) ),
    inference(resolution,[status(thm)],[c_2577,c_54])).

tff(c_2587,plain,(
    ! [A_662,B_663] :
      ( ~ l1_struct_0(k8_tmap_1(A_662,B_663))
      | k7_tmap_1(A_662,u1_struct_0(B_663)) = k9_tmap_1(A_662,B_663)
      | ~ m1_pre_topc(B_663,A_662)
      | ~ l1_pre_topc(A_662)
      | ~ v2_pre_topc(A_662)
      | v2_struct_0(A_662) ) ),
    inference(resolution,[status(thm)],[c_48,c_2582])).

tff(c_2592,plain,(
    ! [A_664,B_665] :
      ( k7_tmap_1(A_664,u1_struct_0(B_665)) = k9_tmap_1(A_664,B_665)
      | ~ m1_pre_topc(B_665,A_664)
      | ~ l1_pre_topc(A_664)
      | ~ v2_pre_topc(A_664)
      | v2_struct_0(A_664)
      | ~ l1_pre_topc(k8_tmap_1(A_664,B_665)) ) ),
    inference(resolution,[status(thm)],[c_2,c_2587])).

tff(c_2597,plain,(
    ! [A_666,B_667] :
      ( k7_tmap_1(A_666,u1_struct_0(B_667)) = k9_tmap_1(A_666,B_667)
      | ~ m1_pre_topc(B_667,A_666)
      | ~ l1_pre_topc(A_666)
      | ~ v2_pre_topc(A_666)
      | v2_struct_0(A_666) ) ),
    inference(resolution,[status(thm)],[c_38,c_2592])).

tff(c_1595,plain,(
    ! [A_397,B_398] :
      ( k7_tmap_1(A_397,B_398) = k6_partfun1(u1_struct_0(A_397))
      | ~ m1_subset_1(B_398,k1_zfmisc_1(u1_struct_0(A_397)))
      | ~ l1_pre_topc(A_397)
      | ~ v2_pre_topc(A_397)
      | v2_struct_0(A_397) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1602,plain,(
    ! [A_73,B_75] :
      ( k7_tmap_1(A_73,u1_struct_0(B_75)) = k6_partfun1(u1_struct_0(A_73))
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73)
      | ~ m1_pre_topc(B_75,A_73)
      | ~ l1_pre_topc(A_73) ) ),
    inference(resolution,[status(thm)],[c_64,c_1595])).

tff(c_2687,plain,(
    ! [A_668,B_669] :
      ( k9_tmap_1(A_668,B_669) = k6_partfun1(u1_struct_0(A_668))
      | ~ v2_pre_topc(A_668)
      | v2_struct_0(A_668)
      | ~ m1_pre_topc(B_669,A_668)
      | ~ l1_pre_topc(A_668)
      | ~ m1_pre_topc(B_669,A_668)
      | ~ l1_pre_topc(A_668)
      | ~ v2_pre_topc(A_668)
      | v2_struct_0(A_668) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2597,c_1602])).

tff(c_2689,plain,
    ( k6_partfun1(u1_struct_0('#skF_4')) = k9_tmap_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_2687])).

tff(c_2692,plain,
    ( k6_partfun1(u1_struct_0('#skF_4')) = k9_tmap_1('#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_2689])).

tff(c_2693,plain,(
    k6_partfun1(u1_struct_0('#skF_4')) = k9_tmap_1('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2692])).

tff(c_1786,plain,(
    ! [A_465,C_466] :
      ( m1_subset_1(k2_tmap_1(A_465,k6_tmap_1(A_465,u1_struct_0(C_466)),k7_tmap_1(A_465,u1_struct_0(C_466)),C_466),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_466),u1_struct_0(k6_tmap_1(A_465,u1_struct_0(C_466))))))
      | ~ m1_pre_topc(C_466,A_465)
      | v2_struct_0(C_466)
      | ~ m1_subset_1(u1_struct_0(C_466),k1_zfmisc_1(u1_struct_0(A_465)))
      | ~ l1_pre_topc(A_465)
      | ~ v2_pre_topc(A_465)
      | v2_struct_0(A_465) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_2005,plain,(
    ! [A_535,B_536] :
      ( m1_subset_1(k2_tmap_1(A_535,k6_tmap_1(A_535,u1_struct_0(B_536)),k6_partfun1(u1_struct_0(A_535)),B_536),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_536),u1_struct_0(k6_tmap_1(A_535,u1_struct_0(B_536))))))
      | ~ m1_pre_topc(B_536,A_535)
      | v2_struct_0(B_536)
      | ~ m1_subset_1(u1_struct_0(B_536),k1_zfmisc_1(u1_struct_0(A_535)))
      | ~ l1_pre_topc(A_535)
      | ~ v2_pre_topc(A_535)
      | v2_struct_0(A_535)
      | ~ v2_pre_topc(A_535)
      | v2_struct_0(A_535)
      | ~ m1_pre_topc(B_536,A_535)
      | ~ l1_pre_topc(A_535) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1602,c_1786])).

tff(c_2368,plain,(
    ! [A_598,B_599] :
      ( m1_subset_1(k2_tmap_1(A_598,k8_tmap_1(A_598,B_599),k6_partfun1(u1_struct_0(A_598)),B_599),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_599),u1_struct_0(k6_tmap_1(A_598,u1_struct_0(B_599))))))
      | ~ m1_pre_topc(B_599,A_598)
      | v2_struct_0(B_599)
      | ~ m1_subset_1(u1_struct_0(B_599),k1_zfmisc_1(u1_struct_0(A_598)))
      | ~ l1_pre_topc(A_598)
      | ~ v2_pre_topc(A_598)
      | v2_struct_0(A_598)
      | ~ v2_pre_topc(A_598)
      | v2_struct_0(A_598)
      | ~ m1_pre_topc(B_599,A_598)
      | ~ l1_pre_topc(A_598)
      | ~ m1_pre_topc(B_599,A_598)
      | ~ l1_pre_topc(A_598)
      | ~ v2_pre_topc(A_598)
      | v2_struct_0(A_598) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1725,c_2005])).

tff(c_2373,plain,(
    ! [A_60,B_61] :
      ( m1_subset_1(k2_tmap_1(A_60,k8_tmap_1(A_60,B_61),k6_partfun1(u1_struct_0(A_60)),B_61),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_61),u1_struct_0(k8_tmap_1(A_60,B_61)))))
      | ~ m1_pre_topc(B_61,A_60)
      | v2_struct_0(B_61)
      | ~ m1_subset_1(u1_struct_0(B_61),k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60)
      | ~ m1_pre_topc(B_61,A_60)
      | ~ l1_pre_topc(A_60)
      | ~ m1_pre_topc(B_61,A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60)
      | ~ m1_pre_topc(B_61,A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1725,c_2368])).

tff(c_2703,plain,(
    ! [B_61] :
      ( m1_subset_1(k2_tmap_1('#skF_4',k8_tmap_1('#skF_4',B_61),k9_tmap_1('#skF_4','#skF_5'),B_61),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_61),u1_struct_0(k8_tmap_1('#skF_4',B_61)))))
      | ~ m1_pre_topc(B_61,'#skF_4')
      | v2_struct_0(B_61)
      | ~ m1_subset_1(u1_struct_0(B_61),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_61,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ m1_pre_topc(B_61,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_61,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2693,c_2373])).

tff(c_2809,plain,(
    ! [B_61] :
      ( m1_subset_1(k2_tmap_1('#skF_4',k8_tmap_1('#skF_4',B_61),k9_tmap_1('#skF_4','#skF_5'),B_61),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_61),u1_struct_0(k8_tmap_1('#skF_4',B_61)))))
      | v2_struct_0(B_61)
      | ~ m1_subset_1(u1_struct_0(B_61),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_61,'#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_74,c_72,c_72,c_74,c_74,c_72,c_2703])).

tff(c_3454,plain,(
    ! [B_703] :
      ( m1_subset_1(k2_tmap_1('#skF_4',k8_tmap_1('#skF_4',B_703),k9_tmap_1('#skF_4','#skF_5'),B_703),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_703),u1_struct_0(k8_tmap_1('#skF_4',B_703)))))
      | v2_struct_0(B_703)
      | ~ m1_subset_1(u1_struct_0(B_703),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_703,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2809])).

tff(c_88,plain,(
    ! [A_93,B_94] :
      ( v1_funct_1(k7_tmap_1(A_93,B_94))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_95,plain,(
    ! [A_73,B_75] :
      ( v1_funct_1(k7_tmap_1(A_73,u1_struct_0(B_75)))
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73)
      | ~ m1_pre_topc(B_75,A_73)
      | ~ l1_pre_topc(A_73) ) ),
    inference(resolution,[status(thm)],[c_64,c_88])).

tff(c_210,plain,(
    ! [A_140,B_141] :
      ( k6_tmap_1(A_140,u1_struct_0(B_141)) = k8_tmap_1(A_140,B_141)
      | ~ m1_subset_1(u1_struct_0(B_141),k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_pre_topc(k8_tmap_1(A_140,B_141))
      | ~ v2_pre_topc(k8_tmap_1(A_140,B_141))
      | ~ v1_pre_topc(k8_tmap_1(A_140,B_141))
      | ~ m1_pre_topc(B_141,A_140)
      | ~ l1_pre_topc(A_140)
      | ~ v2_pre_topc(A_140)
      | v2_struct_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_215,plain,(
    ! [A_142,B_143] :
      ( k6_tmap_1(A_142,u1_struct_0(B_143)) = k8_tmap_1(A_142,B_143)
      | ~ l1_pre_topc(k8_tmap_1(A_142,B_143))
      | ~ v2_pre_topc(k8_tmap_1(A_142,B_143))
      | ~ v1_pre_topc(k8_tmap_1(A_142,B_143))
      | ~ v2_pre_topc(A_142)
      | v2_struct_0(A_142)
      | ~ m1_pre_topc(B_143,A_142)
      | ~ l1_pre_topc(A_142) ) ),
    inference(resolution,[status(thm)],[c_64,c_210])).

tff(c_220,plain,(
    ! [A_144,B_145] :
      ( k6_tmap_1(A_144,u1_struct_0(B_145)) = k8_tmap_1(A_144,B_145)
      | ~ l1_pre_topc(k8_tmap_1(A_144,B_145))
      | ~ v1_pre_topc(k8_tmap_1(A_144,B_145))
      | ~ m1_pre_topc(B_145,A_144)
      | ~ l1_pre_topc(A_144)
      | ~ v2_pre_topc(A_144)
      | v2_struct_0(A_144) ) ),
    inference(resolution,[status(thm)],[c_50,c_215])).

tff(c_229,plain,(
    ! [A_148,B_149] :
      ( k6_tmap_1(A_148,u1_struct_0(B_149)) = k8_tmap_1(A_148,B_149)
      | ~ l1_pre_topc(k8_tmap_1(A_148,B_149))
      | ~ m1_pre_topc(B_149,A_148)
      | ~ l1_pre_topc(A_148)
      | ~ v2_pre_topc(A_148)
      | v2_struct_0(A_148) ) ),
    inference(resolution,[status(thm)],[c_52,c_220])).

tff(c_233,plain,(
    ! [A_60,B_61] :
      ( k6_tmap_1(A_60,u1_struct_0(B_61)) = k8_tmap_1(A_60,B_61)
      | ~ m1_pre_topc(B_61,A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_38,c_229])).

tff(c_396,plain,(
    ! [A_203,B_204] :
      ( r1_funct_2(u1_struct_0(A_203),u1_struct_0(k8_tmap_1(A_203,B_204)),u1_struct_0(A_203),u1_struct_0(k6_tmap_1(A_203,u1_struct_0(B_204))),k9_tmap_1(A_203,B_204),k7_tmap_1(A_203,u1_struct_0(B_204)))
      | ~ m1_subset_1(u1_struct_0(B_204),k1_zfmisc_1(u1_struct_0(A_203)))
      | ~ m1_subset_1(k9_tmap_1(A_203,B_204),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_203),u1_struct_0(k8_tmap_1(A_203,B_204)))))
      | ~ v1_funct_2(k9_tmap_1(A_203,B_204),u1_struct_0(A_203),u1_struct_0(k8_tmap_1(A_203,B_204)))
      | ~ v1_funct_1(k9_tmap_1(A_203,B_204))
      | ~ m1_pre_topc(B_204,A_203)
      | ~ l1_pre_topc(A_203)
      | ~ v2_pre_topc(A_203)
      | v2_struct_0(A_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_649,plain,(
    ! [A_256,B_257] :
      ( k7_tmap_1(A_256,u1_struct_0(B_257)) = k9_tmap_1(A_256,B_257)
      | ~ m1_subset_1(k7_tmap_1(A_256,u1_struct_0(B_257)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_256),u1_struct_0(k6_tmap_1(A_256,u1_struct_0(B_257))))))
      | ~ v1_funct_2(k7_tmap_1(A_256,u1_struct_0(B_257)),u1_struct_0(A_256),u1_struct_0(k6_tmap_1(A_256,u1_struct_0(B_257))))
      | ~ v1_funct_1(k7_tmap_1(A_256,u1_struct_0(B_257)))
      | v1_xboole_0(u1_struct_0(k6_tmap_1(A_256,u1_struct_0(B_257))))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_256,B_257)))
      | ~ m1_subset_1(u1_struct_0(B_257),k1_zfmisc_1(u1_struct_0(A_256)))
      | ~ m1_subset_1(k9_tmap_1(A_256,B_257),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_256),u1_struct_0(k8_tmap_1(A_256,B_257)))))
      | ~ v1_funct_2(k9_tmap_1(A_256,B_257),u1_struct_0(A_256),u1_struct_0(k8_tmap_1(A_256,B_257)))
      | ~ v1_funct_1(k9_tmap_1(A_256,B_257))
      | ~ m1_pre_topc(B_257,A_256)
      | ~ l1_pre_topc(A_256)
      | ~ v2_pre_topc(A_256)
      | v2_struct_0(A_256) ) ),
    inference(resolution,[status(thm)],[c_396,c_12])).

tff(c_974,plain,(
    ! [A_329,B_330] :
      ( k7_tmap_1(A_329,u1_struct_0(B_330)) = k9_tmap_1(A_329,B_330)
      | ~ v1_funct_2(k7_tmap_1(A_329,u1_struct_0(B_330)),u1_struct_0(A_329),u1_struct_0(k6_tmap_1(A_329,u1_struct_0(B_330))))
      | ~ v1_funct_1(k7_tmap_1(A_329,u1_struct_0(B_330)))
      | v1_xboole_0(u1_struct_0(k6_tmap_1(A_329,u1_struct_0(B_330))))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_329,B_330)))
      | ~ m1_subset_1(k9_tmap_1(A_329,B_330),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_329),u1_struct_0(k8_tmap_1(A_329,B_330)))))
      | ~ v1_funct_2(k9_tmap_1(A_329,B_330),u1_struct_0(A_329),u1_struct_0(k8_tmap_1(A_329,B_330)))
      | ~ v1_funct_1(k9_tmap_1(A_329,B_330))
      | ~ m1_pre_topc(B_330,A_329)
      | ~ m1_subset_1(u1_struct_0(B_330),k1_zfmisc_1(u1_struct_0(A_329)))
      | ~ l1_pre_topc(A_329)
      | ~ v2_pre_topc(A_329)
      | v2_struct_0(A_329) ) ),
    inference(resolution,[status(thm)],[c_32,c_649])).

tff(c_1018,plain,(
    ! [A_339,B_340] :
      ( k7_tmap_1(A_339,u1_struct_0(B_340)) = k9_tmap_1(A_339,B_340)
      | ~ v1_funct_1(k7_tmap_1(A_339,u1_struct_0(B_340)))
      | v1_xboole_0(u1_struct_0(k6_tmap_1(A_339,u1_struct_0(B_340))))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_339,B_340)))
      | ~ m1_subset_1(k9_tmap_1(A_339,B_340),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_339),u1_struct_0(k8_tmap_1(A_339,B_340)))))
      | ~ v1_funct_2(k9_tmap_1(A_339,B_340),u1_struct_0(A_339),u1_struct_0(k8_tmap_1(A_339,B_340)))
      | ~ v1_funct_1(k9_tmap_1(A_339,B_340))
      | ~ m1_pre_topc(B_340,A_339)
      | ~ m1_subset_1(u1_struct_0(B_340),k1_zfmisc_1(u1_struct_0(A_339)))
      | ~ l1_pre_topc(A_339)
      | ~ v2_pre_topc(A_339)
      | v2_struct_0(A_339) ) ),
    inference(resolution,[status(thm)],[c_34,c_974])).

tff(c_1023,plain,(
    ! [A_341,B_342] :
      ( k7_tmap_1(A_341,u1_struct_0(B_342)) = k9_tmap_1(A_341,B_342)
      | ~ v1_funct_1(k7_tmap_1(A_341,u1_struct_0(B_342)))
      | v1_xboole_0(u1_struct_0(k6_tmap_1(A_341,u1_struct_0(B_342))))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_341,B_342)))
      | ~ v1_funct_2(k9_tmap_1(A_341,B_342),u1_struct_0(A_341),u1_struct_0(k8_tmap_1(A_341,B_342)))
      | ~ v1_funct_1(k9_tmap_1(A_341,B_342))
      | ~ m1_subset_1(u1_struct_0(B_342),k1_zfmisc_1(u1_struct_0(A_341)))
      | ~ m1_pre_topc(B_342,A_341)
      | ~ l1_pre_topc(A_341)
      | ~ v2_pre_topc(A_341)
      | v2_struct_0(A_341) ) ),
    inference(resolution,[status(thm)],[c_44,c_1018])).

tff(c_1028,plain,(
    ! [A_343,B_344] :
      ( k7_tmap_1(A_343,u1_struct_0(B_344)) = k9_tmap_1(A_343,B_344)
      | ~ v1_funct_1(k7_tmap_1(A_343,u1_struct_0(B_344)))
      | v1_xboole_0(u1_struct_0(k6_tmap_1(A_343,u1_struct_0(B_344))))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_343,B_344)))
      | ~ v1_funct_1(k9_tmap_1(A_343,B_344))
      | ~ m1_subset_1(u1_struct_0(B_344),k1_zfmisc_1(u1_struct_0(A_343)))
      | ~ m1_pre_topc(B_344,A_343)
      | ~ l1_pre_topc(A_343)
      | ~ v2_pre_topc(A_343)
      | v2_struct_0(A_343) ) ),
    inference(resolution,[status(thm)],[c_46,c_1023])).

tff(c_1033,plain,(
    ! [A_345,B_346] :
      ( k7_tmap_1(A_345,u1_struct_0(B_346)) = k9_tmap_1(A_345,B_346)
      | ~ v1_funct_1(k7_tmap_1(A_345,u1_struct_0(B_346)))
      | v1_xboole_0(u1_struct_0(k6_tmap_1(A_345,u1_struct_0(B_346))))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_345,B_346)))
      | ~ v1_funct_1(k9_tmap_1(A_345,B_346))
      | ~ v2_pre_topc(A_345)
      | v2_struct_0(A_345)
      | ~ m1_pre_topc(B_346,A_345)
      | ~ l1_pre_topc(A_345) ) ),
    inference(resolution,[status(thm)],[c_64,c_1028])).

tff(c_1039,plain,(
    ! [A_60,B_61] :
      ( k7_tmap_1(A_60,u1_struct_0(B_61)) = k9_tmap_1(A_60,B_61)
      | ~ v1_funct_1(k7_tmap_1(A_60,u1_struct_0(B_61)))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_60,B_61)))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_60,B_61)))
      | ~ v1_funct_1(k9_tmap_1(A_60,B_61))
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60)
      | ~ m1_pre_topc(B_61,A_60)
      | ~ l1_pre_topc(A_60)
      | ~ m1_pre_topc(B_61,A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_1033])).

tff(c_1068,plain,(
    ! [A_355,B_356] :
      ( k7_tmap_1(A_355,u1_struct_0(B_356)) = k9_tmap_1(A_355,B_356)
      | ~ v1_funct_1(k7_tmap_1(A_355,u1_struct_0(B_356)))
      | ~ v1_funct_1(k9_tmap_1(A_355,B_356))
      | ~ m1_pre_topc(B_356,A_355)
      | ~ l1_pre_topc(A_355)
      | ~ v2_pre_topc(A_355)
      | v2_struct_0(A_355)
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_355,B_356))) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_1039])).

tff(c_1073,plain,(
    ! [A_357,B_358] :
      ( ~ l1_struct_0(k8_tmap_1(A_357,B_358))
      | v2_struct_0(k8_tmap_1(A_357,B_358))
      | k7_tmap_1(A_357,u1_struct_0(B_358)) = k9_tmap_1(A_357,B_358)
      | ~ v1_funct_1(k7_tmap_1(A_357,u1_struct_0(B_358)))
      | ~ v1_funct_1(k9_tmap_1(A_357,B_358))
      | ~ m1_pre_topc(B_358,A_357)
      | ~ l1_pre_topc(A_357)
      | ~ v2_pre_topc(A_357)
      | v2_struct_0(A_357) ) ),
    inference(resolution,[status(thm)],[c_1068,c_4])).

tff(c_1081,plain,(
    ! [A_359,B_360] :
      ( ~ l1_struct_0(k8_tmap_1(A_359,B_360))
      | v2_struct_0(k8_tmap_1(A_359,B_360))
      | k7_tmap_1(A_359,u1_struct_0(B_360)) = k9_tmap_1(A_359,B_360)
      | ~ v1_funct_1(k9_tmap_1(A_359,B_360))
      | ~ v2_pre_topc(A_359)
      | v2_struct_0(A_359)
      | ~ m1_pre_topc(B_360,A_359)
      | ~ l1_pre_topc(A_359) ) ),
    inference(resolution,[status(thm)],[c_95,c_1073])).

tff(c_1086,plain,(
    ! [A_361,B_362] :
      ( ~ l1_struct_0(k8_tmap_1(A_361,B_362))
      | k7_tmap_1(A_361,u1_struct_0(B_362)) = k9_tmap_1(A_361,B_362)
      | ~ v1_funct_1(k9_tmap_1(A_361,B_362))
      | ~ v2_pre_topc(A_361)
      | v2_struct_0(A_361)
      | ~ m1_pre_topc(B_362,A_361)
      | ~ l1_pre_topc(A_361) ) ),
    inference(resolution,[status(thm)],[c_1081,c_54])).

tff(c_1091,plain,(
    ! [A_363,B_364] :
      ( ~ l1_struct_0(k8_tmap_1(A_363,B_364))
      | k7_tmap_1(A_363,u1_struct_0(B_364)) = k9_tmap_1(A_363,B_364)
      | ~ m1_pre_topc(B_364,A_363)
      | ~ l1_pre_topc(A_363)
      | ~ v2_pre_topc(A_363)
      | v2_struct_0(A_363) ) ),
    inference(resolution,[status(thm)],[c_48,c_1086])).

tff(c_1096,plain,(
    ! [A_365,B_366] :
      ( k7_tmap_1(A_365,u1_struct_0(B_366)) = k9_tmap_1(A_365,B_366)
      | ~ m1_pre_topc(B_366,A_365)
      | ~ l1_pre_topc(A_365)
      | ~ v2_pre_topc(A_365)
      | v2_struct_0(A_365)
      | ~ l1_pre_topc(k8_tmap_1(A_365,B_366)) ) ),
    inference(resolution,[status(thm)],[c_2,c_1091])).

tff(c_1101,plain,(
    ! [A_367,B_368] :
      ( k7_tmap_1(A_367,u1_struct_0(B_368)) = k9_tmap_1(A_367,B_368)
      | ~ m1_pre_topc(B_368,A_367)
      | ~ l1_pre_topc(A_367)
      | ~ v2_pre_topc(A_367)
      | v2_struct_0(A_367) ) ),
    inference(resolution,[status(thm)],[c_38,c_1096])).

tff(c_98,plain,(
    ! [A_96,B_97] :
      ( k7_tmap_1(A_96,B_97) = k6_partfun1(u1_struct_0(A_96))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96)
      | ~ v2_pre_topc(A_96)
      | v2_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_105,plain,(
    ! [A_73,B_75] :
      ( k7_tmap_1(A_73,u1_struct_0(B_75)) = k6_partfun1(u1_struct_0(A_73))
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73)
      | ~ m1_pre_topc(B_75,A_73)
      | ~ l1_pre_topc(A_73) ) ),
    inference(resolution,[status(thm)],[c_64,c_98])).

tff(c_1204,plain,(
    ! [A_373,B_374] :
      ( k9_tmap_1(A_373,B_374) = k6_partfun1(u1_struct_0(A_373))
      | ~ v2_pre_topc(A_373)
      | v2_struct_0(A_373)
      | ~ m1_pre_topc(B_374,A_373)
      | ~ l1_pre_topc(A_373)
      | ~ m1_pre_topc(B_374,A_373)
      | ~ l1_pre_topc(A_373)
      | ~ v2_pre_topc(A_373)
      | v2_struct_0(A_373) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1101,c_105])).

tff(c_1206,plain,
    ( k6_partfun1(u1_struct_0('#skF_4')) = k9_tmap_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_1204])).

tff(c_1209,plain,
    ( k6_partfun1(u1_struct_0('#skF_4')) = k9_tmap_1('#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_1206])).

tff(c_1210,plain,(
    k6_partfun1(u1_struct_0('#skF_4')) = k9_tmap_1('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1209])).

tff(c_170,plain,(
    ! [A_124,C_125] :
      ( v1_funct_1(k2_tmap_1(A_124,k6_tmap_1(A_124,u1_struct_0(C_125)),k7_tmap_1(A_124,u1_struct_0(C_125)),C_125))
      | ~ m1_pre_topc(C_125,A_124)
      | v2_struct_0(C_125)
      | ~ m1_subset_1(u1_struct_0(C_125),k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_pre_topc(A_124)
      | ~ v2_pre_topc(A_124)
      | v2_struct_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_286,plain,(
    ! [A_164,B_165] :
      ( v1_funct_1(k2_tmap_1(A_164,k6_tmap_1(A_164,u1_struct_0(B_165)),k6_partfun1(u1_struct_0(A_164)),B_165))
      | ~ m1_pre_topc(B_165,A_164)
      | v2_struct_0(B_165)
      | ~ m1_subset_1(u1_struct_0(B_165),k1_zfmisc_1(u1_struct_0(A_164)))
      | ~ l1_pre_topc(A_164)
      | ~ v2_pre_topc(A_164)
      | v2_struct_0(A_164)
      | ~ v2_pre_topc(A_164)
      | v2_struct_0(A_164)
      | ~ m1_pre_topc(B_165,A_164)
      | ~ l1_pre_topc(A_164) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_170])).

tff(c_289,plain,(
    ! [A_60,B_61] :
      ( v1_funct_1(k2_tmap_1(A_60,k8_tmap_1(A_60,B_61),k6_partfun1(u1_struct_0(A_60)),B_61))
      | ~ m1_pre_topc(B_61,A_60)
      | v2_struct_0(B_61)
      | ~ m1_subset_1(u1_struct_0(B_61),k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60)
      | ~ m1_pre_topc(B_61,A_60)
      | ~ l1_pre_topc(A_60)
      | ~ m1_pre_topc(B_61,A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_286])).

tff(c_1286,plain,(
    ! [B_61] :
      ( v1_funct_1(k2_tmap_1('#skF_4',k8_tmap_1('#skF_4',B_61),k9_tmap_1('#skF_4','#skF_5'),B_61))
      | ~ m1_pre_topc(B_61,'#skF_4')
      | v2_struct_0(B_61)
      | ~ m1_subset_1(u1_struct_0(B_61),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_61,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ m1_pre_topc(B_61,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1210,c_289])).

tff(c_1395,plain,(
    ! [B_61] :
      ( v1_funct_1(k2_tmap_1('#skF_4',k8_tmap_1('#skF_4',B_61),k9_tmap_1('#skF_4','#skF_5'),B_61))
      | v2_struct_0(B_61)
      | ~ m1_subset_1(u1_struct_0(B_61),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_61,'#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_72,c_74,c_74,c_72,c_1286])).

tff(c_1559,plain,(
    ! [B_378] :
      ( v1_funct_1(k2_tmap_1('#skF_4',k8_tmap_1('#skF_4',B_378),k9_tmap_1('#skF_4','#skF_5'),B_378))
      | v2_struct_0(B_378)
      | ~ m1_subset_1(u1_struct_0(B_378),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_378,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1395])).

tff(c_1562,plain,(
    ! [B_75] :
      ( v1_funct_1(k2_tmap_1('#skF_4',k8_tmap_1('#skF_4',B_75),k9_tmap_1('#skF_4','#skF_5'),B_75))
      | v2_struct_0(B_75)
      | ~ m1_pre_topc(B_75,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_64,c_1559])).

tff(c_1566,plain,(
    ! [B_379] :
      ( v1_funct_1(k2_tmap_1('#skF_4',k8_tmap_1('#skF_4',B_379),k9_tmap_1('#skF_4','#skF_5'),B_379))
      | v2_struct_0(B_379)
      | ~ m1_pre_topc(B_379,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1562])).

tff(c_66,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_4',k8_tmap_1('#skF_4','#skF_5'),k9_tmap_1('#skF_4','#skF_5'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_4','#skF_5')))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_4',k8_tmap_1('#skF_4','#skF_5'),k9_tmap_1('#skF_4','#skF_5'),'#skF_5'),'#skF_5',k8_tmap_1('#skF_4','#skF_5'))
    | ~ v1_funct_2(k2_tmap_1('#skF_4',k8_tmap_1('#skF_4','#skF_5'),k9_tmap_1('#skF_4','#skF_5'),'#skF_5'),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_4','#skF_5')))
    | ~ v1_funct_1(k2_tmap_1('#skF_4',k8_tmap_1('#skF_4','#skF_5'),k9_tmap_1('#skF_4','#skF_5'),'#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_81,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_4',k8_tmap_1('#skF_4','#skF_5'),k9_tmap_1('#skF_4','#skF_5'),'#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_1569,plain,
    ( v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1566,c_81])).

tff(c_1572,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1569])).

tff(c_1574,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1572])).

tff(c_1575,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_4',k8_tmap_1('#skF_4','#skF_5'),k9_tmap_1('#skF_4','#skF_5'),'#skF_5'),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_4','#skF_5')))
    | ~ v5_pre_topc(k2_tmap_1('#skF_4',k8_tmap_1('#skF_4','#skF_5'),k9_tmap_1('#skF_4','#skF_5'),'#skF_5'),'#skF_5',k8_tmap_1('#skF_4','#skF_5'))
    | ~ m1_subset_1(k2_tmap_1('#skF_4',k8_tmap_1('#skF_4','#skF_5'),k9_tmap_1('#skF_4','#skF_5'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_4','#skF_5'))))) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_1581,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_4',k8_tmap_1('#skF_4','#skF_5'),k9_tmap_1('#skF_4','#skF_5'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_4','#skF_5'))))) ),
    inference(splitLeft,[status(thm)],[c_1575])).

tff(c_3467,plain,
    ( v2_struct_0('#skF_5')
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_pre_topc('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_3454,c_1581])).

tff(c_3479,plain,
    ( v2_struct_0('#skF_5')
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3467])).

tff(c_3480,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_3479])).

tff(c_3483,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_3480])).

tff(c_3487,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_3483])).

tff(c_3488,plain,
    ( ~ v5_pre_topc(k2_tmap_1('#skF_4',k8_tmap_1('#skF_4','#skF_5'),k9_tmap_1('#skF_4','#skF_5'),'#skF_5'),'#skF_5',k8_tmap_1('#skF_4','#skF_5'))
    | ~ v1_funct_2(k2_tmap_1('#skF_4',k8_tmap_1('#skF_4','#skF_5'),k9_tmap_1('#skF_4','#skF_5'),'#skF_5'),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_1575])).

tff(c_3563,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_4',k8_tmap_1('#skF_4','#skF_5'),k9_tmap_1('#skF_4','#skF_5'),'#skF_5'),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_3488])).

tff(c_5335,plain,
    ( v2_struct_0('#skF_5')
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_pre_topc('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_5332,c_3563])).

tff(c_5338,plain,
    ( v2_struct_0('#skF_5')
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_5335])).

tff(c_5339,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_5338])).

tff(c_5342,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_5339])).

tff(c_5346,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_5342])).

tff(c_5347,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_4',k8_tmap_1('#skF_4','#skF_5'),k9_tmap_1('#skF_4','#skF_5'),'#skF_5'),'#skF_5',k8_tmap_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_3488])).

tff(c_5405,plain,(
    ! [A_1041,B_1042] :
      ( k6_tmap_1(A_1041,u1_struct_0(B_1042)) = k8_tmap_1(A_1041,B_1042)
      | ~ m1_subset_1(u1_struct_0(B_1042),k1_zfmisc_1(u1_struct_0(A_1041)))
      | ~ l1_pre_topc(k8_tmap_1(A_1041,B_1042))
      | ~ v2_pre_topc(k8_tmap_1(A_1041,B_1042))
      | ~ v1_pre_topc(k8_tmap_1(A_1041,B_1042))
      | ~ m1_pre_topc(B_1042,A_1041)
      | ~ l1_pre_topc(A_1041)
      | ~ v2_pre_topc(A_1041)
      | v2_struct_0(A_1041) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_5410,plain,(
    ! [A_1043,B_1044] :
      ( k6_tmap_1(A_1043,u1_struct_0(B_1044)) = k8_tmap_1(A_1043,B_1044)
      | ~ l1_pre_topc(k8_tmap_1(A_1043,B_1044))
      | ~ v2_pre_topc(k8_tmap_1(A_1043,B_1044))
      | ~ v1_pre_topc(k8_tmap_1(A_1043,B_1044))
      | ~ v2_pre_topc(A_1043)
      | v2_struct_0(A_1043)
      | ~ m1_pre_topc(B_1044,A_1043)
      | ~ l1_pre_topc(A_1043) ) ),
    inference(resolution,[status(thm)],[c_64,c_5405])).

tff(c_5419,plain,(
    ! [A_1047,B_1048] :
      ( k6_tmap_1(A_1047,u1_struct_0(B_1048)) = k8_tmap_1(A_1047,B_1048)
      | ~ l1_pre_topc(k8_tmap_1(A_1047,B_1048))
      | ~ v1_pre_topc(k8_tmap_1(A_1047,B_1048))
      | ~ m1_pre_topc(B_1048,A_1047)
      | ~ l1_pre_topc(A_1047)
      | ~ v2_pre_topc(A_1047)
      | v2_struct_0(A_1047) ) ),
    inference(resolution,[status(thm)],[c_50,c_5410])).

tff(c_5424,plain,(
    ! [A_1049,B_1050] :
      ( k6_tmap_1(A_1049,u1_struct_0(B_1050)) = k8_tmap_1(A_1049,B_1050)
      | ~ l1_pre_topc(k8_tmap_1(A_1049,B_1050))
      | ~ m1_pre_topc(B_1050,A_1049)
      | ~ l1_pre_topc(A_1049)
      | ~ v2_pre_topc(A_1049)
      | v2_struct_0(A_1049) ) ),
    inference(resolution,[status(thm)],[c_52,c_5419])).

tff(c_5428,plain,(
    ! [A_60,B_61] :
      ( k6_tmap_1(A_60,u1_struct_0(B_61)) = k8_tmap_1(A_60,B_61)
      | ~ m1_pre_topc(B_61,A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_38,c_5424])).

tff(c_5625,plain,(
    ! [A_1110,B_1111] :
      ( r1_funct_2(u1_struct_0(A_1110),u1_struct_0(k8_tmap_1(A_1110,B_1111)),u1_struct_0(A_1110),u1_struct_0(k6_tmap_1(A_1110,u1_struct_0(B_1111))),k9_tmap_1(A_1110,B_1111),k7_tmap_1(A_1110,u1_struct_0(B_1111)))
      | ~ m1_subset_1(u1_struct_0(B_1111),k1_zfmisc_1(u1_struct_0(A_1110)))
      | ~ m1_subset_1(k9_tmap_1(A_1110,B_1111),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1110),u1_struct_0(k8_tmap_1(A_1110,B_1111)))))
      | ~ v1_funct_2(k9_tmap_1(A_1110,B_1111),u1_struct_0(A_1110),u1_struct_0(k8_tmap_1(A_1110,B_1111)))
      | ~ v1_funct_1(k9_tmap_1(A_1110,B_1111))
      | ~ m1_pre_topc(B_1111,A_1110)
      | ~ l1_pre_topc(A_1110)
      | ~ v2_pre_topc(A_1110)
      | v2_struct_0(A_1110) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_5883,plain,(
    ! [A_1165,B_1166] :
      ( k7_tmap_1(A_1165,u1_struct_0(B_1166)) = k9_tmap_1(A_1165,B_1166)
      | ~ m1_subset_1(k7_tmap_1(A_1165,u1_struct_0(B_1166)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1165),u1_struct_0(k6_tmap_1(A_1165,u1_struct_0(B_1166))))))
      | ~ v1_funct_2(k7_tmap_1(A_1165,u1_struct_0(B_1166)),u1_struct_0(A_1165),u1_struct_0(k6_tmap_1(A_1165,u1_struct_0(B_1166))))
      | ~ v1_funct_1(k7_tmap_1(A_1165,u1_struct_0(B_1166)))
      | v1_xboole_0(u1_struct_0(k6_tmap_1(A_1165,u1_struct_0(B_1166))))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_1165,B_1166)))
      | ~ m1_subset_1(u1_struct_0(B_1166),k1_zfmisc_1(u1_struct_0(A_1165)))
      | ~ m1_subset_1(k9_tmap_1(A_1165,B_1166),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1165),u1_struct_0(k8_tmap_1(A_1165,B_1166)))))
      | ~ v1_funct_2(k9_tmap_1(A_1165,B_1166),u1_struct_0(A_1165),u1_struct_0(k8_tmap_1(A_1165,B_1166)))
      | ~ v1_funct_1(k9_tmap_1(A_1165,B_1166))
      | ~ m1_pre_topc(B_1166,A_1165)
      | ~ l1_pre_topc(A_1165)
      | ~ v2_pre_topc(A_1165)
      | v2_struct_0(A_1165) ) ),
    inference(resolution,[status(thm)],[c_5625,c_12])).

tff(c_6208,plain,(
    ! [A_1238,B_1239] :
      ( k7_tmap_1(A_1238,u1_struct_0(B_1239)) = k9_tmap_1(A_1238,B_1239)
      | ~ v1_funct_2(k7_tmap_1(A_1238,u1_struct_0(B_1239)),u1_struct_0(A_1238),u1_struct_0(k6_tmap_1(A_1238,u1_struct_0(B_1239))))
      | ~ v1_funct_1(k7_tmap_1(A_1238,u1_struct_0(B_1239)))
      | v1_xboole_0(u1_struct_0(k6_tmap_1(A_1238,u1_struct_0(B_1239))))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_1238,B_1239)))
      | ~ m1_subset_1(k9_tmap_1(A_1238,B_1239),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1238),u1_struct_0(k8_tmap_1(A_1238,B_1239)))))
      | ~ v1_funct_2(k9_tmap_1(A_1238,B_1239),u1_struct_0(A_1238),u1_struct_0(k8_tmap_1(A_1238,B_1239)))
      | ~ v1_funct_1(k9_tmap_1(A_1238,B_1239))
      | ~ m1_pre_topc(B_1239,A_1238)
      | ~ m1_subset_1(u1_struct_0(B_1239),k1_zfmisc_1(u1_struct_0(A_1238)))
      | ~ l1_pre_topc(A_1238)
      | ~ v2_pre_topc(A_1238)
      | v2_struct_0(A_1238) ) ),
    inference(resolution,[status(thm)],[c_32,c_5883])).

tff(c_6252,plain,(
    ! [A_1248,B_1249] :
      ( k7_tmap_1(A_1248,u1_struct_0(B_1249)) = k9_tmap_1(A_1248,B_1249)
      | ~ v1_funct_1(k7_tmap_1(A_1248,u1_struct_0(B_1249)))
      | v1_xboole_0(u1_struct_0(k6_tmap_1(A_1248,u1_struct_0(B_1249))))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_1248,B_1249)))
      | ~ m1_subset_1(k9_tmap_1(A_1248,B_1249),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1248),u1_struct_0(k8_tmap_1(A_1248,B_1249)))))
      | ~ v1_funct_2(k9_tmap_1(A_1248,B_1249),u1_struct_0(A_1248),u1_struct_0(k8_tmap_1(A_1248,B_1249)))
      | ~ v1_funct_1(k9_tmap_1(A_1248,B_1249))
      | ~ m1_pre_topc(B_1249,A_1248)
      | ~ m1_subset_1(u1_struct_0(B_1249),k1_zfmisc_1(u1_struct_0(A_1248)))
      | ~ l1_pre_topc(A_1248)
      | ~ v2_pre_topc(A_1248)
      | v2_struct_0(A_1248) ) ),
    inference(resolution,[status(thm)],[c_34,c_6208])).

tff(c_6257,plain,(
    ! [A_1250,B_1251] :
      ( k7_tmap_1(A_1250,u1_struct_0(B_1251)) = k9_tmap_1(A_1250,B_1251)
      | ~ v1_funct_1(k7_tmap_1(A_1250,u1_struct_0(B_1251)))
      | v1_xboole_0(u1_struct_0(k6_tmap_1(A_1250,u1_struct_0(B_1251))))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_1250,B_1251)))
      | ~ v1_funct_2(k9_tmap_1(A_1250,B_1251),u1_struct_0(A_1250),u1_struct_0(k8_tmap_1(A_1250,B_1251)))
      | ~ v1_funct_1(k9_tmap_1(A_1250,B_1251))
      | ~ m1_subset_1(u1_struct_0(B_1251),k1_zfmisc_1(u1_struct_0(A_1250)))
      | ~ m1_pre_topc(B_1251,A_1250)
      | ~ l1_pre_topc(A_1250)
      | ~ v2_pre_topc(A_1250)
      | v2_struct_0(A_1250) ) ),
    inference(resolution,[status(thm)],[c_44,c_6252])).

tff(c_6262,plain,(
    ! [A_1252,B_1253] :
      ( k7_tmap_1(A_1252,u1_struct_0(B_1253)) = k9_tmap_1(A_1252,B_1253)
      | ~ v1_funct_1(k7_tmap_1(A_1252,u1_struct_0(B_1253)))
      | v1_xboole_0(u1_struct_0(k6_tmap_1(A_1252,u1_struct_0(B_1253))))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_1252,B_1253)))
      | ~ v1_funct_1(k9_tmap_1(A_1252,B_1253))
      | ~ m1_subset_1(u1_struct_0(B_1253),k1_zfmisc_1(u1_struct_0(A_1252)))
      | ~ m1_pre_topc(B_1253,A_1252)
      | ~ l1_pre_topc(A_1252)
      | ~ v2_pre_topc(A_1252)
      | v2_struct_0(A_1252) ) ),
    inference(resolution,[status(thm)],[c_46,c_6257])).

tff(c_6267,plain,(
    ! [A_1254,B_1255] :
      ( k7_tmap_1(A_1254,u1_struct_0(B_1255)) = k9_tmap_1(A_1254,B_1255)
      | ~ v1_funct_1(k7_tmap_1(A_1254,u1_struct_0(B_1255)))
      | v1_xboole_0(u1_struct_0(k6_tmap_1(A_1254,u1_struct_0(B_1255))))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_1254,B_1255)))
      | ~ v1_funct_1(k9_tmap_1(A_1254,B_1255))
      | ~ v2_pre_topc(A_1254)
      | v2_struct_0(A_1254)
      | ~ m1_pre_topc(B_1255,A_1254)
      | ~ l1_pre_topc(A_1254) ) ),
    inference(resolution,[status(thm)],[c_64,c_6262])).

tff(c_6273,plain,(
    ! [A_60,B_61] :
      ( k7_tmap_1(A_60,u1_struct_0(B_61)) = k9_tmap_1(A_60,B_61)
      | ~ v1_funct_1(k7_tmap_1(A_60,u1_struct_0(B_61)))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_60,B_61)))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_60,B_61)))
      | ~ v1_funct_1(k9_tmap_1(A_60,B_61))
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60)
      | ~ m1_pre_topc(B_61,A_60)
      | ~ l1_pre_topc(A_60)
      | ~ m1_pre_topc(B_61,A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5428,c_6267])).

tff(c_6304,plain,(
    ! [A_1264,B_1265] :
      ( k7_tmap_1(A_1264,u1_struct_0(B_1265)) = k9_tmap_1(A_1264,B_1265)
      | ~ v1_funct_1(k7_tmap_1(A_1264,u1_struct_0(B_1265)))
      | ~ v1_funct_1(k9_tmap_1(A_1264,B_1265))
      | ~ m1_pre_topc(B_1265,A_1264)
      | ~ l1_pre_topc(A_1264)
      | ~ v2_pre_topc(A_1264)
      | v2_struct_0(A_1264)
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_1264,B_1265))) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_6273])).

tff(c_1576,plain,(
    v1_funct_1(k2_tmap_1('#skF_4',k8_tmap_1('#skF_4','#skF_5'),k9_tmap_1('#skF_4','#skF_5'),'#skF_5')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_5348,plain,(
    v1_funct_2(k2_tmap_1('#skF_4',k8_tmap_1('#skF_4','#skF_5'),k9_tmap_1('#skF_4','#skF_5'),'#skF_5'),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_3488])).

tff(c_3489,plain,(
    m1_subset_1(k2_tmap_1('#skF_4',k8_tmap_1('#skF_4','#skF_5'),k9_tmap_1('#skF_4','#skF_5'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_4','#skF_5'))))) ),
    inference(splitRight,[status(thm)],[c_1575])).

tff(c_5384,plain,(
    ! [D_1031,B_1033,A_1035,C_1034,F_1032] :
      ( r1_funct_2(A_1035,B_1033,C_1034,D_1031,F_1032,F_1032)
      | ~ m1_subset_1(F_1032,k1_zfmisc_1(k2_zfmisc_1(C_1034,D_1031)))
      | ~ v1_funct_2(F_1032,C_1034,D_1031)
      | ~ m1_subset_1(F_1032,k1_zfmisc_1(k2_zfmisc_1(A_1035,B_1033)))
      | ~ v1_funct_2(F_1032,A_1035,B_1033)
      | ~ v1_funct_1(F_1032)
      | v1_xboole_0(D_1031)
      | v1_xboole_0(B_1033) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_5390,plain,(
    ! [A_1035,B_1033] :
      ( r1_funct_2(A_1035,B_1033,u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_4','#skF_5')),k2_tmap_1('#skF_4',k8_tmap_1('#skF_4','#skF_5'),k9_tmap_1('#skF_4','#skF_5'),'#skF_5'),k2_tmap_1('#skF_4',k8_tmap_1('#skF_4','#skF_5'),k9_tmap_1('#skF_4','#skF_5'),'#skF_5'))
      | ~ v1_funct_2(k2_tmap_1('#skF_4',k8_tmap_1('#skF_4','#skF_5'),k9_tmap_1('#skF_4','#skF_5'),'#skF_5'),u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_4','#skF_5')))
      | ~ m1_subset_1(k2_tmap_1('#skF_4',k8_tmap_1('#skF_4','#skF_5'),k9_tmap_1('#skF_4','#skF_5'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(A_1035,B_1033)))
      | ~ v1_funct_2(k2_tmap_1('#skF_4',k8_tmap_1('#skF_4','#skF_5'),k9_tmap_1('#skF_4','#skF_5'),'#skF_5'),A_1035,B_1033)
      | ~ v1_funct_1(k2_tmap_1('#skF_4',k8_tmap_1('#skF_4','#skF_5'),k9_tmap_1('#skF_4','#skF_5'),'#skF_5'))
      | v1_xboole_0(u1_struct_0(k8_tmap_1('#skF_4','#skF_5')))
      | v1_xboole_0(B_1033) ) ),
    inference(resolution,[status(thm)],[c_3489,c_5384])).

tff(c_5395,plain,(
    ! [A_1035,B_1033] :
      ( r1_funct_2(A_1035,B_1033,u1_struct_0('#skF_5'),u1_struct_0(k8_tmap_1('#skF_4','#skF_5')),k2_tmap_1('#skF_4',k8_tmap_1('#skF_4','#skF_5'),k9_tmap_1('#skF_4','#skF_5'),'#skF_5'),k2_tmap_1('#skF_4',k8_tmap_1('#skF_4','#skF_5'),k9_tmap_1('#skF_4','#skF_5'),'#skF_5'))
      | ~ m1_subset_1(k2_tmap_1('#skF_4',k8_tmap_1('#skF_4','#skF_5'),k9_tmap_1('#skF_4','#skF_5'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(A_1035,B_1033)))
      | ~ v1_funct_2(k2_tmap_1('#skF_4',k8_tmap_1('#skF_4','#skF_5'),k9_tmap_1('#skF_4','#skF_5'),'#skF_5'),A_1035,B_1033)
      | v1_xboole_0(u1_struct_0(k8_tmap_1('#skF_4','#skF_5')))
      | v1_xboole_0(B_1033) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1576,c_5348,c_5390])).

tff(c_5462,plain,(
    v1_xboole_0(u1_struct_0(k8_tmap_1('#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_5395])).

tff(c_5466,plain,
    ( ~ l1_struct_0(k8_tmap_1('#skF_4','#skF_5'))
    | v2_struct_0(k8_tmap_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_5462,c_4])).

tff(c_5467,plain,(
    ~ l1_struct_0(k8_tmap_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_5466])).

tff(c_5471,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_2,c_5467])).

tff(c_5474,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_5471])).

tff(c_5477,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_5474])).

tff(c_5479,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_5477])).

tff(c_5480,plain,(
    v2_struct_0(k8_tmap_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_5466])).

tff(c_5485,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_5480,c_54])).

tff(c_5488,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_5485])).

tff(c_5490,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_5488])).

tff(c_5492,plain,(
    ~ v1_xboole_0(u1_struct_0(k8_tmap_1('#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_5395])).

tff(c_6307,plain,
    ( k7_tmap_1('#skF_4',u1_struct_0('#skF_5')) = k9_tmap_1('#skF_4','#skF_5')
    | ~ v1_funct_1(k7_tmap_1('#skF_4',u1_struct_0('#skF_5')))
    | ~ v1_funct_1(k9_tmap_1('#skF_4','#skF_5'))
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_6304,c_5492])).

tff(c_6313,plain,
    ( k7_tmap_1('#skF_4',u1_struct_0('#skF_5')) = k9_tmap_1('#skF_4','#skF_5')
    | ~ v1_funct_1(k7_tmap_1('#skF_4',u1_struct_0('#skF_5')))
    | ~ v1_funct_1(k9_tmap_1('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_6307])).

tff(c_6314,plain,
    ( k7_tmap_1('#skF_4',u1_struct_0('#skF_5')) = k9_tmap_1('#skF_4','#skF_5')
    | ~ v1_funct_1(k7_tmap_1('#skF_4',u1_struct_0('#skF_5')))
    | ~ v1_funct_1(k9_tmap_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_6313])).

tff(c_6316,plain,(
    ~ v1_funct_1(k9_tmap_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_6314])).

tff(c_6319,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_6316])).

tff(c_6322,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_6319])).

tff(c_6324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_6322])).

tff(c_6325,plain,
    ( ~ v1_funct_1(k7_tmap_1('#skF_4',u1_struct_0('#skF_5')))
    | k7_tmap_1('#skF_4',u1_struct_0('#skF_5')) = k9_tmap_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_6314])).

tff(c_6327,plain,(
    ~ v1_funct_1(k7_tmap_1('#skF_4',u1_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_6325])).

tff(c_6333,plain,
    ( ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_3499,c_6327])).

tff(c_6339,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_74,c_6333])).

tff(c_6341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_6339])).

tff(c_6342,plain,(
    k7_tmap_1('#skF_4',u1_struct_0('#skF_5')) = k9_tmap_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_6325])).

tff(c_5429,plain,(
    ! [A_1051,B_1052] :
      ( k6_tmap_1(A_1051,u1_struct_0(B_1052)) = k8_tmap_1(A_1051,B_1052)
      | ~ m1_pre_topc(B_1052,A_1051)
      | ~ l1_pre_topc(A_1051)
      | ~ v2_pre_topc(A_1051)
      | v2_struct_0(A_1051) ) ),
    inference(resolution,[status(thm)],[c_38,c_5424])).

tff(c_58,plain,(
    ! [A_66,C_72] :
      ( v5_pre_topc(k2_tmap_1(A_66,k6_tmap_1(A_66,u1_struct_0(C_72)),k7_tmap_1(A_66,u1_struct_0(C_72)),C_72),C_72,k6_tmap_1(A_66,u1_struct_0(C_72)))
      | ~ m1_pre_topc(C_72,A_66)
      | v2_struct_0(C_72)
      | ~ m1_subset_1(u1_struct_0(C_72),k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_5618,plain,(
    ! [A_1108,B_1109] :
      ( v5_pre_topc(k2_tmap_1(A_1108,k6_tmap_1(A_1108,u1_struct_0(B_1109)),k7_tmap_1(A_1108,u1_struct_0(B_1109)),B_1109),B_1109,k8_tmap_1(A_1108,B_1109))
      | ~ m1_pre_topc(B_1109,A_1108)
      | v2_struct_0(B_1109)
      | ~ m1_subset_1(u1_struct_0(B_1109),k1_zfmisc_1(u1_struct_0(A_1108)))
      | ~ l1_pre_topc(A_1108)
      | ~ v2_pre_topc(A_1108)
      | v2_struct_0(A_1108)
      | ~ m1_pre_topc(B_1109,A_1108)
      | ~ l1_pre_topc(A_1108)
      | ~ v2_pre_topc(A_1108)
      | v2_struct_0(A_1108) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5429,c_58])).

tff(c_5621,plain,(
    ! [A_60,B_61] :
      ( v5_pre_topc(k2_tmap_1(A_60,k8_tmap_1(A_60,B_61),k7_tmap_1(A_60,u1_struct_0(B_61)),B_61),B_61,k8_tmap_1(A_60,B_61))
      | ~ m1_pre_topc(B_61,A_60)
      | v2_struct_0(B_61)
      | ~ m1_subset_1(u1_struct_0(B_61),k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60)
      | ~ m1_pre_topc(B_61,A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60)
      | ~ m1_pre_topc(B_61,A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5428,c_5618])).

tff(c_6385,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_4',k8_tmap_1('#skF_4','#skF_5'),k9_tmap_1('#skF_4','#skF_5'),'#skF_5'),'#skF_5',k8_tmap_1('#skF_4','#skF_5'))
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | v2_struct_0('#skF_5')
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6342,c_5621])).

tff(c_6491,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_4',k8_tmap_1('#skF_4','#skF_5'),k9_tmap_1('#skF_4','#skF_5'),'#skF_5'),'#skF_5',k8_tmap_1('#skF_4','#skF_5'))
    | v2_struct_0('#skF_5')
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_74,c_72,c_68,c_74,c_72,c_68,c_6385])).

tff(c_6492,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_5347,c_6491])).

tff(c_6577,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_6492])).

tff(c_6581,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_6577])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:28:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.78/3.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.78/3.60  
% 9.78/3.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.78/3.60  %$ r1_funct_2 > v5_pre_topc > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k9_tmap_1 > k8_tmap_1 > k7_tmap_1 > k6_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_partfun1 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 9.78/3.60  
% 9.78/3.60  %Foreground sorts:
% 9.78/3.60  
% 9.78/3.60  
% 9.78/3.60  %Background operators:
% 9.78/3.60  
% 9.78/3.60  
% 9.78/3.60  %Foreground operators:
% 9.78/3.60  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.78/3.60  tff(k7_tmap_1, type, k7_tmap_1: ($i * $i) > $i).
% 9.78/3.60  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.78/3.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.78/3.60  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.78/3.60  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.78/3.60  tff('#skF_5', type, '#skF_5': $i).
% 9.78/3.60  tff(k9_tmap_1, type, k9_tmap_1: ($i * $i) > $i).
% 9.78/3.60  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.78/3.60  tff(k8_tmap_1, type, k8_tmap_1: ($i * $i) > $i).
% 9.78/3.60  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.78/3.60  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 9.78/3.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.78/3.60  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 9.78/3.60  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.78/3.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.78/3.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.78/3.60  tff('#skF_4', type, '#skF_4': $i).
% 9.78/3.60  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 9.78/3.60  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 9.78/3.60  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 9.78/3.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.78/3.60  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 9.78/3.60  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 9.78/3.60  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.78/3.60  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 9.78/3.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.78/3.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.78/3.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.78/3.60  
% 10.04/3.64  tff(f_246, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (((v1_funct_1(k2_tmap_1(A, k8_tmap_1(A, B), k9_tmap_1(A, B), B)) & v1_funct_2(k2_tmap_1(A, k8_tmap_1(A, B), k9_tmap_1(A, B), B), u1_struct_0(B), u1_struct_0(k8_tmap_1(A, B)))) & v5_pre_topc(k2_tmap_1(A, k8_tmap_1(A, B), k9_tmap_1(A, B), B), B, k8_tmap_1(A, B))) & m1_subset_1(k2_tmap_1(A, k8_tmap_1(A, B), k9_tmap_1(A, B), B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(k8_tmap_1(A, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_tmap_1)).
% 10.04/3.64  tff(f_224, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 10.04/3.64  tff(f_160, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_pre_topc(k8_tmap_1(A, B)) & v2_pre_topc(k8_tmap_1(A, B))) & l1_pre_topc(k8_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 10.04/3.64  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 10.04/3.64  tff(f_175, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_funct_1(k9_tmap_1(A, B)) & v1_funct_2(k9_tmap_1(A, B), u1_struct_0(A), u1_struct_0(k8_tmap_1(A, B)))) & m1_subset_1(k9_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k8_tmap_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_tmap_1)).
% 10.04/3.64  tff(f_145, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_funct_1(k7_tmap_1(A, B)) & v1_funct_2(k7_tmap_1(A, B), u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))) & m1_subset_1(k7_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 10.04/3.64  tff(f_191, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((~v2_struct_0(k8_tmap_1(A, B)) & v1_pre_topc(k8_tmap_1(A, B))) & v2_pre_topc(k8_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_tmap_1)).
% 10.04/3.64  tff(f_104, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (((v1_pre_topc(C) & v2_pre_topc(C)) & l1_pre_topc(C)) => ((C = k8_tmap_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((D = u1_struct_0(B)) => (C = k6_tmap_1(A, D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_tmap_1)).
% 10.04/3.64  tff(f_130, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(k8_tmap_1(A, B)))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k8_tmap_1(A, B)))))) => ((C = k9_tmap_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((D = u1_struct_0(B)) => r1_funct_2(u1_struct_0(A), u1_struct_0(k8_tmap_1(A, B)), u1_struct_0(A), u1_struct_0(k6_tmap_1(A, D)), C, k7_tmap_1(A, D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_tmap_1)).
% 10.04/3.64  tff(f_66, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 10.04/3.64  tff(f_37, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 10.04/3.64  tff(f_78, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k7_tmap_1(A, B) = k6_partfun1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_tmap_1)).
% 10.04/3.64  tff(f_217, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => ((u1_struct_0(C) = B) => (((v1_funct_1(k2_tmap_1(A, k6_tmap_1(A, B), k7_tmap_1(A, B), C)) & v1_funct_2(k2_tmap_1(A, k6_tmap_1(A, B), k7_tmap_1(A, B), C), u1_struct_0(C), u1_struct_0(k6_tmap_1(A, B)))) & v5_pre_topc(k2_tmap_1(A, k6_tmap_1(A, B), k7_tmap_1(A, B), C), C, k6_tmap_1(A, B))) & m1_subset_1(k2_tmap_1(A, k6_tmap_1(A, B), k7_tmap_1(A, B), C), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(k6_tmap_1(A, B))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_tmap_1)).
% 10.04/3.64  tff(c_72, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_246])).
% 10.04/3.64  tff(c_68, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_246])).
% 10.04/3.64  tff(c_64, plain, (![B_75, A_73]: (m1_subset_1(u1_struct_0(B_75), k1_zfmisc_1(u1_struct_0(A_73))) | ~m1_pre_topc(B_75, A_73) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_224])).
% 10.04/3.64  tff(c_76, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_246])).
% 10.04/3.64  tff(c_70, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_246])).
% 10.04/3.64  tff(c_74, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_246])).
% 10.04/3.64  tff(c_38, plain, (![A_60, B_61]: (l1_pre_topc(k8_tmap_1(A_60, B_61)) | ~m1_pre_topc(B_61, A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_160])).
% 10.04/3.64  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.04/3.64  tff(c_48, plain, (![A_62, B_63]: (v1_funct_1(k9_tmap_1(A_62, B_63)) | ~m1_pre_topc(B_63, A_62) | ~l1_pre_topc(A_62) | ~v2_pre_topc(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_175])).
% 10.04/3.64  tff(c_3492, plain, (![A_708, B_709]: (v1_funct_1(k7_tmap_1(A_708, B_709)) | ~m1_subset_1(B_709, k1_zfmisc_1(u1_struct_0(A_708))) | ~l1_pre_topc(A_708) | ~v2_pre_topc(A_708) | v2_struct_0(A_708))), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.04/3.64  tff(c_3499, plain, (![A_73, B_75]: (v1_funct_1(k7_tmap_1(A_73, u1_struct_0(B_75))) | ~v2_pre_topc(A_73) | v2_struct_0(A_73) | ~m1_pre_topc(B_75, A_73) | ~l1_pre_topc(A_73))), inference(resolution, [status(thm)], [c_64, c_3492])).
% 10.04/3.64  tff(c_52, plain, (![A_64, B_65]: (v1_pre_topc(k8_tmap_1(A_64, B_65)) | ~m1_pre_topc(B_65, A_64) | ~l1_pre_topc(A_64) | ~v2_pre_topc(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_191])).
% 10.04/3.64  tff(c_50, plain, (![A_64, B_65]: (v2_pre_topc(k8_tmap_1(A_64, B_65)) | ~m1_pre_topc(B_65, A_64) | ~l1_pre_topc(A_64) | ~v2_pre_topc(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_191])).
% 10.04/3.64  tff(c_3620, plain, (![A_755, B_756]: (k6_tmap_1(A_755, u1_struct_0(B_756))=k8_tmap_1(A_755, B_756) | ~m1_subset_1(u1_struct_0(B_756), k1_zfmisc_1(u1_struct_0(A_755))) | ~l1_pre_topc(k8_tmap_1(A_755, B_756)) | ~v2_pre_topc(k8_tmap_1(A_755, B_756)) | ~v1_pre_topc(k8_tmap_1(A_755, B_756)) | ~m1_pre_topc(B_756, A_755) | ~l1_pre_topc(A_755) | ~v2_pre_topc(A_755) | v2_struct_0(A_755))), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.04/3.64  tff(c_3625, plain, (![A_757, B_758]: (k6_tmap_1(A_757, u1_struct_0(B_758))=k8_tmap_1(A_757, B_758) | ~l1_pre_topc(k8_tmap_1(A_757, B_758)) | ~v2_pre_topc(k8_tmap_1(A_757, B_758)) | ~v1_pre_topc(k8_tmap_1(A_757, B_758)) | ~v2_pre_topc(A_757) | v2_struct_0(A_757) | ~m1_pre_topc(B_758, A_757) | ~l1_pre_topc(A_757))), inference(resolution, [status(thm)], [c_64, c_3620])).
% 10.04/3.64  tff(c_3630, plain, (![A_759, B_760]: (k6_tmap_1(A_759, u1_struct_0(B_760))=k8_tmap_1(A_759, B_760) | ~l1_pre_topc(k8_tmap_1(A_759, B_760)) | ~v1_pre_topc(k8_tmap_1(A_759, B_760)) | ~m1_pre_topc(B_760, A_759) | ~l1_pre_topc(A_759) | ~v2_pre_topc(A_759) | v2_struct_0(A_759))), inference(resolution, [status(thm)], [c_50, c_3625])).
% 10.04/3.64  tff(c_3639, plain, (![A_763, B_764]: (k6_tmap_1(A_763, u1_struct_0(B_764))=k8_tmap_1(A_763, B_764) | ~l1_pre_topc(k8_tmap_1(A_763, B_764)) | ~m1_pre_topc(B_764, A_763) | ~l1_pre_topc(A_763) | ~v2_pre_topc(A_763) | v2_struct_0(A_763))), inference(resolution, [status(thm)], [c_52, c_3630])).
% 10.04/3.64  tff(c_3643, plain, (![A_60, B_61]: (k6_tmap_1(A_60, u1_struct_0(B_61))=k8_tmap_1(A_60, B_61) | ~m1_pre_topc(B_61, A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(resolution, [status(thm)], [c_38, c_3639])).
% 10.04/3.64  tff(c_46, plain, (![A_62, B_63]: (v1_funct_2(k9_tmap_1(A_62, B_63), u1_struct_0(A_62), u1_struct_0(k8_tmap_1(A_62, B_63))) | ~m1_pre_topc(B_63, A_62) | ~l1_pre_topc(A_62) | ~v2_pre_topc(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_175])).
% 10.04/3.64  tff(c_44, plain, (![A_62, B_63]: (m1_subset_1(k9_tmap_1(A_62, B_63), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_62), u1_struct_0(k8_tmap_1(A_62, B_63))))) | ~m1_pre_topc(B_63, A_62) | ~l1_pre_topc(A_62) | ~v2_pre_topc(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_175])).
% 10.04/3.64  tff(c_34, plain, (![A_58, B_59]: (v1_funct_2(k7_tmap_1(A_58, B_59), u1_struct_0(A_58), u1_struct_0(k6_tmap_1(A_58, B_59))) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.04/3.64  tff(c_32, plain, (![A_58, B_59]: (m1_subset_1(k7_tmap_1(A_58, B_59), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_58), u1_struct_0(k6_tmap_1(A_58, B_59))))) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.04/3.64  tff(c_3806, plain, (![A_818, B_819]: (r1_funct_2(u1_struct_0(A_818), u1_struct_0(k8_tmap_1(A_818, B_819)), u1_struct_0(A_818), u1_struct_0(k6_tmap_1(A_818, u1_struct_0(B_819))), k9_tmap_1(A_818, B_819), k7_tmap_1(A_818, u1_struct_0(B_819))) | ~m1_subset_1(u1_struct_0(B_819), k1_zfmisc_1(u1_struct_0(A_818))) | ~m1_subset_1(k9_tmap_1(A_818, B_819), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_818), u1_struct_0(k8_tmap_1(A_818, B_819))))) | ~v1_funct_2(k9_tmap_1(A_818, B_819), u1_struct_0(A_818), u1_struct_0(k8_tmap_1(A_818, B_819))) | ~v1_funct_1(k9_tmap_1(A_818, B_819)) | ~m1_pre_topc(B_819, A_818) | ~l1_pre_topc(A_818) | ~v2_pre_topc(A_818) | v2_struct_0(A_818))), inference(cnfTransformation, [status(thm)], [f_130])).
% 10.04/3.64  tff(c_12, plain, (![B_6, C_7, E_9, D_8, A_5, F_10]: (F_10=E_9 | ~r1_funct_2(A_5, B_6, C_7, D_8, E_9, F_10) | ~m1_subset_1(F_10, k1_zfmisc_1(k2_zfmisc_1(C_7, D_8))) | ~v1_funct_2(F_10, C_7, D_8) | ~v1_funct_1(F_10) | ~m1_subset_1(E_9, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))) | ~v1_funct_2(E_9, A_5, B_6) | ~v1_funct_1(E_9) | v1_xboole_0(D_8) | v1_xboole_0(B_6))), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.04/3.64  tff(c_4059, plain, (![A_871, B_872]: (k7_tmap_1(A_871, u1_struct_0(B_872))=k9_tmap_1(A_871, B_872) | ~m1_subset_1(k7_tmap_1(A_871, u1_struct_0(B_872)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_871), u1_struct_0(k6_tmap_1(A_871, u1_struct_0(B_872)))))) | ~v1_funct_2(k7_tmap_1(A_871, u1_struct_0(B_872)), u1_struct_0(A_871), u1_struct_0(k6_tmap_1(A_871, u1_struct_0(B_872)))) | ~v1_funct_1(k7_tmap_1(A_871, u1_struct_0(B_872))) | v1_xboole_0(u1_struct_0(k6_tmap_1(A_871, u1_struct_0(B_872)))) | v1_xboole_0(u1_struct_0(k8_tmap_1(A_871, B_872))) | ~m1_subset_1(u1_struct_0(B_872), k1_zfmisc_1(u1_struct_0(A_871))) | ~m1_subset_1(k9_tmap_1(A_871, B_872), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_871), u1_struct_0(k8_tmap_1(A_871, B_872))))) | ~v1_funct_2(k9_tmap_1(A_871, B_872), u1_struct_0(A_871), u1_struct_0(k8_tmap_1(A_871, B_872))) | ~v1_funct_1(k9_tmap_1(A_871, B_872)) | ~m1_pre_topc(B_872, A_871) | ~l1_pre_topc(A_871) | ~v2_pre_topc(A_871) | v2_struct_0(A_871))), inference(resolution, [status(thm)], [c_3806, c_12])).
% 10.04/3.64  tff(c_4384, plain, (![A_944, B_945]: (k7_tmap_1(A_944, u1_struct_0(B_945))=k9_tmap_1(A_944, B_945) | ~v1_funct_2(k7_tmap_1(A_944, u1_struct_0(B_945)), u1_struct_0(A_944), u1_struct_0(k6_tmap_1(A_944, u1_struct_0(B_945)))) | ~v1_funct_1(k7_tmap_1(A_944, u1_struct_0(B_945))) | v1_xboole_0(u1_struct_0(k6_tmap_1(A_944, u1_struct_0(B_945)))) | v1_xboole_0(u1_struct_0(k8_tmap_1(A_944, B_945))) | ~m1_subset_1(k9_tmap_1(A_944, B_945), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_944), u1_struct_0(k8_tmap_1(A_944, B_945))))) | ~v1_funct_2(k9_tmap_1(A_944, B_945), u1_struct_0(A_944), u1_struct_0(k8_tmap_1(A_944, B_945))) | ~v1_funct_1(k9_tmap_1(A_944, B_945)) | ~m1_pre_topc(B_945, A_944) | ~m1_subset_1(u1_struct_0(B_945), k1_zfmisc_1(u1_struct_0(A_944))) | ~l1_pre_topc(A_944) | ~v2_pre_topc(A_944) | v2_struct_0(A_944))), inference(resolution, [status(thm)], [c_32, c_4059])).
% 10.04/3.64  tff(c_4428, plain, (![A_954, B_955]: (k7_tmap_1(A_954, u1_struct_0(B_955))=k9_tmap_1(A_954, B_955) | ~v1_funct_1(k7_tmap_1(A_954, u1_struct_0(B_955))) | v1_xboole_0(u1_struct_0(k6_tmap_1(A_954, u1_struct_0(B_955)))) | v1_xboole_0(u1_struct_0(k8_tmap_1(A_954, B_955))) | ~m1_subset_1(k9_tmap_1(A_954, B_955), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_954), u1_struct_0(k8_tmap_1(A_954, B_955))))) | ~v1_funct_2(k9_tmap_1(A_954, B_955), u1_struct_0(A_954), u1_struct_0(k8_tmap_1(A_954, B_955))) | ~v1_funct_1(k9_tmap_1(A_954, B_955)) | ~m1_pre_topc(B_955, A_954) | ~m1_subset_1(u1_struct_0(B_955), k1_zfmisc_1(u1_struct_0(A_954))) | ~l1_pre_topc(A_954) | ~v2_pre_topc(A_954) | v2_struct_0(A_954))), inference(resolution, [status(thm)], [c_34, c_4384])).
% 10.04/3.64  tff(c_4433, plain, (![A_956, B_957]: (k7_tmap_1(A_956, u1_struct_0(B_957))=k9_tmap_1(A_956, B_957) | ~v1_funct_1(k7_tmap_1(A_956, u1_struct_0(B_957))) | v1_xboole_0(u1_struct_0(k6_tmap_1(A_956, u1_struct_0(B_957)))) | v1_xboole_0(u1_struct_0(k8_tmap_1(A_956, B_957))) | ~v1_funct_2(k9_tmap_1(A_956, B_957), u1_struct_0(A_956), u1_struct_0(k8_tmap_1(A_956, B_957))) | ~v1_funct_1(k9_tmap_1(A_956, B_957)) | ~m1_subset_1(u1_struct_0(B_957), k1_zfmisc_1(u1_struct_0(A_956))) | ~m1_pre_topc(B_957, A_956) | ~l1_pre_topc(A_956) | ~v2_pre_topc(A_956) | v2_struct_0(A_956))), inference(resolution, [status(thm)], [c_44, c_4428])).
% 10.04/3.64  tff(c_4438, plain, (![A_958, B_959]: (k7_tmap_1(A_958, u1_struct_0(B_959))=k9_tmap_1(A_958, B_959) | ~v1_funct_1(k7_tmap_1(A_958, u1_struct_0(B_959))) | v1_xboole_0(u1_struct_0(k6_tmap_1(A_958, u1_struct_0(B_959)))) | v1_xboole_0(u1_struct_0(k8_tmap_1(A_958, B_959))) | ~v1_funct_1(k9_tmap_1(A_958, B_959)) | ~m1_subset_1(u1_struct_0(B_959), k1_zfmisc_1(u1_struct_0(A_958))) | ~m1_pre_topc(B_959, A_958) | ~l1_pre_topc(A_958) | ~v2_pre_topc(A_958) | v2_struct_0(A_958))), inference(resolution, [status(thm)], [c_46, c_4433])).
% 10.04/3.64  tff(c_4443, plain, (![A_960, B_961]: (k7_tmap_1(A_960, u1_struct_0(B_961))=k9_tmap_1(A_960, B_961) | ~v1_funct_1(k7_tmap_1(A_960, u1_struct_0(B_961))) | v1_xboole_0(u1_struct_0(k6_tmap_1(A_960, u1_struct_0(B_961)))) | v1_xboole_0(u1_struct_0(k8_tmap_1(A_960, B_961))) | ~v1_funct_1(k9_tmap_1(A_960, B_961)) | ~v2_pre_topc(A_960) | v2_struct_0(A_960) | ~m1_pre_topc(B_961, A_960) | ~l1_pre_topc(A_960))), inference(resolution, [status(thm)], [c_64, c_4438])).
% 10.04/3.64  tff(c_4449, plain, (![A_60, B_61]: (k7_tmap_1(A_60, u1_struct_0(B_61))=k9_tmap_1(A_60, B_61) | ~v1_funct_1(k7_tmap_1(A_60, u1_struct_0(B_61))) | v1_xboole_0(u1_struct_0(k8_tmap_1(A_60, B_61))) | v1_xboole_0(u1_struct_0(k8_tmap_1(A_60, B_61))) | ~v1_funct_1(k9_tmap_1(A_60, B_61)) | ~v2_pre_topc(A_60) | v2_struct_0(A_60) | ~m1_pre_topc(B_61, A_60) | ~l1_pre_topc(A_60) | ~m1_pre_topc(B_61, A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(superposition, [status(thm), theory('equality')], [c_3643, c_4443])).
% 10.04/3.64  tff(c_4478, plain, (![A_970, B_971]: (k7_tmap_1(A_970, u1_struct_0(B_971))=k9_tmap_1(A_970, B_971) | ~v1_funct_1(k7_tmap_1(A_970, u1_struct_0(B_971))) | ~v1_funct_1(k9_tmap_1(A_970, B_971)) | ~m1_pre_topc(B_971, A_970) | ~l1_pre_topc(A_970) | ~v2_pre_topc(A_970) | v2_struct_0(A_970) | v1_xboole_0(u1_struct_0(k8_tmap_1(A_970, B_971))))), inference(factorization, [status(thm), theory('equality')], [c_4449])).
% 10.04/3.64  tff(c_4, plain, (![A_2]: (~v1_xboole_0(u1_struct_0(A_2)) | ~l1_struct_0(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.04/3.64  tff(c_4483, plain, (![A_972, B_973]: (~l1_struct_0(k8_tmap_1(A_972, B_973)) | v2_struct_0(k8_tmap_1(A_972, B_973)) | k7_tmap_1(A_972, u1_struct_0(B_973))=k9_tmap_1(A_972, B_973) | ~v1_funct_1(k7_tmap_1(A_972, u1_struct_0(B_973))) | ~v1_funct_1(k9_tmap_1(A_972, B_973)) | ~m1_pre_topc(B_973, A_972) | ~l1_pre_topc(A_972) | ~v2_pre_topc(A_972) | v2_struct_0(A_972))), inference(resolution, [status(thm)], [c_4478, c_4])).
% 10.04/3.64  tff(c_4491, plain, (![A_974, B_975]: (~l1_struct_0(k8_tmap_1(A_974, B_975)) | v2_struct_0(k8_tmap_1(A_974, B_975)) | k7_tmap_1(A_974, u1_struct_0(B_975))=k9_tmap_1(A_974, B_975) | ~v1_funct_1(k9_tmap_1(A_974, B_975)) | ~v2_pre_topc(A_974) | v2_struct_0(A_974) | ~m1_pre_topc(B_975, A_974) | ~l1_pre_topc(A_974))), inference(resolution, [status(thm)], [c_3499, c_4483])).
% 10.04/3.64  tff(c_54, plain, (![A_64, B_65]: (~v2_struct_0(k8_tmap_1(A_64, B_65)) | ~m1_pre_topc(B_65, A_64) | ~l1_pre_topc(A_64) | ~v2_pre_topc(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_191])).
% 10.04/3.64  tff(c_4496, plain, (![A_976, B_977]: (~l1_struct_0(k8_tmap_1(A_976, B_977)) | k7_tmap_1(A_976, u1_struct_0(B_977))=k9_tmap_1(A_976, B_977) | ~v1_funct_1(k9_tmap_1(A_976, B_977)) | ~v2_pre_topc(A_976) | v2_struct_0(A_976) | ~m1_pre_topc(B_977, A_976) | ~l1_pre_topc(A_976))), inference(resolution, [status(thm)], [c_4491, c_54])).
% 10.04/3.64  tff(c_4501, plain, (![A_978, B_979]: (~l1_struct_0(k8_tmap_1(A_978, B_979)) | k7_tmap_1(A_978, u1_struct_0(B_979))=k9_tmap_1(A_978, B_979) | ~m1_pre_topc(B_979, A_978) | ~l1_pre_topc(A_978) | ~v2_pre_topc(A_978) | v2_struct_0(A_978))), inference(resolution, [status(thm)], [c_48, c_4496])).
% 10.04/3.64  tff(c_4506, plain, (![A_980, B_981]: (k7_tmap_1(A_980, u1_struct_0(B_981))=k9_tmap_1(A_980, B_981) | ~m1_pre_topc(B_981, A_980) | ~l1_pre_topc(A_980) | ~v2_pre_topc(A_980) | v2_struct_0(A_980) | ~l1_pre_topc(k8_tmap_1(A_980, B_981)))), inference(resolution, [status(thm)], [c_2, c_4501])).
% 10.04/3.64  tff(c_4511, plain, (![A_982, B_983]: (k7_tmap_1(A_982, u1_struct_0(B_983))=k9_tmap_1(A_982, B_983) | ~m1_pre_topc(B_983, A_982) | ~l1_pre_topc(A_982) | ~v2_pre_topc(A_982) | v2_struct_0(A_982))), inference(resolution, [status(thm)], [c_38, c_4506])).
% 10.04/3.64  tff(c_3501, plain, (![A_710, B_711]: (k7_tmap_1(A_710, B_711)=k6_partfun1(u1_struct_0(A_710)) | ~m1_subset_1(B_711, k1_zfmisc_1(u1_struct_0(A_710))) | ~l1_pre_topc(A_710) | ~v2_pre_topc(A_710) | v2_struct_0(A_710))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.04/3.64  tff(c_3508, plain, (![A_73, B_75]: (k7_tmap_1(A_73, u1_struct_0(B_75))=k6_partfun1(u1_struct_0(A_73)) | ~v2_pre_topc(A_73) | v2_struct_0(A_73) | ~m1_pre_topc(B_75, A_73) | ~l1_pre_topc(A_73))), inference(resolution, [status(thm)], [c_64, c_3501])).
% 10.04/3.64  tff(c_4614, plain, (![A_988, B_989]: (k9_tmap_1(A_988, B_989)=k6_partfun1(u1_struct_0(A_988)) | ~v2_pre_topc(A_988) | v2_struct_0(A_988) | ~m1_pre_topc(B_989, A_988) | ~l1_pre_topc(A_988) | ~m1_pre_topc(B_989, A_988) | ~l1_pre_topc(A_988) | ~v2_pre_topc(A_988) | v2_struct_0(A_988))), inference(superposition, [status(thm), theory('equality')], [c_4511, c_3508])).
% 10.04/3.64  tff(c_4616, plain, (k6_partfun1(u1_struct_0('#skF_4'))=k9_tmap_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_68, c_4614])).
% 10.04/3.64  tff(c_4619, plain, (k6_partfun1(u1_struct_0('#skF_4'))=k9_tmap_1('#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_68, c_4616])).
% 10.04/3.64  tff(c_4620, plain, (k6_partfun1(u1_struct_0('#skF_4'))=k9_tmap_1('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_76, c_4619])).
% 10.04/3.64  tff(c_3635, plain, (![A_761, C_762]: (v1_funct_2(k2_tmap_1(A_761, k6_tmap_1(A_761, u1_struct_0(C_762)), k7_tmap_1(A_761, u1_struct_0(C_762)), C_762), u1_struct_0(C_762), u1_struct_0(k6_tmap_1(A_761, u1_struct_0(C_762)))) | ~m1_pre_topc(C_762, A_761) | v2_struct_0(C_762) | ~m1_subset_1(u1_struct_0(C_762), k1_zfmisc_1(u1_struct_0(A_761))) | ~l1_pre_topc(A_761) | ~v2_pre_topc(A_761) | v2_struct_0(A_761))), inference(cnfTransformation, [status(thm)], [f_217])).
% 10.04/3.64  tff(c_3839, plain, (![A_826, B_827]: (v1_funct_2(k2_tmap_1(A_826, k6_tmap_1(A_826, u1_struct_0(B_827)), k6_partfun1(u1_struct_0(A_826)), B_827), u1_struct_0(B_827), u1_struct_0(k6_tmap_1(A_826, u1_struct_0(B_827)))) | ~m1_pre_topc(B_827, A_826) | v2_struct_0(B_827) | ~m1_subset_1(u1_struct_0(B_827), k1_zfmisc_1(u1_struct_0(A_826))) | ~l1_pre_topc(A_826) | ~v2_pre_topc(A_826) | v2_struct_0(A_826) | ~v2_pre_topc(A_826) | v2_struct_0(A_826) | ~m1_pre_topc(B_827, A_826) | ~l1_pre_topc(A_826))), inference(superposition, [status(thm), theory('equality')], [c_3508, c_3635])).
% 10.04/3.64  tff(c_4253, plain, (![A_904, B_905]: (v1_funct_2(k2_tmap_1(A_904, k8_tmap_1(A_904, B_905), k6_partfun1(u1_struct_0(A_904)), B_905), u1_struct_0(B_905), u1_struct_0(k6_tmap_1(A_904, u1_struct_0(B_905)))) | ~m1_pre_topc(B_905, A_904) | v2_struct_0(B_905) | ~m1_subset_1(u1_struct_0(B_905), k1_zfmisc_1(u1_struct_0(A_904))) | ~l1_pre_topc(A_904) | ~v2_pre_topc(A_904) | v2_struct_0(A_904) | ~v2_pre_topc(A_904) | v2_struct_0(A_904) | ~m1_pre_topc(B_905, A_904) | ~l1_pre_topc(A_904) | ~m1_pre_topc(B_905, A_904) | ~l1_pre_topc(A_904) | ~v2_pre_topc(A_904) | v2_struct_0(A_904))), inference(superposition, [status(thm), theory('equality')], [c_3643, c_3839])).
% 10.04/3.64  tff(c_4256, plain, (![A_60, B_61]: (v1_funct_2(k2_tmap_1(A_60, k8_tmap_1(A_60, B_61), k6_partfun1(u1_struct_0(A_60)), B_61), u1_struct_0(B_61), u1_struct_0(k8_tmap_1(A_60, B_61))) | ~m1_pre_topc(B_61, A_60) | v2_struct_0(B_61) | ~m1_subset_1(u1_struct_0(B_61), k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60) | ~m1_pre_topc(B_61, A_60) | ~l1_pre_topc(A_60) | ~m1_pre_topc(B_61, A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60) | ~m1_pre_topc(B_61, A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(superposition, [status(thm), theory('equality')], [c_3643, c_4253])).
% 10.04/3.64  tff(c_4633, plain, (![B_61]: (v1_funct_2(k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', B_61), k9_tmap_1('#skF_4', '#skF_5'), B_61), u1_struct_0(B_61), u1_struct_0(k8_tmap_1('#skF_4', B_61))) | ~m1_pre_topc(B_61, '#skF_4') | v2_struct_0(B_61) | ~m1_subset_1(u1_struct_0(B_61), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_61, '#skF_4') | ~l1_pre_topc('#skF_4') | ~m1_pre_topc(B_61, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_61, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4620, c_4256])).
% 10.04/3.64  tff(c_4742, plain, (![B_61]: (v1_funct_2(k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', B_61), k9_tmap_1('#skF_4', '#skF_5'), B_61), u1_struct_0(B_61), u1_struct_0(k8_tmap_1('#skF_4', B_61))) | v2_struct_0(B_61) | ~m1_subset_1(u1_struct_0(B_61), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc(B_61, '#skF_4') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_74, c_72, c_72, c_74, c_74, c_72, c_4633])).
% 10.04/3.64  tff(c_5332, plain, (![B_1015]: (v1_funct_2(k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', B_1015), k9_tmap_1('#skF_4', '#skF_5'), B_1015), u1_struct_0(B_1015), u1_struct_0(k8_tmap_1('#skF_4', B_1015))) | v2_struct_0(B_1015) | ~m1_subset_1(u1_struct_0(B_1015), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc(B_1015, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_76, c_4742])).
% 10.04/3.64  tff(c_1584, plain, (![A_392, B_393]: (v1_funct_1(k7_tmap_1(A_392, B_393)) | ~m1_subset_1(B_393, k1_zfmisc_1(u1_struct_0(A_392))) | ~l1_pre_topc(A_392) | ~v2_pre_topc(A_392) | v2_struct_0(A_392))), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.04/3.64  tff(c_1591, plain, (![A_73, B_75]: (v1_funct_1(k7_tmap_1(A_73, u1_struct_0(B_75))) | ~v2_pre_topc(A_73) | v2_struct_0(A_73) | ~m1_pre_topc(B_75, A_73) | ~l1_pre_topc(A_73))), inference(resolution, [status(thm)], [c_64, c_1584])).
% 10.04/3.64  tff(c_1702, plain, (![A_437, B_438]: (k6_tmap_1(A_437, u1_struct_0(B_438))=k8_tmap_1(A_437, B_438) | ~m1_subset_1(u1_struct_0(B_438), k1_zfmisc_1(u1_struct_0(A_437))) | ~l1_pre_topc(k8_tmap_1(A_437, B_438)) | ~v2_pre_topc(k8_tmap_1(A_437, B_438)) | ~v1_pre_topc(k8_tmap_1(A_437, B_438)) | ~m1_pre_topc(B_438, A_437) | ~l1_pre_topc(A_437) | ~v2_pre_topc(A_437) | v2_struct_0(A_437))), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.04/3.64  tff(c_1707, plain, (![A_439, B_440]: (k6_tmap_1(A_439, u1_struct_0(B_440))=k8_tmap_1(A_439, B_440) | ~l1_pre_topc(k8_tmap_1(A_439, B_440)) | ~v2_pre_topc(k8_tmap_1(A_439, B_440)) | ~v1_pre_topc(k8_tmap_1(A_439, B_440)) | ~v2_pre_topc(A_439) | v2_struct_0(A_439) | ~m1_pre_topc(B_440, A_439) | ~l1_pre_topc(A_439))), inference(resolution, [status(thm)], [c_64, c_1702])).
% 10.04/3.64  tff(c_1716, plain, (![A_443, B_444]: (k6_tmap_1(A_443, u1_struct_0(B_444))=k8_tmap_1(A_443, B_444) | ~l1_pre_topc(k8_tmap_1(A_443, B_444)) | ~v1_pre_topc(k8_tmap_1(A_443, B_444)) | ~m1_pre_topc(B_444, A_443) | ~l1_pre_topc(A_443) | ~v2_pre_topc(A_443) | v2_struct_0(A_443))), inference(resolution, [status(thm)], [c_50, c_1707])).
% 10.04/3.64  tff(c_1721, plain, (![A_445, B_446]: (k6_tmap_1(A_445, u1_struct_0(B_446))=k8_tmap_1(A_445, B_446) | ~l1_pre_topc(k8_tmap_1(A_445, B_446)) | ~m1_pre_topc(B_446, A_445) | ~l1_pre_topc(A_445) | ~v2_pre_topc(A_445) | v2_struct_0(A_445))), inference(resolution, [status(thm)], [c_52, c_1716])).
% 10.04/3.64  tff(c_1725, plain, (![A_60, B_61]: (k6_tmap_1(A_60, u1_struct_0(B_61))=k8_tmap_1(A_60, B_61) | ~m1_pre_topc(B_61, A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(resolution, [status(thm)], [c_38, c_1721])).
% 10.04/3.64  tff(c_1892, plain, (![A_502, B_503]: (r1_funct_2(u1_struct_0(A_502), u1_struct_0(k8_tmap_1(A_502, B_503)), u1_struct_0(A_502), u1_struct_0(k6_tmap_1(A_502, u1_struct_0(B_503))), k9_tmap_1(A_502, B_503), k7_tmap_1(A_502, u1_struct_0(B_503))) | ~m1_subset_1(u1_struct_0(B_503), k1_zfmisc_1(u1_struct_0(A_502))) | ~m1_subset_1(k9_tmap_1(A_502, B_503), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_502), u1_struct_0(k8_tmap_1(A_502, B_503))))) | ~v1_funct_2(k9_tmap_1(A_502, B_503), u1_struct_0(A_502), u1_struct_0(k8_tmap_1(A_502, B_503))) | ~v1_funct_1(k9_tmap_1(A_502, B_503)) | ~m1_pre_topc(B_503, A_502) | ~l1_pre_topc(A_502) | ~v2_pre_topc(A_502) | v2_struct_0(A_502))), inference(cnfTransformation, [status(thm)], [f_130])).
% 10.04/3.64  tff(c_2182, plain, (![A_564, B_565]: (k7_tmap_1(A_564, u1_struct_0(B_565))=k9_tmap_1(A_564, B_565) | ~m1_subset_1(k7_tmap_1(A_564, u1_struct_0(B_565)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_564), u1_struct_0(k6_tmap_1(A_564, u1_struct_0(B_565)))))) | ~v1_funct_2(k7_tmap_1(A_564, u1_struct_0(B_565)), u1_struct_0(A_564), u1_struct_0(k6_tmap_1(A_564, u1_struct_0(B_565)))) | ~v1_funct_1(k7_tmap_1(A_564, u1_struct_0(B_565))) | v1_xboole_0(u1_struct_0(k6_tmap_1(A_564, u1_struct_0(B_565)))) | v1_xboole_0(u1_struct_0(k8_tmap_1(A_564, B_565))) | ~m1_subset_1(u1_struct_0(B_565), k1_zfmisc_1(u1_struct_0(A_564))) | ~m1_subset_1(k9_tmap_1(A_564, B_565), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_564), u1_struct_0(k8_tmap_1(A_564, B_565))))) | ~v1_funct_2(k9_tmap_1(A_564, B_565), u1_struct_0(A_564), u1_struct_0(k8_tmap_1(A_564, B_565))) | ~v1_funct_1(k9_tmap_1(A_564, B_565)) | ~m1_pre_topc(B_565, A_564) | ~l1_pre_topc(A_564) | ~v2_pre_topc(A_564) | v2_struct_0(A_564))), inference(resolution, [status(thm)], [c_1892, c_12])).
% 10.04/3.64  tff(c_2445, plain, (![A_621, B_622]: (k7_tmap_1(A_621, u1_struct_0(B_622))=k9_tmap_1(A_621, B_622) | ~v1_funct_2(k7_tmap_1(A_621, u1_struct_0(B_622)), u1_struct_0(A_621), u1_struct_0(k6_tmap_1(A_621, u1_struct_0(B_622)))) | ~v1_funct_1(k7_tmap_1(A_621, u1_struct_0(B_622))) | v1_xboole_0(u1_struct_0(k6_tmap_1(A_621, u1_struct_0(B_622)))) | v1_xboole_0(u1_struct_0(k8_tmap_1(A_621, B_622))) | ~m1_subset_1(k9_tmap_1(A_621, B_622), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_621), u1_struct_0(k8_tmap_1(A_621, B_622))))) | ~v1_funct_2(k9_tmap_1(A_621, B_622), u1_struct_0(A_621), u1_struct_0(k8_tmap_1(A_621, B_622))) | ~v1_funct_1(k9_tmap_1(A_621, B_622)) | ~m1_pre_topc(B_622, A_621) | ~m1_subset_1(u1_struct_0(B_622), k1_zfmisc_1(u1_struct_0(A_621))) | ~l1_pre_topc(A_621) | ~v2_pre_topc(A_621) | v2_struct_0(A_621))), inference(resolution, [status(thm)], [c_32, c_2182])).
% 10.04/3.64  tff(c_2514, plain, (![A_638, B_639]: (k7_tmap_1(A_638, u1_struct_0(B_639))=k9_tmap_1(A_638, B_639) | ~v1_funct_1(k7_tmap_1(A_638, u1_struct_0(B_639))) | v1_xboole_0(u1_struct_0(k6_tmap_1(A_638, u1_struct_0(B_639)))) | v1_xboole_0(u1_struct_0(k8_tmap_1(A_638, B_639))) | ~m1_subset_1(k9_tmap_1(A_638, B_639), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_638), u1_struct_0(k8_tmap_1(A_638, B_639))))) | ~v1_funct_2(k9_tmap_1(A_638, B_639), u1_struct_0(A_638), u1_struct_0(k8_tmap_1(A_638, B_639))) | ~v1_funct_1(k9_tmap_1(A_638, B_639)) | ~m1_pre_topc(B_639, A_638) | ~m1_subset_1(u1_struct_0(B_639), k1_zfmisc_1(u1_struct_0(A_638))) | ~l1_pre_topc(A_638) | ~v2_pre_topc(A_638) | v2_struct_0(A_638))), inference(resolution, [status(thm)], [c_34, c_2445])).
% 10.04/3.64  tff(c_2519, plain, (![A_640, B_641]: (k7_tmap_1(A_640, u1_struct_0(B_641))=k9_tmap_1(A_640, B_641) | ~v1_funct_1(k7_tmap_1(A_640, u1_struct_0(B_641))) | v1_xboole_0(u1_struct_0(k6_tmap_1(A_640, u1_struct_0(B_641)))) | v1_xboole_0(u1_struct_0(k8_tmap_1(A_640, B_641))) | ~v1_funct_2(k9_tmap_1(A_640, B_641), u1_struct_0(A_640), u1_struct_0(k8_tmap_1(A_640, B_641))) | ~v1_funct_1(k9_tmap_1(A_640, B_641)) | ~m1_subset_1(u1_struct_0(B_641), k1_zfmisc_1(u1_struct_0(A_640))) | ~m1_pre_topc(B_641, A_640) | ~l1_pre_topc(A_640) | ~v2_pre_topc(A_640) | v2_struct_0(A_640))), inference(resolution, [status(thm)], [c_44, c_2514])).
% 10.04/3.64  tff(c_2524, plain, (![A_642, B_643]: (k7_tmap_1(A_642, u1_struct_0(B_643))=k9_tmap_1(A_642, B_643) | ~v1_funct_1(k7_tmap_1(A_642, u1_struct_0(B_643))) | v1_xboole_0(u1_struct_0(k6_tmap_1(A_642, u1_struct_0(B_643)))) | v1_xboole_0(u1_struct_0(k8_tmap_1(A_642, B_643))) | ~v1_funct_1(k9_tmap_1(A_642, B_643)) | ~m1_subset_1(u1_struct_0(B_643), k1_zfmisc_1(u1_struct_0(A_642))) | ~m1_pre_topc(B_643, A_642) | ~l1_pre_topc(A_642) | ~v2_pre_topc(A_642) | v2_struct_0(A_642))), inference(resolution, [status(thm)], [c_46, c_2519])).
% 10.04/3.64  tff(c_2529, plain, (![A_644, B_645]: (k7_tmap_1(A_644, u1_struct_0(B_645))=k9_tmap_1(A_644, B_645) | ~v1_funct_1(k7_tmap_1(A_644, u1_struct_0(B_645))) | v1_xboole_0(u1_struct_0(k6_tmap_1(A_644, u1_struct_0(B_645)))) | v1_xboole_0(u1_struct_0(k8_tmap_1(A_644, B_645))) | ~v1_funct_1(k9_tmap_1(A_644, B_645)) | ~v2_pre_topc(A_644) | v2_struct_0(A_644) | ~m1_pre_topc(B_645, A_644) | ~l1_pre_topc(A_644))), inference(resolution, [status(thm)], [c_64, c_2524])).
% 10.04/3.64  tff(c_2535, plain, (![A_60, B_61]: (k7_tmap_1(A_60, u1_struct_0(B_61))=k9_tmap_1(A_60, B_61) | ~v1_funct_1(k7_tmap_1(A_60, u1_struct_0(B_61))) | v1_xboole_0(u1_struct_0(k8_tmap_1(A_60, B_61))) | v1_xboole_0(u1_struct_0(k8_tmap_1(A_60, B_61))) | ~v1_funct_1(k9_tmap_1(A_60, B_61)) | ~v2_pre_topc(A_60) | v2_struct_0(A_60) | ~m1_pre_topc(B_61, A_60) | ~l1_pre_topc(A_60) | ~m1_pre_topc(B_61, A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(superposition, [status(thm), theory('equality')], [c_1725, c_2529])).
% 10.04/3.64  tff(c_2554, plain, (![A_650, B_651]: (k7_tmap_1(A_650, u1_struct_0(B_651))=k9_tmap_1(A_650, B_651) | ~v1_funct_1(k7_tmap_1(A_650, u1_struct_0(B_651))) | ~v1_funct_1(k9_tmap_1(A_650, B_651)) | ~m1_pre_topc(B_651, A_650) | ~l1_pre_topc(A_650) | ~v2_pre_topc(A_650) | v2_struct_0(A_650) | v1_xboole_0(u1_struct_0(k8_tmap_1(A_650, B_651))))), inference(factorization, [status(thm), theory('equality')], [c_2535])).
% 10.04/3.64  tff(c_2559, plain, (![A_652, B_653]: (~l1_struct_0(k8_tmap_1(A_652, B_653)) | v2_struct_0(k8_tmap_1(A_652, B_653)) | k7_tmap_1(A_652, u1_struct_0(B_653))=k9_tmap_1(A_652, B_653) | ~v1_funct_1(k7_tmap_1(A_652, u1_struct_0(B_653))) | ~v1_funct_1(k9_tmap_1(A_652, B_653)) | ~m1_pre_topc(B_653, A_652) | ~l1_pre_topc(A_652) | ~v2_pre_topc(A_652) | v2_struct_0(A_652))), inference(resolution, [status(thm)], [c_2554, c_4])).
% 10.04/3.64  tff(c_2577, plain, (![A_658, B_659]: (~l1_struct_0(k8_tmap_1(A_658, B_659)) | v2_struct_0(k8_tmap_1(A_658, B_659)) | k7_tmap_1(A_658, u1_struct_0(B_659))=k9_tmap_1(A_658, B_659) | ~v1_funct_1(k9_tmap_1(A_658, B_659)) | ~v2_pre_topc(A_658) | v2_struct_0(A_658) | ~m1_pre_topc(B_659, A_658) | ~l1_pre_topc(A_658))), inference(resolution, [status(thm)], [c_1591, c_2559])).
% 10.04/3.64  tff(c_2582, plain, (![A_660, B_661]: (~l1_struct_0(k8_tmap_1(A_660, B_661)) | k7_tmap_1(A_660, u1_struct_0(B_661))=k9_tmap_1(A_660, B_661) | ~v1_funct_1(k9_tmap_1(A_660, B_661)) | ~v2_pre_topc(A_660) | v2_struct_0(A_660) | ~m1_pre_topc(B_661, A_660) | ~l1_pre_topc(A_660))), inference(resolution, [status(thm)], [c_2577, c_54])).
% 10.04/3.64  tff(c_2587, plain, (![A_662, B_663]: (~l1_struct_0(k8_tmap_1(A_662, B_663)) | k7_tmap_1(A_662, u1_struct_0(B_663))=k9_tmap_1(A_662, B_663) | ~m1_pre_topc(B_663, A_662) | ~l1_pre_topc(A_662) | ~v2_pre_topc(A_662) | v2_struct_0(A_662))), inference(resolution, [status(thm)], [c_48, c_2582])).
% 10.04/3.64  tff(c_2592, plain, (![A_664, B_665]: (k7_tmap_1(A_664, u1_struct_0(B_665))=k9_tmap_1(A_664, B_665) | ~m1_pre_topc(B_665, A_664) | ~l1_pre_topc(A_664) | ~v2_pre_topc(A_664) | v2_struct_0(A_664) | ~l1_pre_topc(k8_tmap_1(A_664, B_665)))), inference(resolution, [status(thm)], [c_2, c_2587])).
% 10.04/3.64  tff(c_2597, plain, (![A_666, B_667]: (k7_tmap_1(A_666, u1_struct_0(B_667))=k9_tmap_1(A_666, B_667) | ~m1_pre_topc(B_667, A_666) | ~l1_pre_topc(A_666) | ~v2_pre_topc(A_666) | v2_struct_0(A_666))), inference(resolution, [status(thm)], [c_38, c_2592])).
% 10.04/3.64  tff(c_1595, plain, (![A_397, B_398]: (k7_tmap_1(A_397, B_398)=k6_partfun1(u1_struct_0(A_397)) | ~m1_subset_1(B_398, k1_zfmisc_1(u1_struct_0(A_397))) | ~l1_pre_topc(A_397) | ~v2_pre_topc(A_397) | v2_struct_0(A_397))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.04/3.64  tff(c_1602, plain, (![A_73, B_75]: (k7_tmap_1(A_73, u1_struct_0(B_75))=k6_partfun1(u1_struct_0(A_73)) | ~v2_pre_topc(A_73) | v2_struct_0(A_73) | ~m1_pre_topc(B_75, A_73) | ~l1_pre_topc(A_73))), inference(resolution, [status(thm)], [c_64, c_1595])).
% 10.04/3.64  tff(c_2687, plain, (![A_668, B_669]: (k9_tmap_1(A_668, B_669)=k6_partfun1(u1_struct_0(A_668)) | ~v2_pre_topc(A_668) | v2_struct_0(A_668) | ~m1_pre_topc(B_669, A_668) | ~l1_pre_topc(A_668) | ~m1_pre_topc(B_669, A_668) | ~l1_pre_topc(A_668) | ~v2_pre_topc(A_668) | v2_struct_0(A_668))), inference(superposition, [status(thm), theory('equality')], [c_2597, c_1602])).
% 10.04/3.64  tff(c_2689, plain, (k6_partfun1(u1_struct_0('#skF_4'))=k9_tmap_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_68, c_2687])).
% 10.04/3.64  tff(c_2692, plain, (k6_partfun1(u1_struct_0('#skF_4'))=k9_tmap_1('#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_68, c_2689])).
% 10.04/3.64  tff(c_2693, plain, (k6_partfun1(u1_struct_0('#skF_4'))=k9_tmap_1('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_76, c_2692])).
% 10.04/3.64  tff(c_1786, plain, (![A_465, C_466]: (m1_subset_1(k2_tmap_1(A_465, k6_tmap_1(A_465, u1_struct_0(C_466)), k7_tmap_1(A_465, u1_struct_0(C_466)), C_466), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_466), u1_struct_0(k6_tmap_1(A_465, u1_struct_0(C_466)))))) | ~m1_pre_topc(C_466, A_465) | v2_struct_0(C_466) | ~m1_subset_1(u1_struct_0(C_466), k1_zfmisc_1(u1_struct_0(A_465))) | ~l1_pre_topc(A_465) | ~v2_pre_topc(A_465) | v2_struct_0(A_465))), inference(cnfTransformation, [status(thm)], [f_217])).
% 10.04/3.64  tff(c_2005, plain, (![A_535, B_536]: (m1_subset_1(k2_tmap_1(A_535, k6_tmap_1(A_535, u1_struct_0(B_536)), k6_partfun1(u1_struct_0(A_535)), B_536), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_536), u1_struct_0(k6_tmap_1(A_535, u1_struct_0(B_536)))))) | ~m1_pre_topc(B_536, A_535) | v2_struct_0(B_536) | ~m1_subset_1(u1_struct_0(B_536), k1_zfmisc_1(u1_struct_0(A_535))) | ~l1_pre_topc(A_535) | ~v2_pre_topc(A_535) | v2_struct_0(A_535) | ~v2_pre_topc(A_535) | v2_struct_0(A_535) | ~m1_pre_topc(B_536, A_535) | ~l1_pre_topc(A_535))), inference(superposition, [status(thm), theory('equality')], [c_1602, c_1786])).
% 10.04/3.64  tff(c_2368, plain, (![A_598, B_599]: (m1_subset_1(k2_tmap_1(A_598, k8_tmap_1(A_598, B_599), k6_partfun1(u1_struct_0(A_598)), B_599), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_599), u1_struct_0(k6_tmap_1(A_598, u1_struct_0(B_599)))))) | ~m1_pre_topc(B_599, A_598) | v2_struct_0(B_599) | ~m1_subset_1(u1_struct_0(B_599), k1_zfmisc_1(u1_struct_0(A_598))) | ~l1_pre_topc(A_598) | ~v2_pre_topc(A_598) | v2_struct_0(A_598) | ~v2_pre_topc(A_598) | v2_struct_0(A_598) | ~m1_pre_topc(B_599, A_598) | ~l1_pre_topc(A_598) | ~m1_pre_topc(B_599, A_598) | ~l1_pre_topc(A_598) | ~v2_pre_topc(A_598) | v2_struct_0(A_598))), inference(superposition, [status(thm), theory('equality')], [c_1725, c_2005])).
% 10.04/3.64  tff(c_2373, plain, (![A_60, B_61]: (m1_subset_1(k2_tmap_1(A_60, k8_tmap_1(A_60, B_61), k6_partfun1(u1_struct_0(A_60)), B_61), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_61), u1_struct_0(k8_tmap_1(A_60, B_61))))) | ~m1_pre_topc(B_61, A_60) | v2_struct_0(B_61) | ~m1_subset_1(u1_struct_0(B_61), k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60) | ~m1_pre_topc(B_61, A_60) | ~l1_pre_topc(A_60) | ~m1_pre_topc(B_61, A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60) | ~m1_pre_topc(B_61, A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(superposition, [status(thm), theory('equality')], [c_1725, c_2368])).
% 10.04/3.64  tff(c_2703, plain, (![B_61]: (m1_subset_1(k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', B_61), k9_tmap_1('#skF_4', '#skF_5'), B_61), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_61), u1_struct_0(k8_tmap_1('#skF_4', B_61))))) | ~m1_pre_topc(B_61, '#skF_4') | v2_struct_0(B_61) | ~m1_subset_1(u1_struct_0(B_61), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_61, '#skF_4') | ~l1_pre_topc('#skF_4') | ~m1_pre_topc(B_61, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_61, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2693, c_2373])).
% 10.04/3.64  tff(c_2809, plain, (![B_61]: (m1_subset_1(k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', B_61), k9_tmap_1('#skF_4', '#skF_5'), B_61), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_61), u1_struct_0(k8_tmap_1('#skF_4', B_61))))) | v2_struct_0(B_61) | ~m1_subset_1(u1_struct_0(B_61), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc(B_61, '#skF_4') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_74, c_72, c_72, c_74, c_74, c_72, c_2703])).
% 10.04/3.64  tff(c_3454, plain, (![B_703]: (m1_subset_1(k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', B_703), k9_tmap_1('#skF_4', '#skF_5'), B_703), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_703), u1_struct_0(k8_tmap_1('#skF_4', B_703))))) | v2_struct_0(B_703) | ~m1_subset_1(u1_struct_0(B_703), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc(B_703, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_76, c_2809])).
% 10.04/3.64  tff(c_88, plain, (![A_93, B_94]: (v1_funct_1(k7_tmap_1(A_93, B_94)) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.04/3.64  tff(c_95, plain, (![A_73, B_75]: (v1_funct_1(k7_tmap_1(A_73, u1_struct_0(B_75))) | ~v2_pre_topc(A_73) | v2_struct_0(A_73) | ~m1_pre_topc(B_75, A_73) | ~l1_pre_topc(A_73))), inference(resolution, [status(thm)], [c_64, c_88])).
% 10.04/3.64  tff(c_210, plain, (![A_140, B_141]: (k6_tmap_1(A_140, u1_struct_0(B_141))=k8_tmap_1(A_140, B_141) | ~m1_subset_1(u1_struct_0(B_141), k1_zfmisc_1(u1_struct_0(A_140))) | ~l1_pre_topc(k8_tmap_1(A_140, B_141)) | ~v2_pre_topc(k8_tmap_1(A_140, B_141)) | ~v1_pre_topc(k8_tmap_1(A_140, B_141)) | ~m1_pre_topc(B_141, A_140) | ~l1_pre_topc(A_140) | ~v2_pre_topc(A_140) | v2_struct_0(A_140))), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.04/3.64  tff(c_215, plain, (![A_142, B_143]: (k6_tmap_1(A_142, u1_struct_0(B_143))=k8_tmap_1(A_142, B_143) | ~l1_pre_topc(k8_tmap_1(A_142, B_143)) | ~v2_pre_topc(k8_tmap_1(A_142, B_143)) | ~v1_pre_topc(k8_tmap_1(A_142, B_143)) | ~v2_pre_topc(A_142) | v2_struct_0(A_142) | ~m1_pre_topc(B_143, A_142) | ~l1_pre_topc(A_142))), inference(resolution, [status(thm)], [c_64, c_210])).
% 10.04/3.64  tff(c_220, plain, (![A_144, B_145]: (k6_tmap_1(A_144, u1_struct_0(B_145))=k8_tmap_1(A_144, B_145) | ~l1_pre_topc(k8_tmap_1(A_144, B_145)) | ~v1_pre_topc(k8_tmap_1(A_144, B_145)) | ~m1_pre_topc(B_145, A_144) | ~l1_pre_topc(A_144) | ~v2_pre_topc(A_144) | v2_struct_0(A_144))), inference(resolution, [status(thm)], [c_50, c_215])).
% 10.04/3.64  tff(c_229, plain, (![A_148, B_149]: (k6_tmap_1(A_148, u1_struct_0(B_149))=k8_tmap_1(A_148, B_149) | ~l1_pre_topc(k8_tmap_1(A_148, B_149)) | ~m1_pre_topc(B_149, A_148) | ~l1_pre_topc(A_148) | ~v2_pre_topc(A_148) | v2_struct_0(A_148))), inference(resolution, [status(thm)], [c_52, c_220])).
% 10.04/3.64  tff(c_233, plain, (![A_60, B_61]: (k6_tmap_1(A_60, u1_struct_0(B_61))=k8_tmap_1(A_60, B_61) | ~m1_pre_topc(B_61, A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(resolution, [status(thm)], [c_38, c_229])).
% 10.04/3.64  tff(c_396, plain, (![A_203, B_204]: (r1_funct_2(u1_struct_0(A_203), u1_struct_0(k8_tmap_1(A_203, B_204)), u1_struct_0(A_203), u1_struct_0(k6_tmap_1(A_203, u1_struct_0(B_204))), k9_tmap_1(A_203, B_204), k7_tmap_1(A_203, u1_struct_0(B_204))) | ~m1_subset_1(u1_struct_0(B_204), k1_zfmisc_1(u1_struct_0(A_203))) | ~m1_subset_1(k9_tmap_1(A_203, B_204), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_203), u1_struct_0(k8_tmap_1(A_203, B_204))))) | ~v1_funct_2(k9_tmap_1(A_203, B_204), u1_struct_0(A_203), u1_struct_0(k8_tmap_1(A_203, B_204))) | ~v1_funct_1(k9_tmap_1(A_203, B_204)) | ~m1_pre_topc(B_204, A_203) | ~l1_pre_topc(A_203) | ~v2_pre_topc(A_203) | v2_struct_0(A_203))), inference(cnfTransformation, [status(thm)], [f_130])).
% 10.04/3.64  tff(c_649, plain, (![A_256, B_257]: (k7_tmap_1(A_256, u1_struct_0(B_257))=k9_tmap_1(A_256, B_257) | ~m1_subset_1(k7_tmap_1(A_256, u1_struct_0(B_257)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_256), u1_struct_0(k6_tmap_1(A_256, u1_struct_0(B_257)))))) | ~v1_funct_2(k7_tmap_1(A_256, u1_struct_0(B_257)), u1_struct_0(A_256), u1_struct_0(k6_tmap_1(A_256, u1_struct_0(B_257)))) | ~v1_funct_1(k7_tmap_1(A_256, u1_struct_0(B_257))) | v1_xboole_0(u1_struct_0(k6_tmap_1(A_256, u1_struct_0(B_257)))) | v1_xboole_0(u1_struct_0(k8_tmap_1(A_256, B_257))) | ~m1_subset_1(u1_struct_0(B_257), k1_zfmisc_1(u1_struct_0(A_256))) | ~m1_subset_1(k9_tmap_1(A_256, B_257), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_256), u1_struct_0(k8_tmap_1(A_256, B_257))))) | ~v1_funct_2(k9_tmap_1(A_256, B_257), u1_struct_0(A_256), u1_struct_0(k8_tmap_1(A_256, B_257))) | ~v1_funct_1(k9_tmap_1(A_256, B_257)) | ~m1_pre_topc(B_257, A_256) | ~l1_pre_topc(A_256) | ~v2_pre_topc(A_256) | v2_struct_0(A_256))), inference(resolution, [status(thm)], [c_396, c_12])).
% 10.04/3.64  tff(c_974, plain, (![A_329, B_330]: (k7_tmap_1(A_329, u1_struct_0(B_330))=k9_tmap_1(A_329, B_330) | ~v1_funct_2(k7_tmap_1(A_329, u1_struct_0(B_330)), u1_struct_0(A_329), u1_struct_0(k6_tmap_1(A_329, u1_struct_0(B_330)))) | ~v1_funct_1(k7_tmap_1(A_329, u1_struct_0(B_330))) | v1_xboole_0(u1_struct_0(k6_tmap_1(A_329, u1_struct_0(B_330)))) | v1_xboole_0(u1_struct_0(k8_tmap_1(A_329, B_330))) | ~m1_subset_1(k9_tmap_1(A_329, B_330), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_329), u1_struct_0(k8_tmap_1(A_329, B_330))))) | ~v1_funct_2(k9_tmap_1(A_329, B_330), u1_struct_0(A_329), u1_struct_0(k8_tmap_1(A_329, B_330))) | ~v1_funct_1(k9_tmap_1(A_329, B_330)) | ~m1_pre_topc(B_330, A_329) | ~m1_subset_1(u1_struct_0(B_330), k1_zfmisc_1(u1_struct_0(A_329))) | ~l1_pre_topc(A_329) | ~v2_pre_topc(A_329) | v2_struct_0(A_329))), inference(resolution, [status(thm)], [c_32, c_649])).
% 10.04/3.64  tff(c_1018, plain, (![A_339, B_340]: (k7_tmap_1(A_339, u1_struct_0(B_340))=k9_tmap_1(A_339, B_340) | ~v1_funct_1(k7_tmap_1(A_339, u1_struct_0(B_340))) | v1_xboole_0(u1_struct_0(k6_tmap_1(A_339, u1_struct_0(B_340)))) | v1_xboole_0(u1_struct_0(k8_tmap_1(A_339, B_340))) | ~m1_subset_1(k9_tmap_1(A_339, B_340), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_339), u1_struct_0(k8_tmap_1(A_339, B_340))))) | ~v1_funct_2(k9_tmap_1(A_339, B_340), u1_struct_0(A_339), u1_struct_0(k8_tmap_1(A_339, B_340))) | ~v1_funct_1(k9_tmap_1(A_339, B_340)) | ~m1_pre_topc(B_340, A_339) | ~m1_subset_1(u1_struct_0(B_340), k1_zfmisc_1(u1_struct_0(A_339))) | ~l1_pre_topc(A_339) | ~v2_pre_topc(A_339) | v2_struct_0(A_339))), inference(resolution, [status(thm)], [c_34, c_974])).
% 10.04/3.64  tff(c_1023, plain, (![A_341, B_342]: (k7_tmap_1(A_341, u1_struct_0(B_342))=k9_tmap_1(A_341, B_342) | ~v1_funct_1(k7_tmap_1(A_341, u1_struct_0(B_342))) | v1_xboole_0(u1_struct_0(k6_tmap_1(A_341, u1_struct_0(B_342)))) | v1_xboole_0(u1_struct_0(k8_tmap_1(A_341, B_342))) | ~v1_funct_2(k9_tmap_1(A_341, B_342), u1_struct_0(A_341), u1_struct_0(k8_tmap_1(A_341, B_342))) | ~v1_funct_1(k9_tmap_1(A_341, B_342)) | ~m1_subset_1(u1_struct_0(B_342), k1_zfmisc_1(u1_struct_0(A_341))) | ~m1_pre_topc(B_342, A_341) | ~l1_pre_topc(A_341) | ~v2_pre_topc(A_341) | v2_struct_0(A_341))), inference(resolution, [status(thm)], [c_44, c_1018])).
% 10.04/3.64  tff(c_1028, plain, (![A_343, B_344]: (k7_tmap_1(A_343, u1_struct_0(B_344))=k9_tmap_1(A_343, B_344) | ~v1_funct_1(k7_tmap_1(A_343, u1_struct_0(B_344))) | v1_xboole_0(u1_struct_0(k6_tmap_1(A_343, u1_struct_0(B_344)))) | v1_xboole_0(u1_struct_0(k8_tmap_1(A_343, B_344))) | ~v1_funct_1(k9_tmap_1(A_343, B_344)) | ~m1_subset_1(u1_struct_0(B_344), k1_zfmisc_1(u1_struct_0(A_343))) | ~m1_pre_topc(B_344, A_343) | ~l1_pre_topc(A_343) | ~v2_pre_topc(A_343) | v2_struct_0(A_343))), inference(resolution, [status(thm)], [c_46, c_1023])).
% 10.04/3.64  tff(c_1033, plain, (![A_345, B_346]: (k7_tmap_1(A_345, u1_struct_0(B_346))=k9_tmap_1(A_345, B_346) | ~v1_funct_1(k7_tmap_1(A_345, u1_struct_0(B_346))) | v1_xboole_0(u1_struct_0(k6_tmap_1(A_345, u1_struct_0(B_346)))) | v1_xboole_0(u1_struct_0(k8_tmap_1(A_345, B_346))) | ~v1_funct_1(k9_tmap_1(A_345, B_346)) | ~v2_pre_topc(A_345) | v2_struct_0(A_345) | ~m1_pre_topc(B_346, A_345) | ~l1_pre_topc(A_345))), inference(resolution, [status(thm)], [c_64, c_1028])).
% 10.04/3.64  tff(c_1039, plain, (![A_60, B_61]: (k7_tmap_1(A_60, u1_struct_0(B_61))=k9_tmap_1(A_60, B_61) | ~v1_funct_1(k7_tmap_1(A_60, u1_struct_0(B_61))) | v1_xboole_0(u1_struct_0(k8_tmap_1(A_60, B_61))) | v1_xboole_0(u1_struct_0(k8_tmap_1(A_60, B_61))) | ~v1_funct_1(k9_tmap_1(A_60, B_61)) | ~v2_pre_topc(A_60) | v2_struct_0(A_60) | ~m1_pre_topc(B_61, A_60) | ~l1_pre_topc(A_60) | ~m1_pre_topc(B_61, A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(superposition, [status(thm), theory('equality')], [c_233, c_1033])).
% 10.04/3.64  tff(c_1068, plain, (![A_355, B_356]: (k7_tmap_1(A_355, u1_struct_0(B_356))=k9_tmap_1(A_355, B_356) | ~v1_funct_1(k7_tmap_1(A_355, u1_struct_0(B_356))) | ~v1_funct_1(k9_tmap_1(A_355, B_356)) | ~m1_pre_topc(B_356, A_355) | ~l1_pre_topc(A_355) | ~v2_pre_topc(A_355) | v2_struct_0(A_355) | v1_xboole_0(u1_struct_0(k8_tmap_1(A_355, B_356))))), inference(factorization, [status(thm), theory('equality')], [c_1039])).
% 10.04/3.64  tff(c_1073, plain, (![A_357, B_358]: (~l1_struct_0(k8_tmap_1(A_357, B_358)) | v2_struct_0(k8_tmap_1(A_357, B_358)) | k7_tmap_1(A_357, u1_struct_0(B_358))=k9_tmap_1(A_357, B_358) | ~v1_funct_1(k7_tmap_1(A_357, u1_struct_0(B_358))) | ~v1_funct_1(k9_tmap_1(A_357, B_358)) | ~m1_pre_topc(B_358, A_357) | ~l1_pre_topc(A_357) | ~v2_pre_topc(A_357) | v2_struct_0(A_357))), inference(resolution, [status(thm)], [c_1068, c_4])).
% 10.04/3.64  tff(c_1081, plain, (![A_359, B_360]: (~l1_struct_0(k8_tmap_1(A_359, B_360)) | v2_struct_0(k8_tmap_1(A_359, B_360)) | k7_tmap_1(A_359, u1_struct_0(B_360))=k9_tmap_1(A_359, B_360) | ~v1_funct_1(k9_tmap_1(A_359, B_360)) | ~v2_pre_topc(A_359) | v2_struct_0(A_359) | ~m1_pre_topc(B_360, A_359) | ~l1_pre_topc(A_359))), inference(resolution, [status(thm)], [c_95, c_1073])).
% 10.04/3.64  tff(c_1086, plain, (![A_361, B_362]: (~l1_struct_0(k8_tmap_1(A_361, B_362)) | k7_tmap_1(A_361, u1_struct_0(B_362))=k9_tmap_1(A_361, B_362) | ~v1_funct_1(k9_tmap_1(A_361, B_362)) | ~v2_pre_topc(A_361) | v2_struct_0(A_361) | ~m1_pre_topc(B_362, A_361) | ~l1_pre_topc(A_361))), inference(resolution, [status(thm)], [c_1081, c_54])).
% 10.04/3.64  tff(c_1091, plain, (![A_363, B_364]: (~l1_struct_0(k8_tmap_1(A_363, B_364)) | k7_tmap_1(A_363, u1_struct_0(B_364))=k9_tmap_1(A_363, B_364) | ~m1_pre_topc(B_364, A_363) | ~l1_pre_topc(A_363) | ~v2_pre_topc(A_363) | v2_struct_0(A_363))), inference(resolution, [status(thm)], [c_48, c_1086])).
% 10.04/3.64  tff(c_1096, plain, (![A_365, B_366]: (k7_tmap_1(A_365, u1_struct_0(B_366))=k9_tmap_1(A_365, B_366) | ~m1_pre_topc(B_366, A_365) | ~l1_pre_topc(A_365) | ~v2_pre_topc(A_365) | v2_struct_0(A_365) | ~l1_pre_topc(k8_tmap_1(A_365, B_366)))), inference(resolution, [status(thm)], [c_2, c_1091])).
% 10.04/3.64  tff(c_1101, plain, (![A_367, B_368]: (k7_tmap_1(A_367, u1_struct_0(B_368))=k9_tmap_1(A_367, B_368) | ~m1_pre_topc(B_368, A_367) | ~l1_pre_topc(A_367) | ~v2_pre_topc(A_367) | v2_struct_0(A_367))), inference(resolution, [status(thm)], [c_38, c_1096])).
% 10.04/3.64  tff(c_98, plain, (![A_96, B_97]: (k7_tmap_1(A_96, B_97)=k6_partfun1(u1_struct_0(A_96)) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96) | ~v2_pre_topc(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.04/3.64  tff(c_105, plain, (![A_73, B_75]: (k7_tmap_1(A_73, u1_struct_0(B_75))=k6_partfun1(u1_struct_0(A_73)) | ~v2_pre_topc(A_73) | v2_struct_0(A_73) | ~m1_pre_topc(B_75, A_73) | ~l1_pre_topc(A_73))), inference(resolution, [status(thm)], [c_64, c_98])).
% 10.04/3.64  tff(c_1204, plain, (![A_373, B_374]: (k9_tmap_1(A_373, B_374)=k6_partfun1(u1_struct_0(A_373)) | ~v2_pre_topc(A_373) | v2_struct_0(A_373) | ~m1_pre_topc(B_374, A_373) | ~l1_pre_topc(A_373) | ~m1_pre_topc(B_374, A_373) | ~l1_pre_topc(A_373) | ~v2_pre_topc(A_373) | v2_struct_0(A_373))), inference(superposition, [status(thm), theory('equality')], [c_1101, c_105])).
% 10.04/3.64  tff(c_1206, plain, (k6_partfun1(u1_struct_0('#skF_4'))=k9_tmap_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_68, c_1204])).
% 10.04/3.64  tff(c_1209, plain, (k6_partfun1(u1_struct_0('#skF_4'))=k9_tmap_1('#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_68, c_1206])).
% 10.04/3.64  tff(c_1210, plain, (k6_partfun1(u1_struct_0('#skF_4'))=k9_tmap_1('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_76, c_1209])).
% 10.04/3.64  tff(c_170, plain, (![A_124, C_125]: (v1_funct_1(k2_tmap_1(A_124, k6_tmap_1(A_124, u1_struct_0(C_125)), k7_tmap_1(A_124, u1_struct_0(C_125)), C_125)) | ~m1_pre_topc(C_125, A_124) | v2_struct_0(C_125) | ~m1_subset_1(u1_struct_0(C_125), k1_zfmisc_1(u1_struct_0(A_124))) | ~l1_pre_topc(A_124) | ~v2_pre_topc(A_124) | v2_struct_0(A_124))), inference(cnfTransformation, [status(thm)], [f_217])).
% 10.04/3.64  tff(c_286, plain, (![A_164, B_165]: (v1_funct_1(k2_tmap_1(A_164, k6_tmap_1(A_164, u1_struct_0(B_165)), k6_partfun1(u1_struct_0(A_164)), B_165)) | ~m1_pre_topc(B_165, A_164) | v2_struct_0(B_165) | ~m1_subset_1(u1_struct_0(B_165), k1_zfmisc_1(u1_struct_0(A_164))) | ~l1_pre_topc(A_164) | ~v2_pre_topc(A_164) | v2_struct_0(A_164) | ~v2_pre_topc(A_164) | v2_struct_0(A_164) | ~m1_pre_topc(B_165, A_164) | ~l1_pre_topc(A_164))), inference(superposition, [status(thm), theory('equality')], [c_105, c_170])).
% 10.04/3.64  tff(c_289, plain, (![A_60, B_61]: (v1_funct_1(k2_tmap_1(A_60, k8_tmap_1(A_60, B_61), k6_partfun1(u1_struct_0(A_60)), B_61)) | ~m1_pre_topc(B_61, A_60) | v2_struct_0(B_61) | ~m1_subset_1(u1_struct_0(B_61), k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60) | ~m1_pre_topc(B_61, A_60) | ~l1_pre_topc(A_60) | ~m1_pre_topc(B_61, A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(superposition, [status(thm), theory('equality')], [c_233, c_286])).
% 10.04/3.64  tff(c_1286, plain, (![B_61]: (v1_funct_1(k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', B_61), k9_tmap_1('#skF_4', '#skF_5'), B_61)) | ~m1_pre_topc(B_61, '#skF_4') | v2_struct_0(B_61) | ~m1_subset_1(u1_struct_0(B_61), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_61, '#skF_4') | ~l1_pre_topc('#skF_4') | ~m1_pre_topc(B_61, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1210, c_289])).
% 10.04/3.64  tff(c_1395, plain, (![B_61]: (v1_funct_1(k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', B_61), k9_tmap_1('#skF_4', '#skF_5'), B_61)) | v2_struct_0(B_61) | ~m1_subset_1(u1_struct_0(B_61), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc(B_61, '#skF_4') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_72, c_74, c_74, c_72, c_1286])).
% 10.04/3.64  tff(c_1559, plain, (![B_378]: (v1_funct_1(k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', B_378), k9_tmap_1('#skF_4', '#skF_5'), B_378)) | v2_struct_0(B_378) | ~m1_subset_1(u1_struct_0(B_378), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc(B_378, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_76, c_1395])).
% 10.04/3.64  tff(c_1562, plain, (![B_75]: (v1_funct_1(k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', B_75), k9_tmap_1('#skF_4', '#skF_5'), B_75)) | v2_struct_0(B_75) | ~m1_pre_topc(B_75, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_64, c_1559])).
% 10.04/3.64  tff(c_1566, plain, (![B_379]: (v1_funct_1(k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', B_379), k9_tmap_1('#skF_4', '#skF_5'), B_379)) | v2_struct_0(B_379) | ~m1_pre_topc(B_379, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1562])).
% 10.04/3.64  tff(c_66, plain, (~m1_subset_1(k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', '#skF_5'), k9_tmap_1('#skF_4', '#skF_5'), '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_4', '#skF_5'))))) | ~v5_pre_topc(k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', '#skF_5'), k9_tmap_1('#skF_4', '#skF_5'), '#skF_5'), '#skF_5', k8_tmap_1('#skF_4', '#skF_5')) | ~v1_funct_2(k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', '#skF_5'), k9_tmap_1('#skF_4', '#skF_5'), '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_4', '#skF_5'))) | ~v1_funct_1(k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', '#skF_5'), k9_tmap_1('#skF_4', '#skF_5'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_246])).
% 10.04/3.64  tff(c_81, plain, (~v1_funct_1(k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', '#skF_5'), k9_tmap_1('#skF_4', '#skF_5'), '#skF_5'))), inference(splitLeft, [status(thm)], [c_66])).
% 10.04/3.64  tff(c_1569, plain, (v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1566, c_81])).
% 10.04/3.64  tff(c_1572, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1569])).
% 10.04/3.64  tff(c_1574, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_1572])).
% 10.04/3.64  tff(c_1575, plain, (~v1_funct_2(k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', '#skF_5'), k9_tmap_1('#skF_4', '#skF_5'), '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_4', '#skF_5'))) | ~v5_pre_topc(k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', '#skF_5'), k9_tmap_1('#skF_4', '#skF_5'), '#skF_5'), '#skF_5', k8_tmap_1('#skF_4', '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', '#skF_5'), k9_tmap_1('#skF_4', '#skF_5'), '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_4', '#skF_5')))))), inference(splitRight, [status(thm)], [c_66])).
% 10.04/3.64  tff(c_1581, plain, (~m1_subset_1(k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', '#skF_5'), k9_tmap_1('#skF_4', '#skF_5'), '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_4', '#skF_5')))))), inference(splitLeft, [status(thm)], [c_1575])).
% 10.04/3.64  tff(c_3467, plain, (v2_struct_0('#skF_5') | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_3454, c_1581])).
% 10.04/3.64  tff(c_3479, plain, (v2_struct_0('#skF_5') | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_3467])).
% 10.04/3.64  tff(c_3480, plain, (~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_70, c_3479])).
% 10.04/3.64  tff(c_3483, plain, (~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_64, c_3480])).
% 10.04/3.64  tff(c_3487, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_3483])).
% 10.04/3.64  tff(c_3488, plain, (~v5_pre_topc(k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', '#skF_5'), k9_tmap_1('#skF_4', '#skF_5'), '#skF_5'), '#skF_5', k8_tmap_1('#skF_4', '#skF_5')) | ~v1_funct_2(k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', '#skF_5'), k9_tmap_1('#skF_4', '#skF_5'), '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_1575])).
% 10.04/3.64  tff(c_3563, plain, (~v1_funct_2(k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', '#skF_5'), k9_tmap_1('#skF_4', '#skF_5'), '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_3488])).
% 10.04/3.64  tff(c_5335, plain, (v2_struct_0('#skF_5') | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_5332, c_3563])).
% 10.04/3.64  tff(c_5338, plain, (v2_struct_0('#skF_5') | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_5335])).
% 10.04/3.64  tff(c_5339, plain, (~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_70, c_5338])).
% 10.04/3.64  tff(c_5342, plain, (~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_64, c_5339])).
% 10.04/3.64  tff(c_5346, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_5342])).
% 10.04/3.64  tff(c_5347, plain, (~v5_pre_topc(k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', '#skF_5'), k9_tmap_1('#skF_4', '#skF_5'), '#skF_5'), '#skF_5', k8_tmap_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_3488])).
% 10.04/3.64  tff(c_5405, plain, (![A_1041, B_1042]: (k6_tmap_1(A_1041, u1_struct_0(B_1042))=k8_tmap_1(A_1041, B_1042) | ~m1_subset_1(u1_struct_0(B_1042), k1_zfmisc_1(u1_struct_0(A_1041))) | ~l1_pre_topc(k8_tmap_1(A_1041, B_1042)) | ~v2_pre_topc(k8_tmap_1(A_1041, B_1042)) | ~v1_pre_topc(k8_tmap_1(A_1041, B_1042)) | ~m1_pre_topc(B_1042, A_1041) | ~l1_pre_topc(A_1041) | ~v2_pre_topc(A_1041) | v2_struct_0(A_1041))), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.04/3.64  tff(c_5410, plain, (![A_1043, B_1044]: (k6_tmap_1(A_1043, u1_struct_0(B_1044))=k8_tmap_1(A_1043, B_1044) | ~l1_pre_topc(k8_tmap_1(A_1043, B_1044)) | ~v2_pre_topc(k8_tmap_1(A_1043, B_1044)) | ~v1_pre_topc(k8_tmap_1(A_1043, B_1044)) | ~v2_pre_topc(A_1043) | v2_struct_0(A_1043) | ~m1_pre_topc(B_1044, A_1043) | ~l1_pre_topc(A_1043))), inference(resolution, [status(thm)], [c_64, c_5405])).
% 10.04/3.64  tff(c_5419, plain, (![A_1047, B_1048]: (k6_tmap_1(A_1047, u1_struct_0(B_1048))=k8_tmap_1(A_1047, B_1048) | ~l1_pre_topc(k8_tmap_1(A_1047, B_1048)) | ~v1_pre_topc(k8_tmap_1(A_1047, B_1048)) | ~m1_pre_topc(B_1048, A_1047) | ~l1_pre_topc(A_1047) | ~v2_pre_topc(A_1047) | v2_struct_0(A_1047))), inference(resolution, [status(thm)], [c_50, c_5410])).
% 10.04/3.64  tff(c_5424, plain, (![A_1049, B_1050]: (k6_tmap_1(A_1049, u1_struct_0(B_1050))=k8_tmap_1(A_1049, B_1050) | ~l1_pre_topc(k8_tmap_1(A_1049, B_1050)) | ~m1_pre_topc(B_1050, A_1049) | ~l1_pre_topc(A_1049) | ~v2_pre_topc(A_1049) | v2_struct_0(A_1049))), inference(resolution, [status(thm)], [c_52, c_5419])).
% 10.04/3.64  tff(c_5428, plain, (![A_60, B_61]: (k6_tmap_1(A_60, u1_struct_0(B_61))=k8_tmap_1(A_60, B_61) | ~m1_pre_topc(B_61, A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(resolution, [status(thm)], [c_38, c_5424])).
% 10.04/3.64  tff(c_5625, plain, (![A_1110, B_1111]: (r1_funct_2(u1_struct_0(A_1110), u1_struct_0(k8_tmap_1(A_1110, B_1111)), u1_struct_0(A_1110), u1_struct_0(k6_tmap_1(A_1110, u1_struct_0(B_1111))), k9_tmap_1(A_1110, B_1111), k7_tmap_1(A_1110, u1_struct_0(B_1111))) | ~m1_subset_1(u1_struct_0(B_1111), k1_zfmisc_1(u1_struct_0(A_1110))) | ~m1_subset_1(k9_tmap_1(A_1110, B_1111), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1110), u1_struct_0(k8_tmap_1(A_1110, B_1111))))) | ~v1_funct_2(k9_tmap_1(A_1110, B_1111), u1_struct_0(A_1110), u1_struct_0(k8_tmap_1(A_1110, B_1111))) | ~v1_funct_1(k9_tmap_1(A_1110, B_1111)) | ~m1_pre_topc(B_1111, A_1110) | ~l1_pre_topc(A_1110) | ~v2_pre_topc(A_1110) | v2_struct_0(A_1110))), inference(cnfTransformation, [status(thm)], [f_130])).
% 10.04/3.64  tff(c_5883, plain, (![A_1165, B_1166]: (k7_tmap_1(A_1165, u1_struct_0(B_1166))=k9_tmap_1(A_1165, B_1166) | ~m1_subset_1(k7_tmap_1(A_1165, u1_struct_0(B_1166)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1165), u1_struct_0(k6_tmap_1(A_1165, u1_struct_0(B_1166)))))) | ~v1_funct_2(k7_tmap_1(A_1165, u1_struct_0(B_1166)), u1_struct_0(A_1165), u1_struct_0(k6_tmap_1(A_1165, u1_struct_0(B_1166)))) | ~v1_funct_1(k7_tmap_1(A_1165, u1_struct_0(B_1166))) | v1_xboole_0(u1_struct_0(k6_tmap_1(A_1165, u1_struct_0(B_1166)))) | v1_xboole_0(u1_struct_0(k8_tmap_1(A_1165, B_1166))) | ~m1_subset_1(u1_struct_0(B_1166), k1_zfmisc_1(u1_struct_0(A_1165))) | ~m1_subset_1(k9_tmap_1(A_1165, B_1166), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1165), u1_struct_0(k8_tmap_1(A_1165, B_1166))))) | ~v1_funct_2(k9_tmap_1(A_1165, B_1166), u1_struct_0(A_1165), u1_struct_0(k8_tmap_1(A_1165, B_1166))) | ~v1_funct_1(k9_tmap_1(A_1165, B_1166)) | ~m1_pre_topc(B_1166, A_1165) | ~l1_pre_topc(A_1165) | ~v2_pre_topc(A_1165) | v2_struct_0(A_1165))), inference(resolution, [status(thm)], [c_5625, c_12])).
% 10.04/3.64  tff(c_6208, plain, (![A_1238, B_1239]: (k7_tmap_1(A_1238, u1_struct_0(B_1239))=k9_tmap_1(A_1238, B_1239) | ~v1_funct_2(k7_tmap_1(A_1238, u1_struct_0(B_1239)), u1_struct_0(A_1238), u1_struct_0(k6_tmap_1(A_1238, u1_struct_0(B_1239)))) | ~v1_funct_1(k7_tmap_1(A_1238, u1_struct_0(B_1239))) | v1_xboole_0(u1_struct_0(k6_tmap_1(A_1238, u1_struct_0(B_1239)))) | v1_xboole_0(u1_struct_0(k8_tmap_1(A_1238, B_1239))) | ~m1_subset_1(k9_tmap_1(A_1238, B_1239), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1238), u1_struct_0(k8_tmap_1(A_1238, B_1239))))) | ~v1_funct_2(k9_tmap_1(A_1238, B_1239), u1_struct_0(A_1238), u1_struct_0(k8_tmap_1(A_1238, B_1239))) | ~v1_funct_1(k9_tmap_1(A_1238, B_1239)) | ~m1_pre_topc(B_1239, A_1238) | ~m1_subset_1(u1_struct_0(B_1239), k1_zfmisc_1(u1_struct_0(A_1238))) | ~l1_pre_topc(A_1238) | ~v2_pre_topc(A_1238) | v2_struct_0(A_1238))), inference(resolution, [status(thm)], [c_32, c_5883])).
% 10.04/3.64  tff(c_6252, plain, (![A_1248, B_1249]: (k7_tmap_1(A_1248, u1_struct_0(B_1249))=k9_tmap_1(A_1248, B_1249) | ~v1_funct_1(k7_tmap_1(A_1248, u1_struct_0(B_1249))) | v1_xboole_0(u1_struct_0(k6_tmap_1(A_1248, u1_struct_0(B_1249)))) | v1_xboole_0(u1_struct_0(k8_tmap_1(A_1248, B_1249))) | ~m1_subset_1(k9_tmap_1(A_1248, B_1249), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1248), u1_struct_0(k8_tmap_1(A_1248, B_1249))))) | ~v1_funct_2(k9_tmap_1(A_1248, B_1249), u1_struct_0(A_1248), u1_struct_0(k8_tmap_1(A_1248, B_1249))) | ~v1_funct_1(k9_tmap_1(A_1248, B_1249)) | ~m1_pre_topc(B_1249, A_1248) | ~m1_subset_1(u1_struct_0(B_1249), k1_zfmisc_1(u1_struct_0(A_1248))) | ~l1_pre_topc(A_1248) | ~v2_pre_topc(A_1248) | v2_struct_0(A_1248))), inference(resolution, [status(thm)], [c_34, c_6208])).
% 10.04/3.64  tff(c_6257, plain, (![A_1250, B_1251]: (k7_tmap_1(A_1250, u1_struct_0(B_1251))=k9_tmap_1(A_1250, B_1251) | ~v1_funct_1(k7_tmap_1(A_1250, u1_struct_0(B_1251))) | v1_xboole_0(u1_struct_0(k6_tmap_1(A_1250, u1_struct_0(B_1251)))) | v1_xboole_0(u1_struct_0(k8_tmap_1(A_1250, B_1251))) | ~v1_funct_2(k9_tmap_1(A_1250, B_1251), u1_struct_0(A_1250), u1_struct_0(k8_tmap_1(A_1250, B_1251))) | ~v1_funct_1(k9_tmap_1(A_1250, B_1251)) | ~m1_subset_1(u1_struct_0(B_1251), k1_zfmisc_1(u1_struct_0(A_1250))) | ~m1_pre_topc(B_1251, A_1250) | ~l1_pre_topc(A_1250) | ~v2_pre_topc(A_1250) | v2_struct_0(A_1250))), inference(resolution, [status(thm)], [c_44, c_6252])).
% 10.04/3.64  tff(c_6262, plain, (![A_1252, B_1253]: (k7_tmap_1(A_1252, u1_struct_0(B_1253))=k9_tmap_1(A_1252, B_1253) | ~v1_funct_1(k7_tmap_1(A_1252, u1_struct_0(B_1253))) | v1_xboole_0(u1_struct_0(k6_tmap_1(A_1252, u1_struct_0(B_1253)))) | v1_xboole_0(u1_struct_0(k8_tmap_1(A_1252, B_1253))) | ~v1_funct_1(k9_tmap_1(A_1252, B_1253)) | ~m1_subset_1(u1_struct_0(B_1253), k1_zfmisc_1(u1_struct_0(A_1252))) | ~m1_pre_topc(B_1253, A_1252) | ~l1_pre_topc(A_1252) | ~v2_pre_topc(A_1252) | v2_struct_0(A_1252))), inference(resolution, [status(thm)], [c_46, c_6257])).
% 10.04/3.64  tff(c_6267, plain, (![A_1254, B_1255]: (k7_tmap_1(A_1254, u1_struct_0(B_1255))=k9_tmap_1(A_1254, B_1255) | ~v1_funct_1(k7_tmap_1(A_1254, u1_struct_0(B_1255))) | v1_xboole_0(u1_struct_0(k6_tmap_1(A_1254, u1_struct_0(B_1255)))) | v1_xboole_0(u1_struct_0(k8_tmap_1(A_1254, B_1255))) | ~v1_funct_1(k9_tmap_1(A_1254, B_1255)) | ~v2_pre_topc(A_1254) | v2_struct_0(A_1254) | ~m1_pre_topc(B_1255, A_1254) | ~l1_pre_topc(A_1254))), inference(resolution, [status(thm)], [c_64, c_6262])).
% 10.04/3.64  tff(c_6273, plain, (![A_60, B_61]: (k7_tmap_1(A_60, u1_struct_0(B_61))=k9_tmap_1(A_60, B_61) | ~v1_funct_1(k7_tmap_1(A_60, u1_struct_0(B_61))) | v1_xboole_0(u1_struct_0(k8_tmap_1(A_60, B_61))) | v1_xboole_0(u1_struct_0(k8_tmap_1(A_60, B_61))) | ~v1_funct_1(k9_tmap_1(A_60, B_61)) | ~v2_pre_topc(A_60) | v2_struct_0(A_60) | ~m1_pre_topc(B_61, A_60) | ~l1_pre_topc(A_60) | ~m1_pre_topc(B_61, A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(superposition, [status(thm), theory('equality')], [c_5428, c_6267])).
% 10.04/3.64  tff(c_6304, plain, (![A_1264, B_1265]: (k7_tmap_1(A_1264, u1_struct_0(B_1265))=k9_tmap_1(A_1264, B_1265) | ~v1_funct_1(k7_tmap_1(A_1264, u1_struct_0(B_1265))) | ~v1_funct_1(k9_tmap_1(A_1264, B_1265)) | ~m1_pre_topc(B_1265, A_1264) | ~l1_pre_topc(A_1264) | ~v2_pre_topc(A_1264) | v2_struct_0(A_1264) | v1_xboole_0(u1_struct_0(k8_tmap_1(A_1264, B_1265))))), inference(factorization, [status(thm), theory('equality')], [c_6273])).
% 10.04/3.64  tff(c_1576, plain, (v1_funct_1(k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', '#skF_5'), k9_tmap_1('#skF_4', '#skF_5'), '#skF_5'))), inference(splitRight, [status(thm)], [c_66])).
% 10.04/3.64  tff(c_5348, plain, (v1_funct_2(k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', '#skF_5'), k9_tmap_1('#skF_4', '#skF_5'), '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_3488])).
% 10.04/3.64  tff(c_3489, plain, (m1_subset_1(k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', '#skF_5'), k9_tmap_1('#skF_4', '#skF_5'), '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_4', '#skF_5')))))), inference(splitRight, [status(thm)], [c_1575])).
% 10.04/3.64  tff(c_5384, plain, (![D_1031, B_1033, A_1035, C_1034, F_1032]: (r1_funct_2(A_1035, B_1033, C_1034, D_1031, F_1032, F_1032) | ~m1_subset_1(F_1032, k1_zfmisc_1(k2_zfmisc_1(C_1034, D_1031))) | ~v1_funct_2(F_1032, C_1034, D_1031) | ~m1_subset_1(F_1032, k1_zfmisc_1(k2_zfmisc_1(A_1035, B_1033))) | ~v1_funct_2(F_1032, A_1035, B_1033) | ~v1_funct_1(F_1032) | v1_xboole_0(D_1031) | v1_xboole_0(B_1033))), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.04/3.64  tff(c_5390, plain, (![A_1035, B_1033]: (r1_funct_2(A_1035, B_1033, u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_4', '#skF_5')), k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', '#skF_5'), k9_tmap_1('#skF_4', '#skF_5'), '#skF_5'), k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', '#skF_5'), k9_tmap_1('#skF_4', '#skF_5'), '#skF_5')) | ~v1_funct_2(k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', '#skF_5'), k9_tmap_1('#skF_4', '#skF_5'), '#skF_5'), u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_4', '#skF_5'))) | ~m1_subset_1(k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', '#skF_5'), k9_tmap_1('#skF_4', '#skF_5'), '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(A_1035, B_1033))) | ~v1_funct_2(k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', '#skF_5'), k9_tmap_1('#skF_4', '#skF_5'), '#skF_5'), A_1035, B_1033) | ~v1_funct_1(k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', '#skF_5'), k9_tmap_1('#skF_4', '#skF_5'), '#skF_5')) | v1_xboole_0(u1_struct_0(k8_tmap_1('#skF_4', '#skF_5'))) | v1_xboole_0(B_1033))), inference(resolution, [status(thm)], [c_3489, c_5384])).
% 10.04/3.64  tff(c_5395, plain, (![A_1035, B_1033]: (r1_funct_2(A_1035, B_1033, u1_struct_0('#skF_5'), u1_struct_0(k8_tmap_1('#skF_4', '#skF_5')), k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', '#skF_5'), k9_tmap_1('#skF_4', '#skF_5'), '#skF_5'), k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', '#skF_5'), k9_tmap_1('#skF_4', '#skF_5'), '#skF_5')) | ~m1_subset_1(k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', '#skF_5'), k9_tmap_1('#skF_4', '#skF_5'), '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(A_1035, B_1033))) | ~v1_funct_2(k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', '#skF_5'), k9_tmap_1('#skF_4', '#skF_5'), '#skF_5'), A_1035, B_1033) | v1_xboole_0(u1_struct_0(k8_tmap_1('#skF_4', '#skF_5'))) | v1_xboole_0(B_1033))), inference(demodulation, [status(thm), theory('equality')], [c_1576, c_5348, c_5390])).
% 10.04/3.64  tff(c_5462, plain, (v1_xboole_0(u1_struct_0(k8_tmap_1('#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_5395])).
% 10.04/3.64  tff(c_5466, plain, (~l1_struct_0(k8_tmap_1('#skF_4', '#skF_5')) | v2_struct_0(k8_tmap_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_5462, c_4])).
% 10.04/3.64  tff(c_5467, plain, (~l1_struct_0(k8_tmap_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_5466])).
% 10.04/3.64  tff(c_5471, plain, (~l1_pre_topc(k8_tmap_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_2, c_5467])).
% 10.04/3.64  tff(c_5474, plain, (~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_38, c_5471])).
% 10.04/3.64  tff(c_5477, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_68, c_5474])).
% 10.04/3.64  tff(c_5479, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_5477])).
% 10.04/3.64  tff(c_5480, plain, (v2_struct_0(k8_tmap_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_5466])).
% 10.04/3.64  tff(c_5485, plain, (~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_5480, c_54])).
% 10.04/3.64  tff(c_5488, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_68, c_5485])).
% 10.04/3.64  tff(c_5490, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_5488])).
% 10.04/3.64  tff(c_5492, plain, (~v1_xboole_0(u1_struct_0(k8_tmap_1('#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_5395])).
% 10.04/3.64  tff(c_6307, plain, (k7_tmap_1('#skF_4', u1_struct_0('#skF_5'))=k9_tmap_1('#skF_4', '#skF_5') | ~v1_funct_1(k7_tmap_1('#skF_4', u1_struct_0('#skF_5'))) | ~v1_funct_1(k9_tmap_1('#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_6304, c_5492])).
% 10.04/3.64  tff(c_6313, plain, (k7_tmap_1('#skF_4', u1_struct_0('#skF_5'))=k9_tmap_1('#skF_4', '#skF_5') | ~v1_funct_1(k7_tmap_1('#skF_4', u1_struct_0('#skF_5'))) | ~v1_funct_1(k9_tmap_1('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_68, c_6307])).
% 10.04/3.64  tff(c_6314, plain, (k7_tmap_1('#skF_4', u1_struct_0('#skF_5'))=k9_tmap_1('#skF_4', '#skF_5') | ~v1_funct_1(k7_tmap_1('#skF_4', u1_struct_0('#skF_5'))) | ~v1_funct_1(k9_tmap_1('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_76, c_6313])).
% 10.04/3.64  tff(c_6316, plain, (~v1_funct_1(k9_tmap_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_6314])).
% 10.04/3.64  tff(c_6319, plain, (~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_6316])).
% 10.04/3.64  tff(c_6322, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_68, c_6319])).
% 10.04/3.64  tff(c_6324, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_6322])).
% 10.04/3.64  tff(c_6325, plain, (~v1_funct_1(k7_tmap_1('#skF_4', u1_struct_0('#skF_5'))) | k7_tmap_1('#skF_4', u1_struct_0('#skF_5'))=k9_tmap_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_6314])).
% 10.04/3.64  tff(c_6327, plain, (~v1_funct_1(k7_tmap_1('#skF_4', u1_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_6325])).
% 10.04/3.64  tff(c_6333, plain, (~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_3499, c_6327])).
% 10.04/3.64  tff(c_6339, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_74, c_6333])).
% 10.04/3.64  tff(c_6341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_6339])).
% 10.04/3.64  tff(c_6342, plain, (k7_tmap_1('#skF_4', u1_struct_0('#skF_5'))=k9_tmap_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_6325])).
% 10.04/3.64  tff(c_5429, plain, (![A_1051, B_1052]: (k6_tmap_1(A_1051, u1_struct_0(B_1052))=k8_tmap_1(A_1051, B_1052) | ~m1_pre_topc(B_1052, A_1051) | ~l1_pre_topc(A_1051) | ~v2_pre_topc(A_1051) | v2_struct_0(A_1051))), inference(resolution, [status(thm)], [c_38, c_5424])).
% 10.04/3.64  tff(c_58, plain, (![A_66, C_72]: (v5_pre_topc(k2_tmap_1(A_66, k6_tmap_1(A_66, u1_struct_0(C_72)), k7_tmap_1(A_66, u1_struct_0(C_72)), C_72), C_72, k6_tmap_1(A_66, u1_struct_0(C_72))) | ~m1_pre_topc(C_72, A_66) | v2_struct_0(C_72) | ~m1_subset_1(u1_struct_0(C_72), k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_217])).
% 10.04/3.64  tff(c_5618, plain, (![A_1108, B_1109]: (v5_pre_topc(k2_tmap_1(A_1108, k6_tmap_1(A_1108, u1_struct_0(B_1109)), k7_tmap_1(A_1108, u1_struct_0(B_1109)), B_1109), B_1109, k8_tmap_1(A_1108, B_1109)) | ~m1_pre_topc(B_1109, A_1108) | v2_struct_0(B_1109) | ~m1_subset_1(u1_struct_0(B_1109), k1_zfmisc_1(u1_struct_0(A_1108))) | ~l1_pre_topc(A_1108) | ~v2_pre_topc(A_1108) | v2_struct_0(A_1108) | ~m1_pre_topc(B_1109, A_1108) | ~l1_pre_topc(A_1108) | ~v2_pre_topc(A_1108) | v2_struct_0(A_1108))), inference(superposition, [status(thm), theory('equality')], [c_5429, c_58])).
% 10.04/3.64  tff(c_5621, plain, (![A_60, B_61]: (v5_pre_topc(k2_tmap_1(A_60, k8_tmap_1(A_60, B_61), k7_tmap_1(A_60, u1_struct_0(B_61)), B_61), B_61, k8_tmap_1(A_60, B_61)) | ~m1_pre_topc(B_61, A_60) | v2_struct_0(B_61) | ~m1_subset_1(u1_struct_0(B_61), k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60) | ~m1_pre_topc(B_61, A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60) | ~m1_pre_topc(B_61, A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(superposition, [status(thm), theory('equality')], [c_5428, c_5618])).
% 10.04/3.64  tff(c_6385, plain, (v5_pre_topc(k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', '#skF_5'), k9_tmap_1('#skF_4', '#skF_5'), '#skF_5'), '#skF_5', k8_tmap_1('#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_5', '#skF_4') | v2_struct_0('#skF_5') | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6342, c_5621])).
% 10.04/3.64  tff(c_6491, plain, (v5_pre_topc(k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', '#skF_5'), k9_tmap_1('#skF_4', '#skF_5'), '#skF_5'), '#skF_5', k8_tmap_1('#skF_4', '#skF_5')) | v2_struct_0('#skF_5') | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_68, c_74, c_72, c_68, c_74, c_72, c_68, c_6385])).
% 10.04/3.64  tff(c_6492, plain, (~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_5347, c_6491])).
% 10.04/3.64  tff(c_6577, plain, (~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_64, c_6492])).
% 10.04/3.64  tff(c_6581, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_6577])).
% 10.04/3.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.04/3.64  
% 10.04/3.64  Inference rules
% 10.04/3.64  ----------------------
% 10.04/3.64  #Ref     : 0
% 10.04/3.64  #Sup     : 1503
% 10.04/3.64  #Fact    : 8
% 10.04/3.64  #Define  : 0
% 10.04/3.64  #Split   : 13
% 10.04/3.64  #Chain   : 0
% 10.04/3.64  #Close   : 0
% 10.04/3.64  
% 10.04/3.64  Ordering : KBO
% 10.04/3.64  
% 10.04/3.64  Simplification rules
% 10.04/3.64  ----------------------
% 10.04/3.64  #Subsume      : 453
% 10.04/3.64  #Demod        : 1370
% 10.04/3.64  #Tautology    : 200
% 10.04/3.64  #SimpNegUnit  : 298
% 10.04/3.64  #BackRed      : 4
% 10.04/3.64  
% 10.04/3.64  #Partial instantiations: 0
% 10.04/3.64  #Strategies tried      : 1
% 10.04/3.64  
% 10.04/3.64  Timing (in seconds)
% 10.04/3.64  ----------------------
% 10.04/3.64  Preprocessing        : 0.40
% 10.04/3.64  Parsing              : 0.20
% 10.04/3.64  CNF conversion       : 0.03
% 10.04/3.64  Main loop            : 2.42
% 10.04/3.64  Inferencing          : 1.09
% 10.04/3.64  Reduction            : 0.60
% 10.04/3.64  Demodulation         : 0.41
% 10.04/3.64  BG Simplification    : 0.11
% 10.04/3.64  Subsumption          : 0.51
% 10.04/3.64  Abstraction          : 0.10
% 10.04/3.64  MUC search           : 0.00
% 10.04/3.64  Cooper               : 0.00
% 10.04/3.64  Total                : 2.90
% 10.04/3.64  Index Insertion      : 0.00
% 10.04/3.64  Index Deletion       : 0.00
% 10.04/3.64  Index Matching       : 0.00
% 10.04/3.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
