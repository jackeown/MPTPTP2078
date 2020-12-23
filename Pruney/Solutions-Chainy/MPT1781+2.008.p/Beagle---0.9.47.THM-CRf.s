%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:46 EST 2020

% Result     : Theorem 4.81s
% Output     : CNFRefutation 5.10s
% Verified   : 
% Statistics : Number of formulae       :  207 (105474 expanded)
%              Number of leaves         :   45 (40306 expanded)
%              Depth                    :   36
%              Number of atoms          :  728 (669230 expanded)
%              Number of equality atoms :   61 (60384 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_tmap_1 > k2_partfun1 > k4_tmap_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_tmap_1,type,(
    k4_tmap_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_341,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
               => ( ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_hidden(D,u1_struct_0(B))
                       => D = k1_funct_1(C,D) ) )
                 => r2_funct_2(u1_struct_0(B),u1_struct_0(A),k4_tmap_1(A,B),C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_tmap_1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_180,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_funct_1(k4_tmap_1(A,B))
        & v1_funct_2(k4_tmap_1(A,B),u1_struct_0(B),u1_struct_0(A))
        & m1_subset_1(k4_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_tmap_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_191,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_147,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ( m1_pre_topc(D,C)
                       => k3_tmap_1(A,B,C,D,E) = k2_partfun1(u1_struct_0(C),u1_struct_0(B),E,u1_struct_0(D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_165,axiom,(
    ! [A,B,C,D] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B)
        & v1_funct_1(C)
        & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B))))
        & l1_struct_0(D) )
     => ( v1_funct_1(k2_tmap_1(A,B,C,D))
        & v1_funct_2(k2_tmap_1(A,B,C,D),u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(k2_tmap_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).

tff(f_115,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_279,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,u1_struct_0(C),u1_struct_0(B))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                 => r2_funct_2(u1_struct_0(C),u1_struct_0(B),D,k3_tmap_1(A,B,C,C,D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tmap_1)).

tff(f_249,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,B) )
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,u1_struct_0(B),u1_struct_0(A))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(A))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(A)))) )
                     => ( ! [F] :
                            ( m1_subset_1(F,u1_struct_0(B))
                           => ( r2_hidden(F,u1_struct_0(C))
                             => k3_funct_2(u1_struct_0(B),u1_struct_0(A),D,F) = k1_funct_1(E,F) ) )
                       => r2_funct_2(u1_struct_0(C),u1_struct_0(A),k2_tmap_1(B,A,D,C),E) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tmap_1)).

tff(f_187,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_88,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_311,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(C,u1_struct_0(B))
               => k1_funct_1(k4_tmap_1(A,B),C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_tmap_1)).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_341])).

tff(c_68,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_341])).

tff(c_64,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_341])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_341])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_341])).

tff(c_60,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_341])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_341])).

tff(c_125,plain,(
    ! [A_209,B_210,D_211] :
      ( r2_funct_2(A_209,B_210,D_211,D_211)
      | ~ m1_subset_1(D_211,k1_zfmisc_1(k2_zfmisc_1(A_209,B_210)))
      | ~ v1_funct_2(D_211,A_209,B_210)
      | ~ v1_funct_1(D_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_127,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_125])).

tff(c_130,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_127])).

tff(c_70,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_341])).

tff(c_28,plain,(
    ! [A_70,B_71] :
      ( m1_subset_1(k4_tmap_1(A_70,B_71),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_71),u1_struct_0(A_70))))
      | ~ m1_pre_topc(B_71,A_70)
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_32,plain,(
    ! [A_70,B_71] :
      ( v1_funct_1(k4_tmap_1(A_70,B_71))
      | ~ m1_pre_topc(B_71,A_70)
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_87,plain,(
    ! [B_191,A_192] :
      ( v2_pre_topc(B_191)
      | ~ m1_pre_topc(B_191,A_192)
      | ~ l1_pre_topc(A_192)
      | ~ v2_pre_topc(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_93,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_87])).

tff(c_97,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_93])).

tff(c_76,plain,(
    ! [B_189,A_190] :
      ( l1_pre_topc(B_189)
      | ~ m1_pre_topc(B_189,A_190)
      | ~ l1_pre_topc(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_82,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_76])).

tff(c_86,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_82])).

tff(c_36,plain,(
    ! [A_75] :
      ( m1_pre_topc(A_75,A_75)
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_317,plain,(
    ! [D_296,C_299,B_297,E_298,A_295] :
      ( k3_tmap_1(A_295,B_297,C_299,D_296,E_298) = k2_partfun1(u1_struct_0(C_299),u1_struct_0(B_297),E_298,u1_struct_0(D_296))
      | ~ m1_pre_topc(D_296,C_299)
      | ~ m1_subset_1(E_298,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_299),u1_struct_0(B_297))))
      | ~ v1_funct_2(E_298,u1_struct_0(C_299),u1_struct_0(B_297))
      | ~ v1_funct_1(E_298)
      | ~ m1_pre_topc(D_296,A_295)
      | ~ m1_pre_topc(C_299,A_295)
      | ~ l1_pre_topc(B_297)
      | ~ v2_pre_topc(B_297)
      | v2_struct_0(B_297)
      | ~ l1_pre_topc(A_295)
      | ~ v2_pre_topc(A_295)
      | v2_struct_0(A_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_323,plain,(
    ! [A_295,D_296] :
      ( k3_tmap_1(A_295,'#skF_2','#skF_3',D_296,'#skF_4') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_296))
      | ~ m1_pre_topc(D_296,'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc(D_296,A_295)
      | ~ m1_pre_topc('#skF_3',A_295)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_295)
      | ~ v2_pre_topc(A_295)
      | v2_struct_0(A_295) ) ),
    inference(resolution,[status(thm)],[c_58,c_317])).

tff(c_328,plain,(
    ! [A_295,D_296] :
      ( k3_tmap_1(A_295,'#skF_2','#skF_3',D_296,'#skF_4') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_296))
      | ~ m1_pre_topc(D_296,'#skF_3')
      | ~ m1_pre_topc(D_296,A_295)
      | ~ m1_pre_topc('#skF_3',A_295)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_295)
      | ~ v2_pre_topc(A_295)
      | v2_struct_0(A_295) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_62,c_60,c_323])).

tff(c_331,plain,(
    ! [A_302,D_303] :
      ( k3_tmap_1(A_302,'#skF_2','#skF_3',D_303,'#skF_4') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_303))
      | ~ m1_pre_topc(D_303,'#skF_3')
      | ~ m1_pre_topc(D_303,A_302)
      | ~ m1_pre_topc('#skF_3',A_302)
      | ~ l1_pre_topc(A_302)
      | ~ v2_pre_topc(A_302)
      | v2_struct_0(A_302) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_328])).

tff(c_335,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_2','#skF_3','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_331])).

tff(c_339,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_2','#skF_3','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_335])).

tff(c_340,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_2','#skF_3','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_339])).

tff(c_341,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_340])).

tff(c_344,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_341])).

tff(c_348,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_344])).

tff(c_350,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_340])).

tff(c_12,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_175,plain,(
    ! [A_235,B_236,C_237,D_238] :
      ( v1_funct_1(k2_tmap_1(A_235,B_236,C_237,D_238))
      | ~ l1_struct_0(D_238)
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_235),u1_struct_0(B_236))))
      | ~ v1_funct_2(C_237,u1_struct_0(A_235),u1_struct_0(B_236))
      | ~ v1_funct_1(C_237)
      | ~ l1_struct_0(B_236)
      | ~ l1_struct_0(A_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_179,plain,(
    ! [D_238] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_4',D_238))
      | ~ l1_struct_0(D_238)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_58,c_175])).

tff(c_183,plain,(
    ! [D_238] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_4',D_238))
      | ~ l1_struct_0(D_238)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_179])).

tff(c_184,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_183])).

tff(c_187,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_184])).

tff(c_191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_187])).

tff(c_193,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_192,plain,(
    ! [D_238] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_4',D_238))
      | ~ l1_struct_0(D_238) ) ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_195,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_192])).

tff(c_198,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_195])).

tff(c_202,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_198])).

tff(c_204,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_213,plain,(
    ! [A_244,B_245,C_246,D_247] :
      ( v1_funct_2(k2_tmap_1(A_244,B_245,C_246,D_247),u1_struct_0(D_247),u1_struct_0(B_245))
      | ~ l1_struct_0(D_247)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_244),u1_struct_0(B_245))))
      | ~ v1_funct_2(C_246,u1_struct_0(A_244),u1_struct_0(B_245))
      | ~ v1_funct_1(C_246)
      | ~ l1_struct_0(B_245)
      | ~ l1_struct_0(A_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_217,plain,(
    ! [D_247] :
      ( v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_4',D_247),u1_struct_0(D_247),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_247)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_58,c_213])).

tff(c_221,plain,(
    ! [D_247] :
      ( v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_4',D_247),u1_struct_0(D_247),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_247) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_204,c_62,c_60,c_217])).

tff(c_203,plain,(
    ! [D_238] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_4',D_238))
      | ~ l1_struct_0(D_238) ) ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_349,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_2','#skF_3','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_340])).

tff(c_251,plain,(
    ! [A_266,B_267,C_268,D_269] :
      ( k2_partfun1(u1_struct_0(A_266),u1_struct_0(B_267),C_268,u1_struct_0(D_269)) = k2_tmap_1(A_266,B_267,C_268,D_269)
      | ~ m1_pre_topc(D_269,A_266)
      | ~ m1_subset_1(C_268,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_266),u1_struct_0(B_267))))
      | ~ v1_funct_2(C_268,u1_struct_0(A_266),u1_struct_0(B_267))
      | ~ v1_funct_1(C_268)
      | ~ l1_pre_topc(B_267)
      | ~ v2_pre_topc(B_267)
      | v2_struct_0(B_267)
      | ~ l1_pre_topc(A_266)
      | ~ v2_pre_topc(A_266)
      | v2_struct_0(A_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_257,plain,(
    ! [D_269] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_269)) = k2_tmap_1('#skF_3','#skF_2','#skF_4',D_269)
      | ~ m1_pre_topc(D_269,'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_58,c_251])).

tff(c_262,plain,(
    ! [D_269] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_269)) = k2_tmap_1('#skF_3','#skF_2','#skF_4',D_269)
      | ~ m1_pre_topc(D_269,'#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_86,c_70,c_68,c_62,c_60,c_257])).

tff(c_263,plain,(
    ! [D_269] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_269)) = k2_tmap_1('#skF_3','#skF_2','#skF_4',D_269)
      | ~ m1_pre_topc(D_269,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_72,c_262])).

tff(c_384,plain,
    ( k3_tmap_1('#skF_2','#skF_2','#skF_3','#skF_3','#skF_4') = k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_349,c_263])).

tff(c_391,plain,(
    k3_tmap_1('#skF_2','#skF_2','#skF_3','#skF_3','#skF_4') = k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_384])).

tff(c_395,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0('#skF_3')) = k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_391,c_349])).

tff(c_329,plain,(
    ! [A_295,D_296] :
      ( k3_tmap_1(A_295,'#skF_2','#skF_3',D_296,'#skF_4') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_296))
      | ~ m1_pre_topc(D_296,'#skF_3')
      | ~ m1_pre_topc(D_296,A_295)
      | ~ m1_pre_topc('#skF_3',A_295)
      | ~ l1_pre_topc(A_295)
      | ~ v2_pre_topc(A_295)
      | v2_struct_0(A_295) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_328])).

tff(c_352,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_350,c_329])).

tff(c_365,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_86,c_350,c_352])).

tff(c_366,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_365])).

tff(c_447,plain,(
    k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_3','#skF_4') = k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_366])).

tff(c_275,plain,(
    ! [C_278,B_279,D_280,A_281] :
      ( r2_funct_2(u1_struct_0(C_278),u1_struct_0(B_279),D_280,k3_tmap_1(A_281,B_279,C_278,C_278,D_280))
      | ~ m1_subset_1(D_280,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_278),u1_struct_0(B_279))))
      | ~ v1_funct_2(D_280,u1_struct_0(C_278),u1_struct_0(B_279))
      | ~ v1_funct_1(D_280)
      | ~ m1_pre_topc(C_278,A_281)
      | v2_struct_0(C_278)
      | ~ l1_pre_topc(B_279)
      | ~ v2_pre_topc(B_279)
      | v2_struct_0(B_279)
      | ~ l1_pre_topc(A_281)
      | ~ v2_pre_topc(A_281)
      | v2_struct_0(A_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_279])).

tff(c_281,plain,(
    ! [A_281] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k3_tmap_1(A_281,'#skF_2','#skF_3','#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc('#skF_3',A_281)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_281)
      | ~ v2_pre_topc(A_281)
      | v2_struct_0(A_281) ) ),
    inference(resolution,[status(thm)],[c_58,c_275])).

tff(c_286,plain,(
    ! [A_281] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k3_tmap_1(A_281,'#skF_2','#skF_3','#skF_3','#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_281)
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_281)
      | ~ v2_pre_topc(A_281)
      | v2_struct_0(A_281) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_62,c_60,c_281])).

tff(c_288,plain,(
    ! [A_282] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k3_tmap_1(A_282,'#skF_2','#skF_3','#skF_3','#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_282)
      | ~ l1_pre_topc(A_282)
      | ~ v2_pre_topc(A_282)
      | v2_struct_0(A_282) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_286])).

tff(c_8,plain,(
    ! [D_11,C_10,A_8,B_9] :
      ( D_11 = C_10
      | ~ r2_funct_2(A_8,B_9,C_10,D_11)
      | ~ m1_subset_1(D_11,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | ~ v1_funct_2(D_11,A_8,B_9)
      | ~ v1_funct_1(D_11)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | ~ v1_funct_2(C_10,A_8,B_9)
      | ~ v1_funct_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_290,plain,(
    ! [A_282] :
      ( k3_tmap_1(A_282,'#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
      | ~ m1_subset_1(k3_tmap_1(A_282,'#skF_2','#skF_3','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k3_tmap_1(A_282,'#skF_2','#skF_3','#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_282,'#skF_2','#skF_3','#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc('#skF_3',A_282)
      | ~ l1_pre_topc(A_282)
      | ~ v2_pre_topc(A_282)
      | v2_struct_0(A_282) ) ),
    inference(resolution,[status(thm)],[c_288,c_8])).

tff(c_293,plain,(
    ! [A_282] :
      ( k3_tmap_1(A_282,'#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
      | ~ m1_subset_1(k3_tmap_1(A_282,'#skF_2','#skF_3','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k3_tmap_1(A_282,'#skF_2','#skF_3','#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_282,'#skF_2','#skF_3','#skF_3','#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_282)
      | ~ l1_pre_topc(A_282)
      | ~ v2_pre_topc(A_282)
      | v2_struct_0(A_282) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_290])).

tff(c_451,plain,
    ( k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
    | ~ m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_3','#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_447,c_293])).

tff(c_458,plain,
    ( k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_86,c_350,c_447,c_447,c_447,c_451])).

tff(c_459,plain,
    ( k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_458])).

tff(c_464,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_459])).

tff(c_467,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_203,c_464])).

tff(c_471,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_467])).

tff(c_473,plain,(
    v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_459])).

tff(c_22,plain,(
    ! [A_66,B_67,C_68,D_69] :
      ( m1_subset_1(k2_tmap_1(A_66,B_67,C_68,D_69),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_69),u1_struct_0(B_67))))
      | ~ l1_struct_0(D_69)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_66),u1_struct_0(B_67))))
      | ~ v1_funct_2(C_68,u1_struct_0(A_66),u1_struct_0(B_67))
      | ~ v1_funct_1(C_68)
      | ~ l1_struct_0(B_67)
      | ~ l1_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_472,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_459])).

tff(c_536,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_472])).

tff(c_539,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_536])).

tff(c_543,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_204,c_62,c_60,c_58,c_539])).

tff(c_545,plain,(
    m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_472])).

tff(c_399,plain,
    ( k3_tmap_1('#skF_2','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
    | ~ m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_2','#skF_2','#skF_3','#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_2','#skF_2','#skF_3','#skF_3','#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_391,c_293])).

tff(c_406,plain,
    ( k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_391,c_391,c_391,c_399])).

tff(c_407,plain,
    ( k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_406])).

tff(c_599,plain,
    ( k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3') = '#skF_4'
    | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_545,c_407])).

tff(c_600,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_599])).

tff(c_603,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_221,c_600])).

tff(c_607,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_603])).

tff(c_608,plain,(
    k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_599])).

tff(c_413,plain,(
    ! [D_308,C_306,B_305,E_307,A_309] :
      ( m1_subset_1('#skF_1'(B_305,C_306,E_307,D_308,A_309),u1_struct_0(B_305))
      | r2_funct_2(u1_struct_0(C_306),u1_struct_0(A_309),k2_tmap_1(B_305,A_309,D_308,C_306),E_307)
      | ~ m1_subset_1(E_307,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_306),u1_struct_0(A_309))))
      | ~ v1_funct_2(E_307,u1_struct_0(C_306),u1_struct_0(A_309))
      | ~ v1_funct_1(E_307)
      | ~ m1_subset_1(D_308,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_305),u1_struct_0(A_309))))
      | ~ v1_funct_2(D_308,u1_struct_0(B_305),u1_struct_0(A_309))
      | ~ v1_funct_1(D_308)
      | ~ m1_pre_topc(C_306,B_305)
      | v2_struct_0(C_306)
      | ~ l1_pre_topc(B_305)
      | ~ v2_pre_topc(B_305)
      | v2_struct_0(B_305)
      | ~ l1_pre_topc(A_309)
      | ~ v2_pre_topc(A_309)
      | v2_struct_0(A_309) ) ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_837,plain,(
    ! [B_350,B_351,A_352,D_353] :
      ( m1_subset_1('#skF_1'(B_350,B_351,k4_tmap_1(A_352,B_351),D_353,A_352),u1_struct_0(B_350))
      | r2_funct_2(u1_struct_0(B_351),u1_struct_0(A_352),k2_tmap_1(B_350,A_352,D_353,B_351),k4_tmap_1(A_352,B_351))
      | ~ v1_funct_2(k4_tmap_1(A_352,B_351),u1_struct_0(B_351),u1_struct_0(A_352))
      | ~ v1_funct_1(k4_tmap_1(A_352,B_351))
      | ~ m1_subset_1(D_353,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_350),u1_struct_0(A_352))))
      | ~ v1_funct_2(D_353,u1_struct_0(B_350),u1_struct_0(A_352))
      | ~ v1_funct_1(D_353)
      | ~ m1_pre_topc(B_351,B_350)
      | v2_struct_0(B_351)
      | ~ l1_pre_topc(B_350)
      | ~ v2_pre_topc(B_350)
      | v2_struct_0(B_350)
      | ~ m1_pre_topc(B_351,A_352)
      | ~ l1_pre_topc(A_352)
      | ~ v2_pre_topc(A_352)
      | v2_struct_0(A_352) ) ),
    inference(resolution,[status(thm)],[c_28,c_413])).

tff(c_844,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_608,c_837])).

tff(c_848,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_97,c_86,c_350,c_62,c_60,c_58,c_844])).

tff(c_849,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_848])).

tff(c_850,plain,(
    ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_849])).

tff(c_853,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_850])).

tff(c_856,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_853])).

tff(c_858,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_856])).

tff(c_860,plain,(
    v1_funct_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_849])).

tff(c_30,plain,(
    ! [A_70,B_71] :
      ( v1_funct_2(k4_tmap_1(A_70,B_71),u1_struct_0(B_71),u1_struct_0(A_70))
      | ~ m1_pre_topc(B_71,A_70)
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_859,plain,
    ( ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | m1_subset_1('#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_849])).

tff(c_863,plain,(
    ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_859])).

tff(c_866,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_863])).

tff(c_869,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_866])).

tff(c_871,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_869])).

tff(c_873,plain,(
    v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_859])).

tff(c_872,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_859])).

tff(c_874,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_872])).

tff(c_876,plain,
    ( k4_tmap_1('#skF_2','#skF_3') = '#skF_4'
    | ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_874,c_8])).

tff(c_879,plain,
    ( k4_tmap_1('#skF_2','#skF_3') = '#skF_4'
    | ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_860,c_873,c_876])).

tff(c_890,plain,(
    ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_879])).

tff(c_893,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_890])).

tff(c_896,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_893])).

tff(c_898,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_896])).

tff(c_899,plain,(
    k4_tmap_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_879])).

tff(c_54,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_341])).

tff(c_904,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_899,c_54])).

tff(c_910,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_904])).

tff(c_912,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_872])).

tff(c_523,plain,(
    ! [B_312,D_315,E_314,C_313,A_316] :
      ( r2_hidden('#skF_1'(B_312,C_313,E_314,D_315,A_316),u1_struct_0(C_313))
      | r2_funct_2(u1_struct_0(C_313),u1_struct_0(A_316),k2_tmap_1(B_312,A_316,D_315,C_313),E_314)
      | ~ m1_subset_1(E_314,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_313),u1_struct_0(A_316))))
      | ~ v1_funct_2(E_314,u1_struct_0(C_313),u1_struct_0(A_316))
      | ~ v1_funct_1(E_314)
      | ~ m1_subset_1(D_315,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_312),u1_struct_0(A_316))))
      | ~ v1_funct_2(D_315,u1_struct_0(B_312),u1_struct_0(A_316))
      | ~ v1_funct_1(D_315)
      | ~ m1_pre_topc(C_313,B_312)
      | v2_struct_0(C_313)
      | ~ l1_pre_topc(B_312)
      | ~ v2_pre_topc(B_312)
      | v2_struct_0(B_312)
      | ~ l1_pre_topc(A_316)
      | ~ v2_pre_topc(A_316)
      | v2_struct_0(A_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_1058,plain,(
    ! [B_369,B_370,A_371,D_372] :
      ( r2_hidden('#skF_1'(B_369,B_370,k4_tmap_1(A_371,B_370),D_372,A_371),u1_struct_0(B_370))
      | r2_funct_2(u1_struct_0(B_370),u1_struct_0(A_371),k2_tmap_1(B_369,A_371,D_372,B_370),k4_tmap_1(A_371,B_370))
      | ~ v1_funct_2(k4_tmap_1(A_371,B_370),u1_struct_0(B_370),u1_struct_0(A_371))
      | ~ v1_funct_1(k4_tmap_1(A_371,B_370))
      | ~ m1_subset_1(D_372,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_369),u1_struct_0(A_371))))
      | ~ v1_funct_2(D_372,u1_struct_0(B_369),u1_struct_0(A_371))
      | ~ v1_funct_1(D_372)
      | ~ m1_pre_topc(B_370,B_369)
      | v2_struct_0(B_370)
      | ~ l1_pre_topc(B_369)
      | ~ v2_pre_topc(B_369)
      | v2_struct_0(B_369)
      | ~ m1_pre_topc(B_370,A_371)
      | ~ l1_pre_topc(A_371)
      | ~ v2_pre_topc(A_371)
      | v2_struct_0(A_371) ) ),
    inference(resolution,[status(thm)],[c_28,c_523])).

tff(c_1063,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_608,c_1058])).

tff(c_1066,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_97,c_86,c_350,c_62,c_60,c_58,c_860,c_873,c_1063])).

tff(c_1067,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_912,c_1066])).

tff(c_103,plain,(
    ! [B_197,A_198] :
      ( m1_subset_1(u1_struct_0(B_197),k1_zfmisc_1(u1_struct_0(A_198)))
      | ~ m1_pre_topc(B_197,A_198)
      | ~ l1_pre_topc(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( m1_subset_1(A_1,C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_106,plain,(
    ! [A_1,A_198,B_197] :
      ( m1_subset_1(A_1,u1_struct_0(A_198))
      | ~ r2_hidden(A_1,u1_struct_0(B_197))
      | ~ m1_pre_topc(B_197,A_198)
      | ~ l1_pre_topc(A_198) ) ),
    inference(resolution,[status(thm)],[c_103,c_2])).

tff(c_1078,plain,(
    ! [A_198] :
      ( m1_subset_1('#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2'),u1_struct_0(A_198))
      | ~ m1_pre_topc('#skF_3',A_198)
      | ~ l1_pre_topc(A_198) ) ),
    inference(resolution,[status(thm)],[c_1067,c_106])).

tff(c_56,plain,(
    ! [D_185] :
      ( k1_funct_1('#skF_4',D_185) = D_185
      | ~ r2_hidden(D_185,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(D_185,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_341])).

tff(c_1079,plain,
    ( k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2')) = '#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1067,c_56])).

tff(c_1194,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1079])).

tff(c_1197,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1078,c_1194])).

tff(c_1201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_1197])).

tff(c_1202,plain,(
    k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2')) = '#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1079])).

tff(c_911,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_872])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6,D_7] :
      ( k3_funct_2(A_4,B_5,C_6,D_7) = k1_funct_1(C_6,D_7)
      | ~ m1_subset_1(D_7,A_4)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(A_4,B_5)))
      | ~ v1_funct_2(C_6,A_4,B_5)
      | ~ v1_funct_1(C_6)
      | v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_917,plain,(
    ! [B_5,C_6] :
      ( k3_funct_2(u1_struct_0('#skF_3'),B_5,C_6,'#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2')) = k1_funct_1(C_6,'#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2'))
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),B_5)))
      | ~ v1_funct_2(C_6,u1_struct_0('#skF_3'),B_5)
      | ~ v1_funct_1(C_6)
      | v1_xboole_0(u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_911,c_4])).

tff(c_918,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_917])).

tff(c_16,plain,(
    ! [A_19] :
      ( ~ v1_xboole_0(u1_struct_0(A_19))
      | ~ l1_struct_0(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_921,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_918,c_16])).

tff(c_924,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_921])).

tff(c_926,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_924])).

tff(c_930,plain,(
    ! [B_364,C_365] :
      ( k3_funct_2(u1_struct_0('#skF_3'),B_364,C_365,'#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2')) = k1_funct_1(C_365,'#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2'))
      | ~ m1_subset_1(C_365,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),B_364)))
      | ~ v1_funct_2(C_365,u1_struct_0('#skF_3'),B_364)
      | ~ v1_funct_1(C_365) ) ),
    inference(splitRight,[status(thm)],[c_917])).

tff(c_941,plain,
    ( k3_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2')) = k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2'))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_930])).

tff(c_948,plain,(
    k3_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2')) = k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_941])).

tff(c_42,plain,(
    ! [B_115,E_143,A_83,D_139,C_131] :
      ( k3_funct_2(u1_struct_0(B_115),u1_struct_0(A_83),D_139,'#skF_1'(B_115,C_131,E_143,D_139,A_83)) != k1_funct_1(E_143,'#skF_1'(B_115,C_131,E_143,D_139,A_83))
      | r2_funct_2(u1_struct_0(C_131),u1_struct_0(A_83),k2_tmap_1(B_115,A_83,D_139,C_131),E_143)
      | ~ m1_subset_1(E_143,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_131),u1_struct_0(A_83))))
      | ~ v1_funct_2(E_143,u1_struct_0(C_131),u1_struct_0(A_83))
      | ~ v1_funct_1(E_143)
      | ~ m1_subset_1(D_139,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_115),u1_struct_0(A_83))))
      | ~ v1_funct_2(D_139,u1_struct_0(B_115),u1_struct_0(A_83))
      | ~ v1_funct_1(D_139)
      | ~ m1_pre_topc(C_131,B_115)
      | v2_struct_0(C_131)
      | ~ l1_pre_topc(B_115)
      | ~ v2_pre_topc(B_115)
      | v2_struct_0(B_115)
      | ~ l1_pre_topc(A_83)
      | ~ v2_pre_topc(A_83)
      | v2_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_951,plain,
    ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2')) != k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),k4_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_948,c_42])).

tff(c_955,plain,
    ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2')) != k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_97,c_86,c_350,c_62,c_60,c_58,c_860,c_873,c_608,c_951])).

tff(c_956,plain,
    ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2')) != k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2'))
    | ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_912,c_955])).

tff(c_958,plain,(
    ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_956])).

tff(c_961,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_958])).

tff(c_964,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_961])).

tff(c_966,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_964])).

tff(c_967,plain,(
    k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2')) != k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_956])).

tff(c_1207,plain,(
    k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2')) != '#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1202,c_967])).

tff(c_1203,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1079])).

tff(c_52,plain,(
    ! [A_167,B_171,C_173] :
      ( k1_funct_1(k4_tmap_1(A_167,B_171),C_173) = C_173
      | ~ r2_hidden(C_173,u1_struct_0(B_171))
      | ~ m1_subset_1(C_173,u1_struct_0(A_167))
      | ~ m1_pre_topc(B_171,A_167)
      | v2_struct_0(B_171)
      | ~ l1_pre_topc(A_167)
      | ~ v2_pre_topc(A_167)
      | v2_struct_0(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_311])).

tff(c_1069,plain,(
    ! [A_167] :
      ( k1_funct_1(k4_tmap_1(A_167,'#skF_3'),'#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2')) = '#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2')
      | ~ m1_subset_1('#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2'),u1_struct_0(A_167))
      | ~ m1_pre_topc('#skF_3',A_167)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_167)
      | ~ v2_pre_topc(A_167)
      | v2_struct_0(A_167) ) ),
    inference(resolution,[status(thm)],[c_1067,c_52])).

tff(c_1359,plain,(
    ! [A_392] :
      ( k1_funct_1(k4_tmap_1(A_392,'#skF_3'),'#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2')) = '#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2')
      | ~ m1_subset_1('#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2'),u1_struct_0(A_392))
      | ~ m1_pre_topc('#skF_3',A_392)
      | ~ l1_pre_topc(A_392)
      | ~ v2_pre_topc(A_392)
      | v2_struct_0(A_392) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1069])).

tff(c_1362,plain,
    ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2')) = '#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1203,c_1359])).

tff(c_1373,plain,
    ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2')) = '#skF_1'('#skF_3','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_1362])).

tff(c_1375,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1207,c_1373])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:24:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.81/1.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.81/1.86  
% 4.81/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.81/1.86  %$ r2_funct_2 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_tmap_1 > k2_partfun1 > k4_tmap_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.81/1.86  
% 4.81/1.86  %Foreground sorts:
% 4.81/1.86  
% 4.81/1.86  
% 4.81/1.86  %Background operators:
% 4.81/1.86  
% 4.81/1.86  
% 4.81/1.86  %Foreground operators:
% 4.81/1.86  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.81/1.86  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.81/1.86  tff(k4_tmap_1, type, k4_tmap_1: ($i * $i) > $i).
% 4.81/1.86  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.81/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.81/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.81/1.86  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.81/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.81/1.86  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.81/1.86  tff('#skF_2', type, '#skF_2': $i).
% 4.81/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.81/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.81/1.86  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.81/1.86  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.81/1.86  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 4.81/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.81/1.86  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.81/1.86  tff('#skF_4', type, '#skF_4': $i).
% 4.81/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.81/1.86  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.81/1.86  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 4.81/1.86  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.81/1.86  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 4.81/1.86  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.81/1.86  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.81/1.86  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 4.81/1.86  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 4.81/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.81/1.86  
% 5.10/1.88  tff(f_341, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, u1_struct_0(B)) => (D = k1_funct_1(C, D))))) => r2_funct_2(u1_struct_0(B), u1_struct_0(A), k4_tmap_1(A, B), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_tmap_1)).
% 5.10/1.88  tff(f_60, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 5.10/1.88  tff(f_180, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_funct_1(k4_tmap_1(A, B)) & v1_funct_2(k4_tmap_1(A, B), u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(k4_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_tmap_1)).
% 5.10/1.88  tff(f_69, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 5.10/1.88  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.10/1.88  tff(f_191, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 5.10/1.88  tff(f_147, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 5.10/1.88  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.10/1.88  tff(f_165, axiom, (![A, B, C, D]: ((((((l1_struct_0(A) & l1_struct_0(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & l1_struct_0(D)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 5.10/1.88  tff(f_115, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 5.10/1.88  tff(f_279, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), D, k3_tmap_1(A, B, C, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tmap_1)).
% 5.10/1.88  tff(f_249, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(A))))) => ((![F]: (m1_subset_1(F, u1_struct_0(B)) => (r2_hidden(F, u1_struct_0(C)) => (k3_funct_2(u1_struct_0(B), u1_struct_0(A), D, F) = k1_funct_1(E, F))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(A), k2_tmap_1(B, A, D, C), E)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_tmap_1)).
% 5.10/1.88  tff(f_187, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 5.10/1.88  tff(f_31, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 5.10/1.88  tff(f_44, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 5.10/1.88  tff(f_88, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 5.10/1.88  tff(f_311, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, u1_struct_0(B)) => (k1_funct_1(k4_tmap_1(A, B), C) = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_tmap_1)).
% 5.10/1.88  tff(c_72, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_341])).
% 5.10/1.88  tff(c_68, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_341])).
% 5.10/1.88  tff(c_64, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_341])).
% 5.10/1.88  tff(c_66, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_341])).
% 5.10/1.88  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_341])).
% 5.10/1.88  tff(c_60, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_341])).
% 5.10/1.88  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_341])).
% 5.10/1.88  tff(c_125, plain, (![A_209, B_210, D_211]: (r2_funct_2(A_209, B_210, D_211, D_211) | ~m1_subset_1(D_211, k1_zfmisc_1(k2_zfmisc_1(A_209, B_210))) | ~v1_funct_2(D_211, A_209, B_210) | ~v1_funct_1(D_211))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.10/1.88  tff(c_127, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_125])).
% 5.10/1.88  tff(c_130, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_127])).
% 5.10/1.88  tff(c_70, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_341])).
% 5.10/1.88  tff(c_28, plain, (![A_70, B_71]: (m1_subset_1(k4_tmap_1(A_70, B_71), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_71), u1_struct_0(A_70)))) | ~m1_pre_topc(B_71, A_70) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_180])).
% 5.10/1.88  tff(c_32, plain, (![A_70, B_71]: (v1_funct_1(k4_tmap_1(A_70, B_71)) | ~m1_pre_topc(B_71, A_70) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_180])).
% 5.10/1.88  tff(c_87, plain, (![B_191, A_192]: (v2_pre_topc(B_191) | ~m1_pre_topc(B_191, A_192) | ~l1_pre_topc(A_192) | ~v2_pre_topc(A_192))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.10/1.88  tff(c_93, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_64, c_87])).
% 5.10/1.88  tff(c_97, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_93])).
% 5.10/1.88  tff(c_76, plain, (![B_189, A_190]: (l1_pre_topc(B_189) | ~m1_pre_topc(B_189, A_190) | ~l1_pre_topc(A_190))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.10/1.88  tff(c_82, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_64, c_76])).
% 5.10/1.88  tff(c_86, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_82])).
% 5.10/1.88  tff(c_36, plain, (![A_75]: (m1_pre_topc(A_75, A_75) | ~l1_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.10/1.88  tff(c_317, plain, (![D_296, C_299, B_297, E_298, A_295]: (k3_tmap_1(A_295, B_297, C_299, D_296, E_298)=k2_partfun1(u1_struct_0(C_299), u1_struct_0(B_297), E_298, u1_struct_0(D_296)) | ~m1_pre_topc(D_296, C_299) | ~m1_subset_1(E_298, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_299), u1_struct_0(B_297)))) | ~v1_funct_2(E_298, u1_struct_0(C_299), u1_struct_0(B_297)) | ~v1_funct_1(E_298) | ~m1_pre_topc(D_296, A_295) | ~m1_pre_topc(C_299, A_295) | ~l1_pre_topc(B_297) | ~v2_pre_topc(B_297) | v2_struct_0(B_297) | ~l1_pre_topc(A_295) | ~v2_pre_topc(A_295) | v2_struct_0(A_295))), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.10/1.88  tff(c_323, plain, (![A_295, D_296]: (k3_tmap_1(A_295, '#skF_2', '#skF_3', D_296, '#skF_4')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_296)) | ~m1_pre_topc(D_296, '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc(D_296, A_295) | ~m1_pre_topc('#skF_3', A_295) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_295) | ~v2_pre_topc(A_295) | v2_struct_0(A_295))), inference(resolution, [status(thm)], [c_58, c_317])).
% 5.10/1.88  tff(c_328, plain, (![A_295, D_296]: (k3_tmap_1(A_295, '#skF_2', '#skF_3', D_296, '#skF_4')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_296)) | ~m1_pre_topc(D_296, '#skF_3') | ~m1_pre_topc(D_296, A_295) | ~m1_pre_topc('#skF_3', A_295) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_295) | ~v2_pre_topc(A_295) | v2_struct_0(A_295))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_62, c_60, c_323])).
% 5.10/1.88  tff(c_331, plain, (![A_302, D_303]: (k3_tmap_1(A_302, '#skF_2', '#skF_3', D_303, '#skF_4')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_303)) | ~m1_pre_topc(D_303, '#skF_3') | ~m1_pre_topc(D_303, A_302) | ~m1_pre_topc('#skF_3', A_302) | ~l1_pre_topc(A_302) | ~v2_pre_topc(A_302) | v2_struct_0(A_302))), inference(negUnitSimplification, [status(thm)], [c_72, c_328])).
% 5.10/1.88  tff(c_335, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_2', '#skF_3', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_64, c_331])).
% 5.10/1.88  tff(c_339, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_2', '#skF_3', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_335])).
% 5.10/1.88  tff(c_340, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_2', '#skF_3', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_72, c_339])).
% 5.10/1.88  tff(c_341, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_340])).
% 5.10/1.88  tff(c_344, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_341])).
% 5.10/1.88  tff(c_348, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_344])).
% 5.10/1.88  tff(c_350, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_340])).
% 5.10/1.88  tff(c_12, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.10/1.88  tff(c_175, plain, (![A_235, B_236, C_237, D_238]: (v1_funct_1(k2_tmap_1(A_235, B_236, C_237, D_238)) | ~l1_struct_0(D_238) | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_235), u1_struct_0(B_236)))) | ~v1_funct_2(C_237, u1_struct_0(A_235), u1_struct_0(B_236)) | ~v1_funct_1(C_237) | ~l1_struct_0(B_236) | ~l1_struct_0(A_235))), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.10/1.88  tff(c_179, plain, (![D_238]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_238)) | ~l1_struct_0(D_238) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_58, c_175])).
% 5.10/1.88  tff(c_183, plain, (![D_238]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_238)) | ~l1_struct_0(D_238) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_179])).
% 5.10/1.88  tff(c_184, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_183])).
% 5.10/1.88  tff(c_187, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_12, c_184])).
% 5.10/1.88  tff(c_191, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_187])).
% 5.10/1.88  tff(c_193, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_183])).
% 5.10/1.88  tff(c_192, plain, (![D_238]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_238)) | ~l1_struct_0(D_238))), inference(splitRight, [status(thm)], [c_183])).
% 5.10/1.88  tff(c_195, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_192])).
% 5.10/1.88  tff(c_198, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_195])).
% 5.10/1.88  tff(c_202, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_198])).
% 5.10/1.88  tff(c_204, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_192])).
% 5.10/1.88  tff(c_213, plain, (![A_244, B_245, C_246, D_247]: (v1_funct_2(k2_tmap_1(A_244, B_245, C_246, D_247), u1_struct_0(D_247), u1_struct_0(B_245)) | ~l1_struct_0(D_247) | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_244), u1_struct_0(B_245)))) | ~v1_funct_2(C_246, u1_struct_0(A_244), u1_struct_0(B_245)) | ~v1_funct_1(C_246) | ~l1_struct_0(B_245) | ~l1_struct_0(A_244))), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.10/1.88  tff(c_217, plain, (![D_247]: (v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_247), u1_struct_0(D_247), u1_struct_0('#skF_2')) | ~l1_struct_0(D_247) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_58, c_213])).
% 5.10/1.88  tff(c_221, plain, (![D_247]: (v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_247), u1_struct_0(D_247), u1_struct_0('#skF_2')) | ~l1_struct_0(D_247))), inference(demodulation, [status(thm), theory('equality')], [c_193, c_204, c_62, c_60, c_217])).
% 5.10/1.88  tff(c_203, plain, (![D_238]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_238)) | ~l1_struct_0(D_238))), inference(splitRight, [status(thm)], [c_192])).
% 5.10/1.88  tff(c_349, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_2', '#skF_3', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_340])).
% 5.10/1.88  tff(c_251, plain, (![A_266, B_267, C_268, D_269]: (k2_partfun1(u1_struct_0(A_266), u1_struct_0(B_267), C_268, u1_struct_0(D_269))=k2_tmap_1(A_266, B_267, C_268, D_269) | ~m1_pre_topc(D_269, A_266) | ~m1_subset_1(C_268, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_266), u1_struct_0(B_267)))) | ~v1_funct_2(C_268, u1_struct_0(A_266), u1_struct_0(B_267)) | ~v1_funct_1(C_268) | ~l1_pre_topc(B_267) | ~v2_pre_topc(B_267) | v2_struct_0(B_267) | ~l1_pre_topc(A_266) | ~v2_pre_topc(A_266) | v2_struct_0(A_266))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.10/1.88  tff(c_257, plain, (![D_269]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_269))=k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_269) | ~m1_pre_topc(D_269, '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_58, c_251])).
% 5.10/1.88  tff(c_262, plain, (![D_269]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_269))=k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_269) | ~m1_pre_topc(D_269, '#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_86, c_70, c_68, c_62, c_60, c_257])).
% 5.10/1.88  tff(c_263, plain, (![D_269]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_269))=k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_269) | ~m1_pre_topc(D_269, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_66, c_72, c_262])).
% 5.10/1.88  tff(c_384, plain, (k3_tmap_1('#skF_2', '#skF_2', '#skF_3', '#skF_3', '#skF_4')=k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_349, c_263])).
% 5.10/1.88  tff(c_391, plain, (k3_tmap_1('#skF_2', '#skF_2', '#skF_3', '#skF_3', '#skF_4')=k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_350, c_384])).
% 5.10/1.88  tff(c_395, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0('#skF_3'))=k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_391, c_349])).
% 5.10/1.88  tff(c_329, plain, (![A_295, D_296]: (k3_tmap_1(A_295, '#skF_2', '#skF_3', D_296, '#skF_4')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_296)) | ~m1_pre_topc(D_296, '#skF_3') | ~m1_pre_topc(D_296, A_295) | ~m1_pre_topc('#skF_3', A_295) | ~l1_pre_topc(A_295) | ~v2_pre_topc(A_295) | v2_struct_0(A_295))), inference(negUnitSimplification, [status(thm)], [c_72, c_328])).
% 5.10/1.88  tff(c_352, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_350, c_329])).
% 5.10/1.88  tff(c_365, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_86, c_350, c_352])).
% 5.10/1.88  tff(c_366, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_66, c_365])).
% 5.10/1.88  tff(c_447, plain, (k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_3', '#skF_4')=k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_395, c_366])).
% 5.10/1.88  tff(c_275, plain, (![C_278, B_279, D_280, A_281]: (r2_funct_2(u1_struct_0(C_278), u1_struct_0(B_279), D_280, k3_tmap_1(A_281, B_279, C_278, C_278, D_280)) | ~m1_subset_1(D_280, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_278), u1_struct_0(B_279)))) | ~v1_funct_2(D_280, u1_struct_0(C_278), u1_struct_0(B_279)) | ~v1_funct_1(D_280) | ~m1_pre_topc(C_278, A_281) | v2_struct_0(C_278) | ~l1_pre_topc(B_279) | ~v2_pre_topc(B_279) | v2_struct_0(B_279) | ~l1_pre_topc(A_281) | ~v2_pre_topc(A_281) | v2_struct_0(A_281))), inference(cnfTransformation, [status(thm)], [f_279])).
% 5.10/1.88  tff(c_281, plain, (![A_281]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k3_tmap_1(A_281, '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', A_281) | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_281) | ~v2_pre_topc(A_281) | v2_struct_0(A_281))), inference(resolution, [status(thm)], [c_58, c_275])).
% 5.10/1.88  tff(c_286, plain, (![A_281]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k3_tmap_1(A_281, '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_3', A_281) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_281) | ~v2_pre_topc(A_281) | v2_struct_0(A_281))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_62, c_60, c_281])).
% 5.10/1.88  tff(c_288, plain, (![A_282]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k3_tmap_1(A_282, '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_3', A_282) | ~l1_pre_topc(A_282) | ~v2_pre_topc(A_282) | v2_struct_0(A_282))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_286])).
% 5.10/1.88  tff(c_8, plain, (![D_11, C_10, A_8, B_9]: (D_11=C_10 | ~r2_funct_2(A_8, B_9, C_10, D_11) | ~m1_subset_1(D_11, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))) | ~v1_funct_2(D_11, A_8, B_9) | ~v1_funct_1(D_11) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))) | ~v1_funct_2(C_10, A_8, B_9) | ~v1_funct_1(C_10))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.10/1.88  tff(c_290, plain, (![A_282]: (k3_tmap_1(A_282, '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~m1_subset_1(k3_tmap_1(A_282, '#skF_2', '#skF_3', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1(A_282, '#skF_2', '#skF_3', '#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_282, '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', A_282) | ~l1_pre_topc(A_282) | ~v2_pre_topc(A_282) | v2_struct_0(A_282))), inference(resolution, [status(thm)], [c_288, c_8])).
% 5.10/1.88  tff(c_293, plain, (![A_282]: (k3_tmap_1(A_282, '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~m1_subset_1(k3_tmap_1(A_282, '#skF_2', '#skF_3', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1(A_282, '#skF_2', '#skF_3', '#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_282, '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_3', A_282) | ~l1_pre_topc(A_282) | ~v2_pre_topc(A_282) | v2_struct_0(A_282))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_290])).
% 5.10/1.88  tff(c_451, plain, (k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_447, c_293])).
% 5.10/1.88  tff(c_458, plain, (k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')='#skF_4' | ~m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_86, c_350, c_447, c_447, c_447, c_451])).
% 5.10/1.88  tff(c_459, plain, (k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')='#skF_4' | ~m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_66, c_458])).
% 5.10/1.88  tff(c_464, plain, (~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_459])).
% 5.10/1.88  tff(c_467, plain, (~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_203, c_464])).
% 5.10/1.88  tff(c_471, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_193, c_467])).
% 5.10/1.88  tff(c_473, plain, (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_459])).
% 5.10/1.88  tff(c_22, plain, (![A_66, B_67, C_68, D_69]: (m1_subset_1(k2_tmap_1(A_66, B_67, C_68, D_69), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_69), u1_struct_0(B_67)))) | ~l1_struct_0(D_69) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_66), u1_struct_0(B_67)))) | ~v1_funct_2(C_68, u1_struct_0(A_66), u1_struct_0(B_67)) | ~v1_funct_1(C_68) | ~l1_struct_0(B_67) | ~l1_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.10/1.88  tff(c_472, plain, (~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_459])).
% 5.10/1.88  tff(c_536, plain, (~m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_472])).
% 5.10/1.88  tff(c_539, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_22, c_536])).
% 5.10/1.88  tff(c_543, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_193, c_204, c_62, c_60, c_58, c_539])).
% 5.10/1.88  tff(c_545, plain, (m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_472])).
% 5.10/1.88  tff(c_399, plain, (k3_tmap_1('#skF_2', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_2', '#skF_2', '#skF_3', '#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_2', '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_391, c_293])).
% 5.10/1.88  tff(c_406, plain, (k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')='#skF_4' | ~m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_391, c_391, c_391, c_399])).
% 5.10/1.88  tff(c_407, plain, (k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')='#skF_4' | ~m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_72, c_406])).
% 5.10/1.88  tff(c_599, plain, (k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')='#skF_4' | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_473, c_545, c_407])).
% 5.10/1.88  tff(c_600, plain, (~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_599])).
% 5.10/1.88  tff(c_603, plain, (~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_221, c_600])).
% 5.10/1.88  tff(c_607, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_193, c_603])).
% 5.10/1.88  tff(c_608, plain, (k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_599])).
% 5.10/1.88  tff(c_413, plain, (![D_308, C_306, B_305, E_307, A_309]: (m1_subset_1('#skF_1'(B_305, C_306, E_307, D_308, A_309), u1_struct_0(B_305)) | r2_funct_2(u1_struct_0(C_306), u1_struct_0(A_309), k2_tmap_1(B_305, A_309, D_308, C_306), E_307) | ~m1_subset_1(E_307, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_306), u1_struct_0(A_309)))) | ~v1_funct_2(E_307, u1_struct_0(C_306), u1_struct_0(A_309)) | ~v1_funct_1(E_307) | ~m1_subset_1(D_308, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_305), u1_struct_0(A_309)))) | ~v1_funct_2(D_308, u1_struct_0(B_305), u1_struct_0(A_309)) | ~v1_funct_1(D_308) | ~m1_pre_topc(C_306, B_305) | v2_struct_0(C_306) | ~l1_pre_topc(B_305) | ~v2_pre_topc(B_305) | v2_struct_0(B_305) | ~l1_pre_topc(A_309) | ~v2_pre_topc(A_309) | v2_struct_0(A_309))), inference(cnfTransformation, [status(thm)], [f_249])).
% 5.10/1.88  tff(c_837, plain, (![B_350, B_351, A_352, D_353]: (m1_subset_1('#skF_1'(B_350, B_351, k4_tmap_1(A_352, B_351), D_353, A_352), u1_struct_0(B_350)) | r2_funct_2(u1_struct_0(B_351), u1_struct_0(A_352), k2_tmap_1(B_350, A_352, D_353, B_351), k4_tmap_1(A_352, B_351)) | ~v1_funct_2(k4_tmap_1(A_352, B_351), u1_struct_0(B_351), u1_struct_0(A_352)) | ~v1_funct_1(k4_tmap_1(A_352, B_351)) | ~m1_subset_1(D_353, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_350), u1_struct_0(A_352)))) | ~v1_funct_2(D_353, u1_struct_0(B_350), u1_struct_0(A_352)) | ~v1_funct_1(D_353) | ~m1_pre_topc(B_351, B_350) | v2_struct_0(B_351) | ~l1_pre_topc(B_350) | ~v2_pre_topc(B_350) | v2_struct_0(B_350) | ~m1_pre_topc(B_351, A_352) | ~l1_pre_topc(A_352) | ~v2_pre_topc(A_352) | v2_struct_0(A_352))), inference(resolution, [status(thm)], [c_28, c_413])).
% 5.10/1.88  tff(c_844, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_608, c_837])).
% 5.10/1.88  tff(c_848, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_97, c_86, c_350, c_62, c_60, c_58, c_844])).
% 5.10/1.88  tff(c_849, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_848])).
% 5.10/1.88  tff(c_850, plain, (~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_849])).
% 5.10/1.88  tff(c_853, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_850])).
% 5.10/1.88  tff(c_856, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_853])).
% 5.10/1.88  tff(c_858, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_856])).
% 5.10/1.88  tff(c_860, plain, (v1_funct_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_849])).
% 5.10/1.88  tff(c_30, plain, (![A_70, B_71]: (v1_funct_2(k4_tmap_1(A_70, B_71), u1_struct_0(B_71), u1_struct_0(A_70)) | ~m1_pre_topc(B_71, A_70) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_180])).
% 5.10/1.88  tff(c_859, plain, (~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | m1_subset_1('#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_849])).
% 5.10/1.88  tff(c_863, plain, (~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_859])).
% 5.10/1.88  tff(c_866, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_863])).
% 5.10/1.88  tff(c_869, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_866])).
% 5.10/1.88  tff(c_871, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_869])).
% 5.10/1.88  tff(c_873, plain, (v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_859])).
% 5.10/1.88  tff(c_872, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_859])).
% 5.10/1.88  tff(c_874, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_872])).
% 5.10/1.88  tff(c_876, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4' | ~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_874, c_8])).
% 5.10/1.88  tff(c_879, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4' | ~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_860, c_873, c_876])).
% 5.10/1.88  tff(c_890, plain, (~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_879])).
% 5.10/1.88  tff(c_893, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_890])).
% 5.10/1.88  tff(c_896, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_893])).
% 5.10/1.88  tff(c_898, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_896])).
% 5.10/1.88  tff(c_899, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_879])).
% 5.10/1.88  tff(c_54, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_341])).
% 5.10/1.88  tff(c_904, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_899, c_54])).
% 5.10/1.88  tff(c_910, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_130, c_904])).
% 5.10/1.88  tff(c_912, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_872])).
% 5.10/1.88  tff(c_523, plain, (![B_312, D_315, E_314, C_313, A_316]: (r2_hidden('#skF_1'(B_312, C_313, E_314, D_315, A_316), u1_struct_0(C_313)) | r2_funct_2(u1_struct_0(C_313), u1_struct_0(A_316), k2_tmap_1(B_312, A_316, D_315, C_313), E_314) | ~m1_subset_1(E_314, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_313), u1_struct_0(A_316)))) | ~v1_funct_2(E_314, u1_struct_0(C_313), u1_struct_0(A_316)) | ~v1_funct_1(E_314) | ~m1_subset_1(D_315, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_312), u1_struct_0(A_316)))) | ~v1_funct_2(D_315, u1_struct_0(B_312), u1_struct_0(A_316)) | ~v1_funct_1(D_315) | ~m1_pre_topc(C_313, B_312) | v2_struct_0(C_313) | ~l1_pre_topc(B_312) | ~v2_pre_topc(B_312) | v2_struct_0(B_312) | ~l1_pre_topc(A_316) | ~v2_pre_topc(A_316) | v2_struct_0(A_316))), inference(cnfTransformation, [status(thm)], [f_249])).
% 5.10/1.89  tff(c_1058, plain, (![B_369, B_370, A_371, D_372]: (r2_hidden('#skF_1'(B_369, B_370, k4_tmap_1(A_371, B_370), D_372, A_371), u1_struct_0(B_370)) | r2_funct_2(u1_struct_0(B_370), u1_struct_0(A_371), k2_tmap_1(B_369, A_371, D_372, B_370), k4_tmap_1(A_371, B_370)) | ~v1_funct_2(k4_tmap_1(A_371, B_370), u1_struct_0(B_370), u1_struct_0(A_371)) | ~v1_funct_1(k4_tmap_1(A_371, B_370)) | ~m1_subset_1(D_372, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_369), u1_struct_0(A_371)))) | ~v1_funct_2(D_372, u1_struct_0(B_369), u1_struct_0(A_371)) | ~v1_funct_1(D_372) | ~m1_pre_topc(B_370, B_369) | v2_struct_0(B_370) | ~l1_pre_topc(B_369) | ~v2_pre_topc(B_369) | v2_struct_0(B_369) | ~m1_pre_topc(B_370, A_371) | ~l1_pre_topc(A_371) | ~v2_pre_topc(A_371) | v2_struct_0(A_371))), inference(resolution, [status(thm)], [c_28, c_523])).
% 5.10/1.89  tff(c_1063, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_608, c_1058])).
% 5.10/1.89  tff(c_1066, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_97, c_86, c_350, c_62, c_60, c_58, c_860, c_873, c_1063])).
% 5.10/1.89  tff(c_1067, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_912, c_1066])).
% 5.10/1.89  tff(c_103, plain, (![B_197, A_198]: (m1_subset_1(u1_struct_0(B_197), k1_zfmisc_1(u1_struct_0(A_198))) | ~m1_pre_topc(B_197, A_198) | ~l1_pre_topc(A_198))), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.10/1.89  tff(c_2, plain, (![A_1, C_3, B_2]: (m1_subset_1(A_1, C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.10/1.89  tff(c_106, plain, (![A_1, A_198, B_197]: (m1_subset_1(A_1, u1_struct_0(A_198)) | ~r2_hidden(A_1, u1_struct_0(B_197)) | ~m1_pre_topc(B_197, A_198) | ~l1_pre_topc(A_198))), inference(resolution, [status(thm)], [c_103, c_2])).
% 5.10/1.89  tff(c_1078, plain, (![A_198]: (m1_subset_1('#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2'), u1_struct_0(A_198)) | ~m1_pre_topc('#skF_3', A_198) | ~l1_pre_topc(A_198))), inference(resolution, [status(thm)], [c_1067, c_106])).
% 5.10/1.89  tff(c_56, plain, (![D_185]: (k1_funct_1('#skF_4', D_185)=D_185 | ~r2_hidden(D_185, u1_struct_0('#skF_3')) | ~m1_subset_1(D_185, u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_341])).
% 5.10/1.89  tff(c_1079, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2'))='#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_1067, c_56])).
% 5.10/1.89  tff(c_1194, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1079])).
% 5.10/1.89  tff(c_1197, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_1078, c_1194])).
% 5.10/1.89  tff(c_1201, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_1197])).
% 5.10/1.89  tff(c_1202, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2'))='#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_1079])).
% 5.10/1.89  tff(c_911, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_872])).
% 5.10/1.89  tff(c_4, plain, (![A_4, B_5, C_6, D_7]: (k3_funct_2(A_4, B_5, C_6, D_7)=k1_funct_1(C_6, D_7) | ~m1_subset_1(D_7, A_4) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1(A_4, B_5))) | ~v1_funct_2(C_6, A_4, B_5) | ~v1_funct_1(C_6) | v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.10/1.89  tff(c_917, plain, (![B_5, C_6]: (k3_funct_2(u1_struct_0('#skF_3'), B_5, C_6, '#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2'))=k1_funct_1(C_6, '#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2')) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), B_5))) | ~v1_funct_2(C_6, u1_struct_0('#skF_3'), B_5) | ~v1_funct_1(C_6) | v1_xboole_0(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_911, c_4])).
% 5.10/1.89  tff(c_918, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_917])).
% 5.10/1.89  tff(c_16, plain, (![A_19]: (~v1_xboole_0(u1_struct_0(A_19)) | ~l1_struct_0(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.10/1.89  tff(c_921, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_918, c_16])).
% 5.10/1.89  tff(c_924, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_193, c_921])).
% 5.10/1.89  tff(c_926, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_924])).
% 5.10/1.89  tff(c_930, plain, (![B_364, C_365]: (k3_funct_2(u1_struct_0('#skF_3'), B_364, C_365, '#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2'))=k1_funct_1(C_365, '#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2')) | ~m1_subset_1(C_365, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), B_364))) | ~v1_funct_2(C_365, u1_struct_0('#skF_3'), B_364) | ~v1_funct_1(C_365))), inference(splitRight, [status(thm)], [c_917])).
% 5.10/1.89  tff(c_941, plain, (k3_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2'))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_930])).
% 5.10/1.89  tff(c_948, plain, (k3_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2'))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_941])).
% 5.10/1.89  tff(c_42, plain, (![B_115, E_143, A_83, D_139, C_131]: (k3_funct_2(u1_struct_0(B_115), u1_struct_0(A_83), D_139, '#skF_1'(B_115, C_131, E_143, D_139, A_83))!=k1_funct_1(E_143, '#skF_1'(B_115, C_131, E_143, D_139, A_83)) | r2_funct_2(u1_struct_0(C_131), u1_struct_0(A_83), k2_tmap_1(B_115, A_83, D_139, C_131), E_143) | ~m1_subset_1(E_143, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_131), u1_struct_0(A_83)))) | ~v1_funct_2(E_143, u1_struct_0(C_131), u1_struct_0(A_83)) | ~v1_funct_1(E_143) | ~m1_subset_1(D_139, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_115), u1_struct_0(A_83)))) | ~v1_funct_2(D_139, u1_struct_0(B_115), u1_struct_0(A_83)) | ~v1_funct_1(D_139) | ~m1_pre_topc(C_131, B_115) | v2_struct_0(C_131) | ~l1_pre_topc(B_115) | ~v2_pre_topc(B_115) | v2_struct_0(B_115) | ~l1_pre_topc(A_83) | ~v2_pre_topc(A_83) | v2_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_249])).
% 5.10/1.89  tff(c_951, plain, (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2'))!=k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_948, c_42])).
% 5.10/1.89  tff(c_955, plain, (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2'))!=k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_97, c_86, c_350, c_62, c_60, c_58, c_860, c_873, c_608, c_951])).
% 5.10/1.89  tff(c_956, plain, (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2'))!=k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2')) | ~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_912, c_955])).
% 5.10/1.89  tff(c_958, plain, (~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_956])).
% 5.10/1.89  tff(c_961, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_958])).
% 5.10/1.89  tff(c_964, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_961])).
% 5.10/1.89  tff(c_966, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_964])).
% 5.10/1.89  tff(c_967, plain, (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2'))!=k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2'))), inference(splitRight, [status(thm)], [c_956])).
% 5.10/1.89  tff(c_1207, plain, (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2'))!='#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1202, c_967])).
% 5.10/1.89  tff(c_1203, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_1079])).
% 5.10/1.89  tff(c_52, plain, (![A_167, B_171, C_173]: (k1_funct_1(k4_tmap_1(A_167, B_171), C_173)=C_173 | ~r2_hidden(C_173, u1_struct_0(B_171)) | ~m1_subset_1(C_173, u1_struct_0(A_167)) | ~m1_pre_topc(B_171, A_167) | v2_struct_0(B_171) | ~l1_pre_topc(A_167) | ~v2_pre_topc(A_167) | v2_struct_0(A_167))), inference(cnfTransformation, [status(thm)], [f_311])).
% 5.10/1.89  tff(c_1069, plain, (![A_167]: (k1_funct_1(k4_tmap_1(A_167, '#skF_3'), '#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2'))='#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2'), u1_struct_0(A_167)) | ~m1_pre_topc('#skF_3', A_167) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_167) | ~v2_pre_topc(A_167) | v2_struct_0(A_167))), inference(resolution, [status(thm)], [c_1067, c_52])).
% 5.10/1.89  tff(c_1359, plain, (![A_392]: (k1_funct_1(k4_tmap_1(A_392, '#skF_3'), '#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2'))='#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2'), u1_struct_0(A_392)) | ~m1_pre_topc('#skF_3', A_392) | ~l1_pre_topc(A_392) | ~v2_pre_topc(A_392) | v2_struct_0(A_392))), inference(negUnitSimplification, [status(thm)], [c_66, c_1069])).
% 5.10/1.89  tff(c_1362, plain, (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2'))='#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_1203, c_1359])).
% 5.10/1.89  tff(c_1373, plain, (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2'))='#skF_1'('#skF_3', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_1362])).
% 5.10/1.89  tff(c_1375, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_1207, c_1373])).
% 5.10/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.10/1.89  
% 5.10/1.89  Inference rules
% 5.10/1.89  ----------------------
% 5.10/1.89  #Ref     : 0
% 5.10/1.89  #Sup     : 246
% 5.10/1.89  #Fact    : 0
% 5.10/1.89  #Define  : 0
% 5.10/1.89  #Split   : 17
% 5.10/1.89  #Chain   : 0
% 5.10/1.89  #Close   : 0
% 5.10/1.89  
% 5.10/1.89  Ordering : KBO
% 5.10/1.89  
% 5.10/1.89  Simplification rules
% 5.10/1.89  ----------------------
% 5.10/1.89  #Subsume      : 29
% 5.10/1.89  #Demod        : 634
% 5.10/1.89  #Tautology    : 101
% 5.10/1.89  #SimpNegUnit  : 70
% 5.10/1.89  #BackRed      : 13
% 5.10/1.89  
% 5.10/1.89  #Partial instantiations: 0
% 5.10/1.89  #Strategies tried      : 1
% 5.10/1.89  
% 5.10/1.89  Timing (in seconds)
% 5.10/1.89  ----------------------
% 5.10/1.89  Preprocessing        : 0.42
% 5.10/1.89  Parsing              : 0.22
% 5.10/1.89  CNF conversion       : 0.04
% 5.10/1.89  Main loop            : 0.66
% 5.10/1.89  Inferencing          : 0.23
% 5.10/1.89  Reduction            : 0.22
% 5.10/1.89  Demodulation         : 0.17
% 5.10/1.89  BG Simplification    : 0.04
% 5.10/1.89  Subsumption          : 0.14
% 5.10/1.89  Abstraction          : 0.04
% 5.10/1.89  MUC search           : 0.00
% 5.10/1.89  Cooper               : 0.00
% 5.10/1.89  Total                : 1.14
% 5.10/1.89  Index Insertion      : 0.00
% 5.10/1.89  Index Deletion       : 0.00
% 5.10/1.89  Index Matching       : 0.00
% 5.10/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
