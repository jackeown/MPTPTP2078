%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:46 EST 2020

% Result     : Theorem 6.71s
% Output     : CNFRefutation 6.95s
% Verified   : 
% Statistics : Number of formulae       :  207 (18611 expanded)
%              Number of leaves         :   45 (7260 expanded)
%              Depth                    :   34
%              Number of atoms          :  852 (118271 expanded)
%              Number of equality atoms :   59 (9774 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_tmap_1 > k2_partfun1 > k4_tmap_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_345,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_tmap_1)).

tff(f_198,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_funct_1(k4_tmap_1(A,B))
        & v1_funct_2(k4_tmap_1(A,B),u1_struct_0(B),u1_struct_0(A))
        & m1_subset_1(k4_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_tmap_1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_209,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_153,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

tff(f_121,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_183,axiom,(
    ! [A,B,C,D,E] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & m1_pre_topc(C,A)
        & m1_pre_topc(D,A)
        & v1_funct_1(E)
        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
     => ( v1_funct_1(k3_tmap_1(A,B,C,D,E))
        & v1_funct_2(k3_tmap_1(A,B,C,D,E),u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(k3_tmap_1(A,B,C,D,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).

tff(f_283,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tmap_1)).

tff(f_253,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_tmap_1)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_94,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_205,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_315,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_tmap_1)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_345])).

tff(c_68,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_345])).

tff(c_66,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_345])).

tff(c_62,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_345])).

tff(c_30,plain,(
    ! [A_73,B_74] :
      ( m1_subset_1(k4_tmap_1(A_73,B_74),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_74),u1_struct_0(A_73))))
      | ~ m1_pre_topc(B_74,A_73)
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_345])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_345])).

tff(c_58,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_345])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_345])).

tff(c_133,plain,(
    ! [A_207,B_208,D_209] :
      ( r2_funct_2(A_207,B_208,D_209,D_209)
      | ~ m1_subset_1(D_209,k1_zfmisc_1(k2_zfmisc_1(A_207,B_208)))
      | ~ v1_funct_2(D_209,A_207,B_208)
      | ~ v1_funct_1(D_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_135,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_133])).

tff(c_138,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_135])).

tff(c_34,plain,(
    ! [A_73,B_74] :
      ( v1_funct_1(k4_tmap_1(A_73,B_74))
      | ~ m1_pre_topc(B_74,A_73)
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_86,plain,(
    ! [B_189,A_190] :
      ( v2_pre_topc(B_189)
      | ~ m1_pre_topc(B_189,A_190)
      | ~ l1_pre_topc(A_190)
      | ~ v2_pre_topc(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_92,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_86])).

tff(c_96,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_92])).

tff(c_74,plain,(
    ! [B_185,A_186] :
      ( l1_pre_topc(B_185)
      | ~ m1_pre_topc(B_185,A_186)
      | ~ l1_pre_topc(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_80,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_74])).

tff(c_84,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_80])).

tff(c_38,plain,(
    ! [A_78] :
      ( m1_pre_topc(A_78,A_78)
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_412,plain,(
    ! [A_303,E_301,C_302,D_305,B_304] :
      ( k3_tmap_1(A_303,B_304,C_302,D_305,E_301) = k2_partfun1(u1_struct_0(C_302),u1_struct_0(B_304),E_301,u1_struct_0(D_305))
      | ~ m1_pre_topc(D_305,C_302)
      | ~ m1_subset_1(E_301,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_302),u1_struct_0(B_304))))
      | ~ v1_funct_2(E_301,u1_struct_0(C_302),u1_struct_0(B_304))
      | ~ v1_funct_1(E_301)
      | ~ m1_pre_topc(D_305,A_303)
      | ~ m1_pre_topc(C_302,A_303)
      | ~ l1_pre_topc(B_304)
      | ~ v2_pre_topc(B_304)
      | v2_struct_0(B_304)
      | ~ l1_pre_topc(A_303)
      | ~ v2_pre_topc(A_303)
      | v2_struct_0(A_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_418,plain,(
    ! [A_303,D_305] :
      ( k3_tmap_1(A_303,'#skF_2','#skF_3',D_305,'#skF_4') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_305))
      | ~ m1_pre_topc(D_305,'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc(D_305,A_303)
      | ~ m1_pre_topc('#skF_3',A_303)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_303)
      | ~ v2_pre_topc(A_303)
      | v2_struct_0(A_303) ) ),
    inference(resolution,[status(thm)],[c_56,c_412])).

tff(c_423,plain,(
    ! [A_303,D_305] :
      ( k3_tmap_1(A_303,'#skF_2','#skF_3',D_305,'#skF_4') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_305))
      | ~ m1_pre_topc(D_305,'#skF_3')
      | ~ m1_pre_topc(D_305,A_303)
      | ~ m1_pre_topc('#skF_3',A_303)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_303)
      | ~ v2_pre_topc(A_303)
      | v2_struct_0(A_303) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_60,c_58,c_418])).

tff(c_425,plain,(
    ! [A_306,D_307] :
      ( k3_tmap_1(A_306,'#skF_2','#skF_3',D_307,'#skF_4') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_307))
      | ~ m1_pre_topc(D_307,'#skF_3')
      | ~ m1_pre_topc(D_307,A_306)
      | ~ m1_pre_topc('#skF_3',A_306)
      | ~ l1_pre_topc(A_306)
      | ~ v2_pre_topc(A_306)
      | v2_struct_0(A_306) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_423])).

tff(c_431,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_2','#skF_3','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_425])).

tff(c_439,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_2','#skF_3','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_62,c_431])).

tff(c_440,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_2','#skF_3','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_439])).

tff(c_441,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_440])).

tff(c_444,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_441])).

tff(c_448,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_444])).

tff(c_450,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_440])).

tff(c_449,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_2','#skF_3','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_440])).

tff(c_329,plain,(
    ! [A_268,B_269,C_270,D_271] :
      ( k2_partfun1(u1_struct_0(A_268),u1_struct_0(B_269),C_270,u1_struct_0(D_271)) = k2_tmap_1(A_268,B_269,C_270,D_271)
      | ~ m1_pre_topc(D_271,A_268)
      | ~ m1_subset_1(C_270,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_268),u1_struct_0(B_269))))
      | ~ v1_funct_2(C_270,u1_struct_0(A_268),u1_struct_0(B_269))
      | ~ v1_funct_1(C_270)
      | ~ l1_pre_topc(B_269)
      | ~ v2_pre_topc(B_269)
      | v2_struct_0(B_269)
      | ~ l1_pre_topc(A_268)
      | ~ v2_pre_topc(A_268)
      | v2_struct_0(A_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_333,plain,(
    ! [D_271] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_271)) = k2_tmap_1('#skF_3','#skF_2','#skF_4',D_271)
      | ~ m1_pre_topc(D_271,'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_56,c_329])).

tff(c_337,plain,(
    ! [D_271] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_271)) = k2_tmap_1('#skF_3','#skF_2','#skF_4',D_271)
      | ~ m1_pre_topc(D_271,'#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_84,c_68,c_66,c_60,c_58,c_333])).

tff(c_338,plain,(
    ! [D_271] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_271)) = k2_tmap_1('#skF_3','#skF_2','#skF_4',D_271)
      | ~ m1_pre_topc(D_271,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_70,c_337])).

tff(c_482,plain,
    ( k3_tmap_1('#skF_2','#skF_2','#skF_3','#skF_3','#skF_4') = k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_449,c_338])).

tff(c_489,plain,(
    k3_tmap_1('#skF_2','#skF_2','#skF_3','#skF_3','#skF_4') = k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_450,c_482])).

tff(c_24,plain,(
    ! [E_72,C_70,B_69,D_71,A_68] :
      ( m1_subset_1(k3_tmap_1(A_68,B_69,C_70,D_71,E_72),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_71),u1_struct_0(B_69))))
      | ~ m1_subset_1(E_72,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_70),u1_struct_0(B_69))))
      | ~ v1_funct_2(E_72,u1_struct_0(C_70),u1_struct_0(B_69))
      | ~ v1_funct_1(E_72)
      | ~ m1_pre_topc(D_71,A_68)
      | ~ m1_pre_topc(C_70,A_68)
      | ~ l1_pre_topc(B_69)
      | ~ v2_pre_topc(B_69)
      | v2_struct_0(B_69)
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_497,plain,
    ( m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_489,c_24])).

tff(c_510,plain,
    ( m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_68,c_66,c_62,c_62,c_60,c_58,c_56,c_497])).

tff(c_511,plain,(
    m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_510])).

tff(c_314,plain,(
    ! [D_257,B_259,A_261,E_260,C_258] :
      ( v1_funct_1(k3_tmap_1(A_261,B_259,C_258,D_257,E_260))
      | ~ m1_subset_1(E_260,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_258),u1_struct_0(B_259))))
      | ~ v1_funct_2(E_260,u1_struct_0(C_258),u1_struct_0(B_259))
      | ~ v1_funct_1(E_260)
      | ~ m1_pre_topc(D_257,A_261)
      | ~ m1_pre_topc(C_258,A_261)
      | ~ l1_pre_topc(B_259)
      | ~ v2_pre_topc(B_259)
      | v2_struct_0(B_259)
      | ~ l1_pre_topc(A_261)
      | ~ v2_pre_topc(A_261)
      | v2_struct_0(A_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_318,plain,(
    ! [A_261,D_257] :
      ( v1_funct_1(k3_tmap_1(A_261,'#skF_2','#skF_3',D_257,'#skF_4'))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc(D_257,A_261)
      | ~ m1_pre_topc('#skF_3',A_261)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_261)
      | ~ v2_pre_topc(A_261)
      | v2_struct_0(A_261) ) ),
    inference(resolution,[status(thm)],[c_56,c_314])).

tff(c_322,plain,(
    ! [A_261,D_257] :
      ( v1_funct_1(k3_tmap_1(A_261,'#skF_2','#skF_3',D_257,'#skF_4'))
      | ~ m1_pre_topc(D_257,A_261)
      | ~ m1_pre_topc('#skF_3',A_261)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_261)
      | ~ v2_pre_topc(A_261)
      | v2_struct_0(A_261) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_60,c_58,c_318])).

tff(c_323,plain,(
    ! [A_261,D_257] :
      ( v1_funct_1(k3_tmap_1(A_261,'#skF_2','#skF_3',D_257,'#skF_4'))
      | ~ m1_pre_topc(D_257,A_261)
      | ~ m1_pre_topc('#skF_3',A_261)
      | ~ l1_pre_topc(A_261)
      | ~ v2_pre_topc(A_261)
      | v2_struct_0(A_261) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_322])).

tff(c_506,plain,
    ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_489,c_323])).

tff(c_519,plain,
    ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_62,c_62,c_506])).

tff(c_520,plain,(
    v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_519])).

tff(c_365,plain,(
    ! [E_285,A_286,D_282,C_283,B_284] :
      ( v1_funct_2(k3_tmap_1(A_286,B_284,C_283,D_282,E_285),u1_struct_0(D_282),u1_struct_0(B_284))
      | ~ m1_subset_1(E_285,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_283),u1_struct_0(B_284))))
      | ~ v1_funct_2(E_285,u1_struct_0(C_283),u1_struct_0(B_284))
      | ~ v1_funct_1(E_285)
      | ~ m1_pre_topc(D_282,A_286)
      | ~ m1_pre_topc(C_283,A_286)
      | ~ l1_pre_topc(B_284)
      | ~ v2_pre_topc(B_284)
      | v2_struct_0(B_284)
      | ~ l1_pre_topc(A_286)
      | ~ v2_pre_topc(A_286)
      | v2_struct_0(A_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_369,plain,(
    ! [A_286,D_282] :
      ( v1_funct_2(k3_tmap_1(A_286,'#skF_2','#skF_3',D_282,'#skF_4'),u1_struct_0(D_282),u1_struct_0('#skF_2'))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc(D_282,A_286)
      | ~ m1_pre_topc('#skF_3',A_286)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_286)
      | ~ v2_pre_topc(A_286)
      | v2_struct_0(A_286) ) ),
    inference(resolution,[status(thm)],[c_56,c_365])).

tff(c_373,plain,(
    ! [A_286,D_282] :
      ( v1_funct_2(k3_tmap_1(A_286,'#skF_2','#skF_3',D_282,'#skF_4'),u1_struct_0(D_282),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_282,A_286)
      | ~ m1_pre_topc('#skF_3',A_286)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_286)
      | ~ v2_pre_topc(A_286)
      | v2_struct_0(A_286) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_60,c_58,c_369])).

tff(c_374,plain,(
    ! [A_286,D_282] :
      ( v1_funct_2(k3_tmap_1(A_286,'#skF_2','#skF_3',D_282,'#skF_4'),u1_struct_0(D_282),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_282,A_286)
      | ~ m1_pre_topc('#skF_3',A_286)
      | ~ l1_pre_topc(A_286)
      | ~ v2_pre_topc(A_286)
      | v2_struct_0(A_286) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_373])).

tff(c_500,plain,
    ( v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_489,c_374])).

tff(c_513,plain,
    ( v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_62,c_62,c_500])).

tff(c_514,plain,(
    v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_513])).

tff(c_349,plain,(
    ! [C_277,B_278,D_279,A_280] :
      ( r2_funct_2(u1_struct_0(C_277),u1_struct_0(B_278),D_279,k3_tmap_1(A_280,B_278,C_277,C_277,D_279))
      | ~ m1_subset_1(D_279,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_277),u1_struct_0(B_278))))
      | ~ v1_funct_2(D_279,u1_struct_0(C_277),u1_struct_0(B_278))
      | ~ v1_funct_1(D_279)
      | ~ m1_pre_topc(C_277,A_280)
      | v2_struct_0(C_277)
      | ~ l1_pre_topc(B_278)
      | ~ v2_pre_topc(B_278)
      | v2_struct_0(B_278)
      | ~ l1_pre_topc(A_280)
      | ~ v2_pre_topc(A_280)
      | v2_struct_0(A_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_353,plain,(
    ! [A_280] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k3_tmap_1(A_280,'#skF_2','#skF_3','#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc('#skF_3',A_280)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_280)
      | ~ v2_pre_topc(A_280)
      | v2_struct_0(A_280) ) ),
    inference(resolution,[status(thm)],[c_56,c_349])).

tff(c_357,plain,(
    ! [A_280] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k3_tmap_1(A_280,'#skF_2','#skF_3','#skF_3','#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_280)
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_280)
      | ~ v2_pre_topc(A_280)
      | v2_struct_0(A_280) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_60,c_58,c_353])).

tff(c_358,plain,(
    ! [A_280] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k3_tmap_1(A_280,'#skF_2','#skF_3','#skF_3','#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_280)
      | ~ l1_pre_topc(A_280)
      | ~ v2_pre_topc(A_280)
      | v2_struct_0(A_280) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_357])).

tff(c_503,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_489,c_358])).

tff(c_516,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_62,c_503])).

tff(c_517,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_516])).

tff(c_10,plain,(
    ! [D_13,C_12,A_10,B_11] :
      ( D_13 = C_12
      | ~ r2_funct_2(A_10,B_11,C_12,D_13)
      | ~ m1_subset_1(D_13,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11)))
      | ~ v1_funct_2(D_13,A_10,B_11)
      | ~ v1_funct_1(D_13)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11)))
      | ~ v1_funct_2(C_12,A_10,B_11)
      | ~ v1_funct_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_537,plain,
    ( k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_517,c_10])).

tff(c_540,plain,
    ( k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_520,c_514,c_537])).

tff(c_646,plain,(
    k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_511,c_540])).

tff(c_665,plain,(
    ! [A_315,D_317,B_318,C_314,E_316] :
      ( r2_hidden('#skF_1'(C_314,A_315,E_316,D_317,B_318),u1_struct_0(C_314))
      | r2_funct_2(u1_struct_0(C_314),u1_struct_0(A_315),k2_tmap_1(B_318,A_315,D_317,C_314),E_316)
      | ~ m1_subset_1(E_316,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_314),u1_struct_0(A_315))))
      | ~ v1_funct_2(E_316,u1_struct_0(C_314),u1_struct_0(A_315))
      | ~ v1_funct_1(E_316)
      | ~ m1_subset_1(D_317,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_318),u1_struct_0(A_315))))
      | ~ v1_funct_2(D_317,u1_struct_0(B_318),u1_struct_0(A_315))
      | ~ v1_funct_1(D_317)
      | ~ m1_pre_topc(C_314,B_318)
      | v2_struct_0(C_314)
      | ~ l1_pre_topc(B_318)
      | ~ v2_pre_topc(B_318)
      | v2_struct_0(B_318)
      | ~ l1_pre_topc(A_315)
      | ~ v2_pre_topc(A_315)
      | v2_struct_0(A_315) ) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_1798,plain,(
    ! [B_437,A_438,D_439,B_440] :
      ( r2_hidden('#skF_1'(B_437,A_438,k4_tmap_1(A_438,B_437),D_439,B_440),u1_struct_0(B_437))
      | r2_funct_2(u1_struct_0(B_437),u1_struct_0(A_438),k2_tmap_1(B_440,A_438,D_439,B_437),k4_tmap_1(A_438,B_437))
      | ~ v1_funct_2(k4_tmap_1(A_438,B_437),u1_struct_0(B_437),u1_struct_0(A_438))
      | ~ v1_funct_1(k4_tmap_1(A_438,B_437))
      | ~ m1_subset_1(D_439,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_440),u1_struct_0(A_438))))
      | ~ v1_funct_2(D_439,u1_struct_0(B_440),u1_struct_0(A_438))
      | ~ v1_funct_1(D_439)
      | ~ m1_pre_topc(B_437,B_440)
      | v2_struct_0(B_437)
      | ~ l1_pre_topc(B_440)
      | ~ v2_pre_topc(B_440)
      | v2_struct_0(B_440)
      | ~ m1_pre_topc(B_437,A_438)
      | ~ l1_pre_topc(A_438)
      | ~ v2_pre_topc(A_438)
      | v2_struct_0(A_438) ) ),
    inference(resolution,[status(thm)],[c_30,c_665])).

tff(c_1803,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_3'),u1_struct_0('#skF_3'))
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
    inference(superposition,[status(thm),theory(equality)],[c_646,c_1798])).

tff(c_1806,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_3'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_62,c_96,c_84,c_450,c_60,c_58,c_56,c_1803])).

tff(c_1807,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_3'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_1806])).

tff(c_1808,plain,(
    ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1807])).

tff(c_1811,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_1808])).

tff(c_1814,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_62,c_1811])).

tff(c_1816,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1814])).

tff(c_1818,plain,(
    v1_funct_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1807])).

tff(c_32,plain,(
    ! [A_73,B_74] :
      ( v1_funct_2(k4_tmap_1(A_73,B_74),u1_struct_0(B_74),u1_struct_0(A_73))
      | ~ m1_pre_topc(B_74,A_73)
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_1817,plain,
    ( ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | r2_hidden('#skF_1'('#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_3'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1807])).

tff(c_1837,plain,(
    ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1817])).

tff(c_1840,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_1837])).

tff(c_1843,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_62,c_1840])).

tff(c_1845,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1843])).

tff(c_1847,plain,(
    v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1817])).

tff(c_1846,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_3'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1817])).

tff(c_1848,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1846])).

tff(c_1850,plain,
    ( k4_tmap_1('#skF_2','#skF_3') = '#skF_4'
    | ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1848,c_10])).

tff(c_1853,plain,
    ( k4_tmap_1('#skF_2','#skF_3') = '#skF_4'
    | ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_1818,c_1847,c_1850])).

tff(c_1877,plain,(
    ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_1853])).

tff(c_1880,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_1877])).

tff(c_1883,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_62,c_1880])).

tff(c_1885,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1883])).

tff(c_1886,plain,(
    k4_tmap_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1853])).

tff(c_52,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_345])).

tff(c_1891,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1886,c_52])).

tff(c_1897,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_1891])).

tff(c_1899,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1846])).

tff(c_14,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_102,plain,(
    ! [D_195] :
      ( k1_funct_1('#skF_4',D_195) = D_195
      | ~ r2_hidden(D_195,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(D_195,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_345])).

tff(c_107,plain,(
    ! [A_1] :
      ( k1_funct_1('#skF_4',A_1) = A_1
      | ~ m1_subset_1(A_1,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_1,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2,c_102])).

tff(c_139,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_18,plain,(
    ! [A_21] :
      ( ~ v1_xboole_0(u1_struct_0(A_21))
      | ~ l1_struct_0(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_142,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_139,c_18])).

tff(c_145,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_142])).

tff(c_148,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_145])).

tff(c_152,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_148])).

tff(c_154,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_522,plain,(
    ! [B_312,D_311,C_308,E_310,A_309] :
      ( m1_subset_1('#skF_1'(C_308,A_309,E_310,D_311,B_312),u1_struct_0(B_312))
      | r2_funct_2(u1_struct_0(C_308),u1_struct_0(A_309),k2_tmap_1(B_312,A_309,D_311,C_308),E_310)
      | ~ m1_subset_1(E_310,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_308),u1_struct_0(A_309))))
      | ~ v1_funct_2(E_310,u1_struct_0(C_308),u1_struct_0(A_309))
      | ~ v1_funct_1(E_310)
      | ~ m1_subset_1(D_311,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_312),u1_struct_0(A_309))))
      | ~ v1_funct_2(D_311,u1_struct_0(B_312),u1_struct_0(A_309))
      | ~ v1_funct_1(D_311)
      | ~ m1_pre_topc(C_308,B_312)
      | v2_struct_0(C_308)
      | ~ l1_pre_topc(B_312)
      | ~ v2_pre_topc(B_312)
      | v2_struct_0(B_312)
      | ~ l1_pre_topc(A_309)
      | ~ v2_pre_topc(A_309)
      | v2_struct_0(A_309) ) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_1960,plain,(
    ! [B_450,A_451,D_452,B_453] :
      ( m1_subset_1('#skF_1'(B_450,A_451,k4_tmap_1(A_451,B_450),D_452,B_453),u1_struct_0(B_453))
      | r2_funct_2(u1_struct_0(B_450),u1_struct_0(A_451),k2_tmap_1(B_453,A_451,D_452,B_450),k4_tmap_1(A_451,B_450))
      | ~ v1_funct_2(k4_tmap_1(A_451,B_450),u1_struct_0(B_450),u1_struct_0(A_451))
      | ~ v1_funct_1(k4_tmap_1(A_451,B_450))
      | ~ m1_subset_1(D_452,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_453),u1_struct_0(A_451))))
      | ~ v1_funct_2(D_452,u1_struct_0(B_453),u1_struct_0(A_451))
      | ~ v1_funct_1(D_452)
      | ~ m1_pre_topc(B_450,B_453)
      | v2_struct_0(B_450)
      | ~ l1_pre_topc(B_453)
      | ~ v2_pre_topc(B_453)
      | v2_struct_0(B_453)
      | ~ m1_pre_topc(B_450,A_451)
      | ~ l1_pre_topc(A_451)
      | ~ v2_pre_topc(A_451)
      | v2_struct_0(A_451) ) ),
    inference(resolution,[status(thm)],[c_30,c_522])).

tff(c_1975,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_3'),u1_struct_0('#skF_3'))
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
    inference(superposition,[status(thm),theory(equality)],[c_646,c_1960])).

tff(c_1981,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_3'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_62,c_96,c_84,c_450,c_60,c_58,c_56,c_1818,c_1847,c_1975])).

tff(c_1982,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_3'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_1899,c_1981])).

tff(c_108,plain,(
    ! [B_196,A_197] :
      ( m1_subset_1(u1_struct_0(B_196),k1_zfmisc_1(u1_struct_0(A_197)))
      | ~ m1_pre_topc(B_196,A_197)
      | ~ l1_pre_topc(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( m1_subset_1(A_3,C_5)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(C_5))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_128,plain,(
    ! [A_204,A_205,B_206] :
      ( m1_subset_1(A_204,u1_struct_0(A_205))
      | ~ r2_hidden(A_204,u1_struct_0(B_206))
      | ~ m1_pre_topc(B_206,A_205)
      | ~ l1_pre_topc(A_205) ) ),
    inference(resolution,[status(thm)],[c_108,c_4])).

tff(c_156,plain,(
    ! [A_211,A_212,B_213] :
      ( m1_subset_1(A_211,u1_struct_0(A_212))
      | ~ m1_pre_topc(B_213,A_212)
      | ~ l1_pre_topc(A_212)
      | v1_xboole_0(u1_struct_0(B_213))
      | ~ m1_subset_1(A_211,u1_struct_0(B_213)) ) ),
    inference(resolution,[status(thm)],[c_2,c_128])).

tff(c_160,plain,(
    ! [A_211] :
      ( m1_subset_1(A_211,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_211,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_62,c_156])).

tff(c_164,plain,(
    ! [A_211] :
      ( m1_subset_1(A_211,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_211,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_160])).

tff(c_165,plain,(
    ! [A_211] :
      ( m1_subset_1(A_211,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(A_211,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_164])).

tff(c_201,plain,(
    ! [A_227,B_228,C_229] :
      ( k1_funct_1(k4_tmap_1(A_227,B_228),C_229) = C_229
      | ~ r2_hidden(C_229,u1_struct_0(B_228))
      | ~ m1_subset_1(C_229,u1_struct_0(A_227))
      | ~ m1_pre_topc(B_228,A_227)
      | v2_struct_0(B_228)
      | ~ l1_pre_topc(A_227)
      | ~ v2_pre_topc(A_227)
      | v2_struct_0(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_206,plain,(
    ! [A_230,B_231,A_232] :
      ( k1_funct_1(k4_tmap_1(A_230,B_231),A_232) = A_232
      | ~ m1_subset_1(A_232,u1_struct_0(A_230))
      | ~ m1_pre_topc(B_231,A_230)
      | v2_struct_0(B_231)
      | ~ l1_pre_topc(A_230)
      | ~ v2_pre_topc(A_230)
      | v2_struct_0(A_230)
      | v1_xboole_0(u1_struct_0(B_231))
      | ~ m1_subset_1(A_232,u1_struct_0(B_231)) ) ),
    inference(resolution,[status(thm)],[c_2,c_201])).

tff(c_208,plain,(
    ! [B_231,A_211] :
      ( k1_funct_1(k4_tmap_1('#skF_2',B_231),A_211) = A_211
      | ~ m1_pre_topc(B_231,'#skF_2')
      | v2_struct_0(B_231)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | v1_xboole_0(u1_struct_0(B_231))
      | ~ m1_subset_1(A_211,u1_struct_0(B_231))
      | ~ m1_subset_1(A_211,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_165,c_206])).

tff(c_211,plain,(
    ! [B_231,A_211] :
      ( k1_funct_1(k4_tmap_1('#skF_2',B_231),A_211) = A_211
      | ~ m1_pre_topc(B_231,'#skF_2')
      | v2_struct_0(B_231)
      | v2_struct_0('#skF_2')
      | v1_xboole_0(u1_struct_0(B_231))
      | ~ m1_subset_1(A_211,u1_struct_0(B_231))
      | ~ m1_subset_1(A_211,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_208])).

tff(c_212,plain,(
    ! [B_231,A_211] :
      ( k1_funct_1(k4_tmap_1('#skF_2',B_231),A_211) = A_211
      | ~ m1_pre_topc(B_231,'#skF_2')
      | v2_struct_0(B_231)
      | v1_xboole_0(u1_struct_0(B_231))
      | ~ m1_subset_1(A_211,u1_struct_0(B_231))
      | ~ m1_subset_1(A_211,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_211])).

tff(c_1987,plain,
    ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_3')) = '#skF_1'('#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_3'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1982,c_212])).

tff(c_1999,plain,
    ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_3')) = '#skF_1'('#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_3')
    | v2_struct_0('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1982,c_62,c_1987])).

tff(c_2000,plain,(
    k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_3')) = '#skF_1'('#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_64,c_1999])).

tff(c_493,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0('#skF_3')) = k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_489,c_449])).

tff(c_424,plain,(
    ! [A_303,D_305] :
      ( k3_tmap_1(A_303,'#skF_2','#skF_3',D_305,'#skF_4') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_305))
      | ~ m1_pre_topc(D_305,'#skF_3')
      | ~ m1_pre_topc(D_305,A_303)
      | ~ m1_pre_topc('#skF_3',A_303)
      | ~ l1_pre_topc(A_303)
      | ~ v2_pre_topc(A_303)
      | v2_struct_0(A_303) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_423])).

tff(c_453,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_450,c_424])).

tff(c_466,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_84,c_450,c_453])).

tff(c_467,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_466])).

tff(c_605,plain,(
    k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_3','#skF_4') = k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_467])).

tff(c_649,plain,(
    k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_646,c_605])).

tff(c_1898,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_3'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1846])).

tff(c_111,plain,(
    ! [A_3,A_197,B_196] :
      ( m1_subset_1(A_3,u1_struct_0(A_197))
      | ~ r2_hidden(A_3,u1_struct_0(B_196))
      | ~ m1_pre_topc(B_196,A_197)
      | ~ l1_pre_topc(A_197) ) ),
    inference(resolution,[status(thm)],[c_108,c_4])).

tff(c_1928,plain,(
    ! [A_449] :
      ( m1_subset_1('#skF_1'('#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_3'),u1_struct_0(A_449))
      | ~ m1_pre_topc('#skF_3',A_449)
      | ~ l1_pre_topc(A_449) ) ),
    inference(resolution,[status(thm)],[c_1898,c_111])).

tff(c_166,plain,(
    ! [A_214] :
      ( m1_subset_1(A_214,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(A_214,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_164])).

tff(c_153,plain,(
    ! [A_1] :
      ( k1_funct_1('#skF_4',A_1) = A_1
      | ~ m1_subset_1(A_1,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(A_1,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_170,plain,(
    ! [A_214] :
      ( k1_funct_1('#skF_4',A_214) = A_214
      | ~ m1_subset_1(A_214,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_166,c_153])).

tff(c_1942,plain,
    ( k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_3')) = '#skF_1'('#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1928,c_170])).

tff(c_1951,plain,(
    k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_3')) = '#skF_1'('#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_450,c_1942])).

tff(c_436,plain,(
    ! [A_78] :
      ( k3_tmap_1(A_78,'#skF_2','#skF_3',A_78,'#skF_4') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(A_78))
      | ~ m1_pre_topc(A_78,'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_78)
      | ~ v2_pre_topc(A_78)
      | v2_struct_0(A_78)
      | ~ l1_pre_topc(A_78) ) ),
    inference(resolution,[status(thm)],[c_38,c_425])).

tff(c_750,plain,(
    ! [A_319] :
      ( k3_tmap_1(A_319,'#skF_2','#skF_3',A_319,'#skF_4') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(A_319))
      | ~ m1_pre_topc(A_319,'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_319)
      | ~ v2_pre_topc(A_319)
      | v2_struct_0(A_319)
      | ~ l1_pre_topc(A_319) ) ),
    inference(resolution,[status(thm)],[c_38,c_425])).

tff(c_762,plain,(
    ! [A_319] :
      ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(A_319)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_319),u1_struct_0('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc(A_319,A_319)
      | ~ m1_pre_topc('#skF_3',A_319)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_319)
      | ~ v2_pre_topc(A_319)
      | v2_struct_0(A_319)
      | ~ m1_pre_topc(A_319,'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_319)
      | ~ v2_pre_topc(A_319)
      | v2_struct_0(A_319)
      | ~ l1_pre_topc(A_319) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_750,c_24])).

tff(c_790,plain,(
    ! [A_319] :
      ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(A_319)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_319),u1_struct_0('#skF_2'))))
      | ~ m1_pre_topc(A_319,A_319)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(A_319,'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_319)
      | ~ v2_pre_topc(A_319)
      | v2_struct_0(A_319)
      | ~ l1_pre_topc(A_319) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_60,c_58,c_56,c_762])).

tff(c_820,plain,(
    ! [A_326] :
      ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(A_326)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_326),u1_struct_0('#skF_2'))))
      | ~ m1_pre_topc(A_326,A_326)
      | ~ m1_pre_topc(A_326,'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_326)
      | ~ v2_pre_topc(A_326)
      | v2_struct_0(A_326)
      | ~ l1_pre_topc(A_326) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_790])).

tff(c_846,plain,(
    ! [A_78] :
      ( m1_subset_1(k3_tmap_1(A_78,'#skF_2','#skF_3',A_78,'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_78),u1_struct_0('#skF_2'))))
      | ~ m1_pre_topc(A_78,A_78)
      | ~ m1_pre_topc(A_78,'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_78)
      | ~ v2_pre_topc(A_78)
      | v2_struct_0(A_78)
      | ~ l1_pre_topc(A_78)
      | ~ m1_pre_topc(A_78,'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_78)
      | ~ v2_pre_topc(A_78)
      | v2_struct_0(A_78)
      | ~ l1_pre_topc(A_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_436,c_820])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8,D_9] :
      ( k3_funct_2(A_6,B_7,C_8,D_9) = k1_funct_1(C_8,D_9)
      | ~ m1_subset_1(D_9,A_6)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7)))
      | ~ v1_funct_2(C_8,A_6,B_7)
      | ~ v1_funct_1(C_8)
      | v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1991,plain,(
    ! [B_7,C_8] :
      ( k3_funct_2(u1_struct_0('#skF_3'),B_7,C_8,'#skF_1'('#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_3')) = k1_funct_1(C_8,'#skF_1'('#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_3'))
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),B_7)))
      | ~ v1_funct_2(C_8,u1_struct_0('#skF_3'),B_7)
      | ~ v1_funct_1(C_8)
      | v1_xboole_0(u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1982,c_6])).

tff(c_2064,plain,(
    ! [B_456,C_457] :
      ( k3_funct_2(u1_struct_0('#skF_3'),B_456,C_457,'#skF_1'('#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_3')) = k1_funct_1(C_457,'#skF_1'('#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_3'))
      | ~ m1_subset_1(C_457,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),B_456)))
      | ~ v1_funct_2(C_457,u1_struct_0('#skF_3'),B_456)
      | ~ v1_funct_1(C_457) ) ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_1991])).

tff(c_2068,plain,
    ( k3_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_3','#skF_4'),'#skF_1'('#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_3')) = k1_funct_1(k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_3','#skF_4'),'#skF_1'('#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_3'))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_3','#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_846,c_2064])).

tff(c_2090,plain,
    ( k3_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_1'('#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_3')) = '#skF_1'('#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_96,c_450,c_60,c_649,c_58,c_649,c_1951,c_649,c_649,c_2068])).

tff(c_2091,plain,(
    k3_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_1'('#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_3')) = '#skF_1'('#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2090])).

tff(c_40,plain,(
    ! [B_111,C_127,D_135,E_139,A_79] :
      ( k3_funct_2(u1_struct_0(B_111),u1_struct_0(A_79),D_135,'#skF_1'(C_127,A_79,E_139,D_135,B_111)) != k1_funct_1(E_139,'#skF_1'(C_127,A_79,E_139,D_135,B_111))
      | r2_funct_2(u1_struct_0(C_127),u1_struct_0(A_79),k2_tmap_1(B_111,A_79,D_135,C_127),E_139)
      | ~ m1_subset_1(E_139,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_127),u1_struct_0(A_79))))
      | ~ v1_funct_2(E_139,u1_struct_0(C_127),u1_struct_0(A_79))
      | ~ v1_funct_1(E_139)
      | ~ m1_subset_1(D_135,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_111),u1_struct_0(A_79))))
      | ~ v1_funct_2(D_135,u1_struct_0(B_111),u1_struct_0(A_79))
      | ~ v1_funct_1(D_135)
      | ~ m1_pre_topc(C_127,B_111)
      | v2_struct_0(C_127)
      | ~ l1_pre_topc(B_111)
      | ~ v2_pre_topc(B_111)
      | v2_struct_0(B_111)
      | ~ l1_pre_topc(A_79)
      | ~ v2_pre_topc(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_2107,plain,
    ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_3')) != '#skF_1'('#skF_3','#skF_2',k4_tmap_1('#skF_2','#skF_3'),'#skF_4','#skF_3')
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
    inference(superposition,[status(thm),theory(equality)],[c_2091,c_40])).

tff(c_2111,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_96,c_84,c_450,c_60,c_58,c_56,c_1818,c_1847,c_646,c_2000,c_2107])).

tff(c_2112,plain,(
    ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_1899,c_2111])).

tff(c_2116,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_2112])).

tff(c_2119,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_62,c_2116])).

tff(c_2121,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2119])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:39:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.71/2.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.95/2.30  
% 6.95/2.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.95/2.30  %$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_tmap_1 > k2_partfun1 > k4_tmap_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.95/2.30  
% 6.95/2.30  %Foreground sorts:
% 6.95/2.30  
% 6.95/2.30  
% 6.95/2.30  %Background operators:
% 6.95/2.30  
% 6.95/2.30  
% 6.95/2.30  %Foreground operators:
% 6.95/2.30  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.95/2.30  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 6.95/2.30  tff(k4_tmap_1, type, k4_tmap_1: ($i * $i) > $i).
% 6.95/2.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.95/2.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.95/2.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.95/2.30  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.95/2.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.95/2.30  tff('#skF_2', type, '#skF_2': $i).
% 6.95/2.30  tff('#skF_3', type, '#skF_3': $i).
% 6.95/2.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.95/2.30  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.95/2.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.95/2.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 6.95/2.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.95/2.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.95/2.30  tff('#skF_4', type, '#skF_4': $i).
% 6.95/2.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.95/2.30  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.95/2.30  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 6.95/2.30  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.95/2.30  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 6.95/2.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.95/2.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.95/2.30  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 6.95/2.30  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 6.95/2.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.95/2.30  
% 6.95/2.33  tff(f_345, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, u1_struct_0(B)) => (D = k1_funct_1(C, D))))) => r2_funct_2(u1_struct_0(B), u1_struct_0(A), k4_tmap_1(A, B), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_tmap_1)).
% 6.95/2.33  tff(f_198, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_funct_1(k4_tmap_1(A, B)) & v1_funct_2(k4_tmap_1(A, B), u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(k4_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_tmap_1)).
% 6.95/2.33  tff(f_66, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 6.95/2.34  tff(f_75, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 6.95/2.34  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 6.95/2.34  tff(f_209, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 6.95/2.34  tff(f_153, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 6.95/2.34  tff(f_121, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 6.95/2.34  tff(f_183, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 6.95/2.34  tff(f_283, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), D, k3_tmap_1(A, B, C, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tmap_1)).
% 6.95/2.34  tff(f_253, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(A))))) => ((![F]: (m1_subset_1(F, u1_struct_0(B)) => (r2_hidden(F, u1_struct_0(C)) => (k3_funct_2(u1_struct_0(B), u1_struct_0(A), D, F) = k1_funct_1(E, F))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(A), k2_tmap_1(B, A, D, C), E)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_tmap_1)).
% 6.95/2.34  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 6.95/2.34  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 6.95/2.34  tff(f_94, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 6.95/2.34  tff(f_205, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 6.95/2.34  tff(f_37, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 6.95/2.34  tff(f_315, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, u1_struct_0(B)) => (k1_funct_1(k4_tmap_1(A, B), C) = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_tmap_1)).
% 6.95/2.34  tff(f_50, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 6.95/2.34  tff(c_70, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_345])).
% 6.95/2.34  tff(c_68, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_345])).
% 6.95/2.34  tff(c_66, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_345])).
% 6.95/2.34  tff(c_62, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_345])).
% 6.95/2.34  tff(c_30, plain, (![A_73, B_74]: (m1_subset_1(k4_tmap_1(A_73, B_74), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_74), u1_struct_0(A_73)))) | ~m1_pre_topc(B_74, A_73) | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_198])).
% 6.95/2.34  tff(c_64, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_345])).
% 6.95/2.34  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_345])).
% 6.95/2.34  tff(c_58, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_345])).
% 6.95/2.34  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_345])).
% 6.95/2.34  tff(c_133, plain, (![A_207, B_208, D_209]: (r2_funct_2(A_207, B_208, D_209, D_209) | ~m1_subset_1(D_209, k1_zfmisc_1(k2_zfmisc_1(A_207, B_208))) | ~v1_funct_2(D_209, A_207, B_208) | ~v1_funct_1(D_209))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.95/2.34  tff(c_135, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_133])).
% 6.95/2.34  tff(c_138, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_135])).
% 6.95/2.34  tff(c_34, plain, (![A_73, B_74]: (v1_funct_1(k4_tmap_1(A_73, B_74)) | ~m1_pre_topc(B_74, A_73) | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_198])).
% 6.95/2.34  tff(c_86, plain, (![B_189, A_190]: (v2_pre_topc(B_189) | ~m1_pre_topc(B_189, A_190) | ~l1_pre_topc(A_190) | ~v2_pre_topc(A_190))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.95/2.34  tff(c_92, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_62, c_86])).
% 6.95/2.34  tff(c_96, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_92])).
% 6.95/2.34  tff(c_74, plain, (![B_185, A_186]: (l1_pre_topc(B_185) | ~m1_pre_topc(B_185, A_186) | ~l1_pre_topc(A_186))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.95/2.34  tff(c_80, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_62, c_74])).
% 6.95/2.34  tff(c_84, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_80])).
% 6.95/2.34  tff(c_38, plain, (![A_78]: (m1_pre_topc(A_78, A_78) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_209])).
% 6.95/2.34  tff(c_412, plain, (![A_303, E_301, C_302, D_305, B_304]: (k3_tmap_1(A_303, B_304, C_302, D_305, E_301)=k2_partfun1(u1_struct_0(C_302), u1_struct_0(B_304), E_301, u1_struct_0(D_305)) | ~m1_pre_topc(D_305, C_302) | ~m1_subset_1(E_301, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_302), u1_struct_0(B_304)))) | ~v1_funct_2(E_301, u1_struct_0(C_302), u1_struct_0(B_304)) | ~v1_funct_1(E_301) | ~m1_pre_topc(D_305, A_303) | ~m1_pre_topc(C_302, A_303) | ~l1_pre_topc(B_304) | ~v2_pre_topc(B_304) | v2_struct_0(B_304) | ~l1_pre_topc(A_303) | ~v2_pre_topc(A_303) | v2_struct_0(A_303))), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.95/2.34  tff(c_418, plain, (![A_303, D_305]: (k3_tmap_1(A_303, '#skF_2', '#skF_3', D_305, '#skF_4')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_305)) | ~m1_pre_topc(D_305, '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc(D_305, A_303) | ~m1_pre_topc('#skF_3', A_303) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_303) | ~v2_pre_topc(A_303) | v2_struct_0(A_303))), inference(resolution, [status(thm)], [c_56, c_412])).
% 6.95/2.34  tff(c_423, plain, (![A_303, D_305]: (k3_tmap_1(A_303, '#skF_2', '#skF_3', D_305, '#skF_4')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_305)) | ~m1_pre_topc(D_305, '#skF_3') | ~m1_pre_topc(D_305, A_303) | ~m1_pre_topc('#skF_3', A_303) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_303) | ~v2_pre_topc(A_303) | v2_struct_0(A_303))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_60, c_58, c_418])).
% 6.95/2.34  tff(c_425, plain, (![A_306, D_307]: (k3_tmap_1(A_306, '#skF_2', '#skF_3', D_307, '#skF_4')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_307)) | ~m1_pre_topc(D_307, '#skF_3') | ~m1_pre_topc(D_307, A_306) | ~m1_pre_topc('#skF_3', A_306) | ~l1_pre_topc(A_306) | ~v2_pre_topc(A_306) | v2_struct_0(A_306))), inference(negUnitSimplification, [status(thm)], [c_70, c_423])).
% 6.95/2.34  tff(c_431, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_2', '#skF_3', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_62, c_425])).
% 6.95/2.34  tff(c_439, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_2', '#skF_3', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_62, c_431])).
% 6.95/2.34  tff(c_440, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_2', '#skF_3', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_70, c_439])).
% 6.95/2.34  tff(c_441, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_440])).
% 6.95/2.34  tff(c_444, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_441])).
% 6.95/2.34  tff(c_448, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_444])).
% 6.95/2.34  tff(c_450, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_440])).
% 6.95/2.34  tff(c_449, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_2', '#skF_3', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_440])).
% 6.95/2.34  tff(c_329, plain, (![A_268, B_269, C_270, D_271]: (k2_partfun1(u1_struct_0(A_268), u1_struct_0(B_269), C_270, u1_struct_0(D_271))=k2_tmap_1(A_268, B_269, C_270, D_271) | ~m1_pre_topc(D_271, A_268) | ~m1_subset_1(C_270, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_268), u1_struct_0(B_269)))) | ~v1_funct_2(C_270, u1_struct_0(A_268), u1_struct_0(B_269)) | ~v1_funct_1(C_270) | ~l1_pre_topc(B_269) | ~v2_pre_topc(B_269) | v2_struct_0(B_269) | ~l1_pre_topc(A_268) | ~v2_pre_topc(A_268) | v2_struct_0(A_268))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.95/2.34  tff(c_333, plain, (![D_271]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_271))=k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_271) | ~m1_pre_topc(D_271, '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_56, c_329])).
% 6.95/2.34  tff(c_337, plain, (![D_271]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_271))=k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_271) | ~m1_pre_topc(D_271, '#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_84, c_68, c_66, c_60, c_58, c_333])).
% 6.95/2.34  tff(c_338, plain, (![D_271]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_271))=k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_271) | ~m1_pre_topc(D_271, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_64, c_70, c_337])).
% 6.95/2.34  tff(c_482, plain, (k3_tmap_1('#skF_2', '#skF_2', '#skF_3', '#skF_3', '#skF_4')=k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_449, c_338])).
% 6.95/2.34  tff(c_489, plain, (k3_tmap_1('#skF_2', '#skF_2', '#skF_3', '#skF_3', '#skF_4')=k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_450, c_482])).
% 6.95/2.34  tff(c_24, plain, (![E_72, C_70, B_69, D_71, A_68]: (m1_subset_1(k3_tmap_1(A_68, B_69, C_70, D_71, E_72), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_71), u1_struct_0(B_69)))) | ~m1_subset_1(E_72, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_70), u1_struct_0(B_69)))) | ~v1_funct_2(E_72, u1_struct_0(C_70), u1_struct_0(B_69)) | ~v1_funct_1(E_72) | ~m1_pre_topc(D_71, A_68) | ~m1_pre_topc(C_70, A_68) | ~l1_pre_topc(B_69) | ~v2_pre_topc(B_69) | v2_struct_0(B_69) | ~l1_pre_topc(A_68) | ~v2_pre_topc(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.95/2.34  tff(c_497, plain, (m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_489, c_24])).
% 6.95/2.34  tff(c_510, plain, (m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_68, c_66, c_62, c_62, c_60, c_58, c_56, c_497])).
% 6.95/2.34  tff(c_511, plain, (m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_70, c_510])).
% 6.95/2.34  tff(c_314, plain, (![D_257, B_259, A_261, E_260, C_258]: (v1_funct_1(k3_tmap_1(A_261, B_259, C_258, D_257, E_260)) | ~m1_subset_1(E_260, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_258), u1_struct_0(B_259)))) | ~v1_funct_2(E_260, u1_struct_0(C_258), u1_struct_0(B_259)) | ~v1_funct_1(E_260) | ~m1_pre_topc(D_257, A_261) | ~m1_pre_topc(C_258, A_261) | ~l1_pre_topc(B_259) | ~v2_pre_topc(B_259) | v2_struct_0(B_259) | ~l1_pre_topc(A_261) | ~v2_pre_topc(A_261) | v2_struct_0(A_261))), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.95/2.34  tff(c_318, plain, (![A_261, D_257]: (v1_funct_1(k3_tmap_1(A_261, '#skF_2', '#skF_3', D_257, '#skF_4')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc(D_257, A_261) | ~m1_pre_topc('#skF_3', A_261) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_261) | ~v2_pre_topc(A_261) | v2_struct_0(A_261))), inference(resolution, [status(thm)], [c_56, c_314])).
% 6.95/2.34  tff(c_322, plain, (![A_261, D_257]: (v1_funct_1(k3_tmap_1(A_261, '#skF_2', '#skF_3', D_257, '#skF_4')) | ~m1_pre_topc(D_257, A_261) | ~m1_pre_topc('#skF_3', A_261) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_261) | ~v2_pre_topc(A_261) | v2_struct_0(A_261))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_60, c_58, c_318])).
% 6.95/2.34  tff(c_323, plain, (![A_261, D_257]: (v1_funct_1(k3_tmap_1(A_261, '#skF_2', '#skF_3', D_257, '#skF_4')) | ~m1_pre_topc(D_257, A_261) | ~m1_pre_topc('#skF_3', A_261) | ~l1_pre_topc(A_261) | ~v2_pre_topc(A_261) | v2_struct_0(A_261))), inference(negUnitSimplification, [status(thm)], [c_70, c_322])).
% 6.95/2.34  tff(c_506, plain, (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_489, c_323])).
% 6.95/2.34  tff(c_519, plain, (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_62, c_62, c_506])).
% 6.95/2.34  tff(c_520, plain, (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_70, c_519])).
% 6.95/2.34  tff(c_365, plain, (![E_285, A_286, D_282, C_283, B_284]: (v1_funct_2(k3_tmap_1(A_286, B_284, C_283, D_282, E_285), u1_struct_0(D_282), u1_struct_0(B_284)) | ~m1_subset_1(E_285, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_283), u1_struct_0(B_284)))) | ~v1_funct_2(E_285, u1_struct_0(C_283), u1_struct_0(B_284)) | ~v1_funct_1(E_285) | ~m1_pre_topc(D_282, A_286) | ~m1_pre_topc(C_283, A_286) | ~l1_pre_topc(B_284) | ~v2_pre_topc(B_284) | v2_struct_0(B_284) | ~l1_pre_topc(A_286) | ~v2_pre_topc(A_286) | v2_struct_0(A_286))), inference(cnfTransformation, [status(thm)], [f_183])).
% 6.95/2.34  tff(c_369, plain, (![A_286, D_282]: (v1_funct_2(k3_tmap_1(A_286, '#skF_2', '#skF_3', D_282, '#skF_4'), u1_struct_0(D_282), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc(D_282, A_286) | ~m1_pre_topc('#skF_3', A_286) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_286) | ~v2_pre_topc(A_286) | v2_struct_0(A_286))), inference(resolution, [status(thm)], [c_56, c_365])).
% 6.95/2.34  tff(c_373, plain, (![A_286, D_282]: (v1_funct_2(k3_tmap_1(A_286, '#skF_2', '#skF_3', D_282, '#skF_4'), u1_struct_0(D_282), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_282, A_286) | ~m1_pre_topc('#skF_3', A_286) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_286) | ~v2_pre_topc(A_286) | v2_struct_0(A_286))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_60, c_58, c_369])).
% 6.95/2.34  tff(c_374, plain, (![A_286, D_282]: (v1_funct_2(k3_tmap_1(A_286, '#skF_2', '#skF_3', D_282, '#skF_4'), u1_struct_0(D_282), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_282, A_286) | ~m1_pre_topc('#skF_3', A_286) | ~l1_pre_topc(A_286) | ~v2_pre_topc(A_286) | v2_struct_0(A_286))), inference(negUnitSimplification, [status(thm)], [c_70, c_373])).
% 6.95/2.34  tff(c_500, plain, (v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_489, c_374])).
% 6.95/2.34  tff(c_513, plain, (v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_62, c_62, c_500])).
% 6.95/2.34  tff(c_514, plain, (v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_70, c_513])).
% 6.95/2.34  tff(c_349, plain, (![C_277, B_278, D_279, A_280]: (r2_funct_2(u1_struct_0(C_277), u1_struct_0(B_278), D_279, k3_tmap_1(A_280, B_278, C_277, C_277, D_279)) | ~m1_subset_1(D_279, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_277), u1_struct_0(B_278)))) | ~v1_funct_2(D_279, u1_struct_0(C_277), u1_struct_0(B_278)) | ~v1_funct_1(D_279) | ~m1_pre_topc(C_277, A_280) | v2_struct_0(C_277) | ~l1_pre_topc(B_278) | ~v2_pre_topc(B_278) | v2_struct_0(B_278) | ~l1_pre_topc(A_280) | ~v2_pre_topc(A_280) | v2_struct_0(A_280))), inference(cnfTransformation, [status(thm)], [f_283])).
% 6.95/2.34  tff(c_353, plain, (![A_280]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k3_tmap_1(A_280, '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', A_280) | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_280) | ~v2_pre_topc(A_280) | v2_struct_0(A_280))), inference(resolution, [status(thm)], [c_56, c_349])).
% 6.95/2.34  tff(c_357, plain, (![A_280]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k3_tmap_1(A_280, '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_3', A_280) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_280) | ~v2_pre_topc(A_280) | v2_struct_0(A_280))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_60, c_58, c_353])).
% 6.95/2.34  tff(c_358, plain, (![A_280]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k3_tmap_1(A_280, '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_3', A_280) | ~l1_pre_topc(A_280) | ~v2_pre_topc(A_280) | v2_struct_0(A_280))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_357])).
% 6.95/2.34  tff(c_503, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_489, c_358])).
% 6.95/2.34  tff(c_516, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_62, c_503])).
% 6.95/2.34  tff(c_517, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_70, c_516])).
% 6.95/2.34  tff(c_10, plain, (![D_13, C_12, A_10, B_11]: (D_13=C_12 | ~r2_funct_2(A_10, B_11, C_12, D_13) | ~m1_subset_1(D_13, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))) | ~v1_funct_2(D_13, A_10, B_11) | ~v1_funct_1(D_13) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))) | ~v1_funct_2(C_12, A_10, B_11) | ~v1_funct_1(C_12))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.95/2.34  tff(c_537, plain, (k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')='#skF_4' | ~m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_517, c_10])).
% 6.95/2.34  tff(c_540, plain, (k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')='#skF_4' | ~m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_520, c_514, c_537])).
% 6.95/2.34  tff(c_646, plain, (k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_511, c_540])).
% 6.95/2.34  tff(c_665, plain, (![A_315, D_317, B_318, C_314, E_316]: (r2_hidden('#skF_1'(C_314, A_315, E_316, D_317, B_318), u1_struct_0(C_314)) | r2_funct_2(u1_struct_0(C_314), u1_struct_0(A_315), k2_tmap_1(B_318, A_315, D_317, C_314), E_316) | ~m1_subset_1(E_316, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_314), u1_struct_0(A_315)))) | ~v1_funct_2(E_316, u1_struct_0(C_314), u1_struct_0(A_315)) | ~v1_funct_1(E_316) | ~m1_subset_1(D_317, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_318), u1_struct_0(A_315)))) | ~v1_funct_2(D_317, u1_struct_0(B_318), u1_struct_0(A_315)) | ~v1_funct_1(D_317) | ~m1_pre_topc(C_314, B_318) | v2_struct_0(C_314) | ~l1_pre_topc(B_318) | ~v2_pre_topc(B_318) | v2_struct_0(B_318) | ~l1_pre_topc(A_315) | ~v2_pre_topc(A_315) | v2_struct_0(A_315))), inference(cnfTransformation, [status(thm)], [f_253])).
% 6.95/2.34  tff(c_1798, plain, (![B_437, A_438, D_439, B_440]: (r2_hidden('#skF_1'(B_437, A_438, k4_tmap_1(A_438, B_437), D_439, B_440), u1_struct_0(B_437)) | r2_funct_2(u1_struct_0(B_437), u1_struct_0(A_438), k2_tmap_1(B_440, A_438, D_439, B_437), k4_tmap_1(A_438, B_437)) | ~v1_funct_2(k4_tmap_1(A_438, B_437), u1_struct_0(B_437), u1_struct_0(A_438)) | ~v1_funct_1(k4_tmap_1(A_438, B_437)) | ~m1_subset_1(D_439, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_440), u1_struct_0(A_438)))) | ~v1_funct_2(D_439, u1_struct_0(B_440), u1_struct_0(A_438)) | ~v1_funct_1(D_439) | ~m1_pre_topc(B_437, B_440) | v2_struct_0(B_437) | ~l1_pre_topc(B_440) | ~v2_pre_topc(B_440) | v2_struct_0(B_440) | ~m1_pre_topc(B_437, A_438) | ~l1_pre_topc(A_438) | ~v2_pre_topc(A_438) | v2_struct_0(A_438))), inference(resolution, [status(thm)], [c_30, c_665])).
% 6.95/2.34  tff(c_1803, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_3'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_646, c_1798])).
% 6.95/2.34  tff(c_1806, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_3'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_62, c_96, c_84, c_450, c_60, c_58, c_56, c_1803])).
% 6.95/2.34  tff(c_1807, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_3'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_1806])).
% 6.95/2.34  tff(c_1808, plain, (~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1807])).
% 6.95/2.34  tff(c_1811, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_1808])).
% 6.95/2.34  tff(c_1814, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_62, c_1811])).
% 6.95/2.34  tff(c_1816, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_1814])).
% 6.95/2.34  tff(c_1818, plain, (v1_funct_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_1807])).
% 6.95/2.34  tff(c_32, plain, (![A_73, B_74]: (v1_funct_2(k4_tmap_1(A_73, B_74), u1_struct_0(B_74), u1_struct_0(A_73)) | ~m1_pre_topc(B_74, A_73) | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_198])).
% 6.95/2.34  tff(c_1817, plain, (~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | r2_hidden('#skF_1'('#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_3'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_1807])).
% 6.95/2.34  tff(c_1837, plain, (~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1817])).
% 6.95/2.34  tff(c_1840, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_1837])).
% 6.95/2.34  tff(c_1843, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_62, c_1840])).
% 6.95/2.34  tff(c_1845, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_1843])).
% 6.95/2.34  tff(c_1847, plain, (v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_1817])).
% 6.95/2.34  tff(c_1846, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_3'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_1817])).
% 6.95/2.34  tff(c_1848, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1846])).
% 6.95/2.34  tff(c_1850, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4' | ~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_1848, c_10])).
% 6.95/2.34  tff(c_1853, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4' | ~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_1818, c_1847, c_1850])).
% 6.95/2.34  tff(c_1877, plain, (~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_1853])).
% 6.95/2.34  tff(c_1880, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_1877])).
% 6.95/2.34  tff(c_1883, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_62, c_1880])).
% 6.95/2.34  tff(c_1885, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_1883])).
% 6.95/2.34  tff(c_1886, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_1853])).
% 6.95/2.34  tff(c_52, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_345])).
% 6.95/2.34  tff(c_1891, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1886, c_52])).
% 6.95/2.34  tff(c_1897, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_138, c_1891])).
% 6.95/2.34  tff(c_1899, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_1846])).
% 6.95/2.34  tff(c_14, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.95/2.34  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.95/2.34  tff(c_102, plain, (![D_195]: (k1_funct_1('#skF_4', D_195)=D_195 | ~r2_hidden(D_195, u1_struct_0('#skF_3')) | ~m1_subset_1(D_195, u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_345])).
% 6.95/2.34  tff(c_107, plain, (![A_1]: (k1_funct_1('#skF_4', A_1)=A_1 | ~m1_subset_1(A_1, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1(A_1, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_2, c_102])).
% 6.95/2.34  tff(c_139, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_107])).
% 6.95/2.34  tff(c_18, plain, (![A_21]: (~v1_xboole_0(u1_struct_0(A_21)) | ~l1_struct_0(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.95/2.34  tff(c_142, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_139, c_18])).
% 6.95/2.34  tff(c_145, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_64, c_142])).
% 6.95/2.34  tff(c_148, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_14, c_145])).
% 6.95/2.34  tff(c_152, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_148])).
% 6.95/2.34  tff(c_154, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_107])).
% 6.95/2.34  tff(c_522, plain, (![B_312, D_311, C_308, E_310, A_309]: (m1_subset_1('#skF_1'(C_308, A_309, E_310, D_311, B_312), u1_struct_0(B_312)) | r2_funct_2(u1_struct_0(C_308), u1_struct_0(A_309), k2_tmap_1(B_312, A_309, D_311, C_308), E_310) | ~m1_subset_1(E_310, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_308), u1_struct_0(A_309)))) | ~v1_funct_2(E_310, u1_struct_0(C_308), u1_struct_0(A_309)) | ~v1_funct_1(E_310) | ~m1_subset_1(D_311, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_312), u1_struct_0(A_309)))) | ~v1_funct_2(D_311, u1_struct_0(B_312), u1_struct_0(A_309)) | ~v1_funct_1(D_311) | ~m1_pre_topc(C_308, B_312) | v2_struct_0(C_308) | ~l1_pre_topc(B_312) | ~v2_pre_topc(B_312) | v2_struct_0(B_312) | ~l1_pre_topc(A_309) | ~v2_pre_topc(A_309) | v2_struct_0(A_309))), inference(cnfTransformation, [status(thm)], [f_253])).
% 6.95/2.34  tff(c_1960, plain, (![B_450, A_451, D_452, B_453]: (m1_subset_1('#skF_1'(B_450, A_451, k4_tmap_1(A_451, B_450), D_452, B_453), u1_struct_0(B_453)) | r2_funct_2(u1_struct_0(B_450), u1_struct_0(A_451), k2_tmap_1(B_453, A_451, D_452, B_450), k4_tmap_1(A_451, B_450)) | ~v1_funct_2(k4_tmap_1(A_451, B_450), u1_struct_0(B_450), u1_struct_0(A_451)) | ~v1_funct_1(k4_tmap_1(A_451, B_450)) | ~m1_subset_1(D_452, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_453), u1_struct_0(A_451)))) | ~v1_funct_2(D_452, u1_struct_0(B_453), u1_struct_0(A_451)) | ~v1_funct_1(D_452) | ~m1_pre_topc(B_450, B_453) | v2_struct_0(B_450) | ~l1_pre_topc(B_453) | ~v2_pre_topc(B_453) | v2_struct_0(B_453) | ~m1_pre_topc(B_450, A_451) | ~l1_pre_topc(A_451) | ~v2_pre_topc(A_451) | v2_struct_0(A_451))), inference(resolution, [status(thm)], [c_30, c_522])).
% 6.95/2.34  tff(c_1975, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_3'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_646, c_1960])).
% 6.95/2.34  tff(c_1981, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_3'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_62, c_96, c_84, c_450, c_60, c_58, c_56, c_1818, c_1847, c_1975])).
% 6.95/2.34  tff(c_1982, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_3'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_1899, c_1981])).
% 6.95/2.34  tff(c_108, plain, (![B_196, A_197]: (m1_subset_1(u1_struct_0(B_196), k1_zfmisc_1(u1_struct_0(A_197))) | ~m1_pre_topc(B_196, A_197) | ~l1_pre_topc(A_197))), inference(cnfTransformation, [status(thm)], [f_205])).
% 6.95/2.34  tff(c_4, plain, (![A_3, C_5, B_4]: (m1_subset_1(A_3, C_5) | ~m1_subset_1(B_4, k1_zfmisc_1(C_5)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.95/2.34  tff(c_128, plain, (![A_204, A_205, B_206]: (m1_subset_1(A_204, u1_struct_0(A_205)) | ~r2_hidden(A_204, u1_struct_0(B_206)) | ~m1_pre_topc(B_206, A_205) | ~l1_pre_topc(A_205))), inference(resolution, [status(thm)], [c_108, c_4])).
% 6.95/2.34  tff(c_156, plain, (![A_211, A_212, B_213]: (m1_subset_1(A_211, u1_struct_0(A_212)) | ~m1_pre_topc(B_213, A_212) | ~l1_pre_topc(A_212) | v1_xboole_0(u1_struct_0(B_213)) | ~m1_subset_1(A_211, u1_struct_0(B_213)))), inference(resolution, [status(thm)], [c_2, c_128])).
% 6.95/2.34  tff(c_160, plain, (![A_211]: (m1_subset_1(A_211, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1(A_211, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_62, c_156])).
% 6.95/2.34  tff(c_164, plain, (![A_211]: (m1_subset_1(A_211, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1(A_211, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_160])).
% 6.95/2.34  tff(c_165, plain, (![A_211]: (m1_subset_1(A_211, u1_struct_0('#skF_2')) | ~m1_subset_1(A_211, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_154, c_164])).
% 6.95/2.34  tff(c_201, plain, (![A_227, B_228, C_229]: (k1_funct_1(k4_tmap_1(A_227, B_228), C_229)=C_229 | ~r2_hidden(C_229, u1_struct_0(B_228)) | ~m1_subset_1(C_229, u1_struct_0(A_227)) | ~m1_pre_topc(B_228, A_227) | v2_struct_0(B_228) | ~l1_pre_topc(A_227) | ~v2_pre_topc(A_227) | v2_struct_0(A_227))), inference(cnfTransformation, [status(thm)], [f_315])).
% 6.95/2.34  tff(c_206, plain, (![A_230, B_231, A_232]: (k1_funct_1(k4_tmap_1(A_230, B_231), A_232)=A_232 | ~m1_subset_1(A_232, u1_struct_0(A_230)) | ~m1_pre_topc(B_231, A_230) | v2_struct_0(B_231) | ~l1_pre_topc(A_230) | ~v2_pre_topc(A_230) | v2_struct_0(A_230) | v1_xboole_0(u1_struct_0(B_231)) | ~m1_subset_1(A_232, u1_struct_0(B_231)))), inference(resolution, [status(thm)], [c_2, c_201])).
% 6.95/2.34  tff(c_208, plain, (![B_231, A_211]: (k1_funct_1(k4_tmap_1('#skF_2', B_231), A_211)=A_211 | ~m1_pre_topc(B_231, '#skF_2') | v2_struct_0(B_231) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v1_xboole_0(u1_struct_0(B_231)) | ~m1_subset_1(A_211, u1_struct_0(B_231)) | ~m1_subset_1(A_211, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_165, c_206])).
% 6.95/2.34  tff(c_211, plain, (![B_231, A_211]: (k1_funct_1(k4_tmap_1('#skF_2', B_231), A_211)=A_211 | ~m1_pre_topc(B_231, '#skF_2') | v2_struct_0(B_231) | v2_struct_0('#skF_2') | v1_xboole_0(u1_struct_0(B_231)) | ~m1_subset_1(A_211, u1_struct_0(B_231)) | ~m1_subset_1(A_211, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_208])).
% 6.95/2.34  tff(c_212, plain, (![B_231, A_211]: (k1_funct_1(k4_tmap_1('#skF_2', B_231), A_211)=A_211 | ~m1_pre_topc(B_231, '#skF_2') | v2_struct_0(B_231) | v1_xboole_0(u1_struct_0(B_231)) | ~m1_subset_1(A_211, u1_struct_0(B_231)) | ~m1_subset_1(A_211, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_70, c_211])).
% 6.95/2.34  tff(c_1987, plain, (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_3'))='#skF_1'('#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_3'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_1982, c_212])).
% 6.95/2.34  tff(c_1999, plain, (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_3'))='#skF_1'('#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_3') | v2_struct_0('#skF_3') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1982, c_62, c_1987])).
% 6.95/2.34  tff(c_2000, plain, (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_3'))='#skF_1'('#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_154, c_64, c_1999])).
% 6.95/2.34  tff(c_493, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0('#skF_3'))=k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_489, c_449])).
% 6.95/2.34  tff(c_424, plain, (![A_303, D_305]: (k3_tmap_1(A_303, '#skF_2', '#skF_3', D_305, '#skF_4')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_305)) | ~m1_pre_topc(D_305, '#skF_3') | ~m1_pre_topc(D_305, A_303) | ~m1_pre_topc('#skF_3', A_303) | ~l1_pre_topc(A_303) | ~v2_pre_topc(A_303) | v2_struct_0(A_303))), inference(negUnitSimplification, [status(thm)], [c_70, c_423])).
% 6.95/2.34  tff(c_453, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_450, c_424])).
% 6.95/2.34  tff(c_466, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_84, c_450, c_453])).
% 6.95/2.34  tff(c_467, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_64, c_466])).
% 6.95/2.34  tff(c_605, plain, (k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_3', '#skF_4')=k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_493, c_467])).
% 6.95/2.34  tff(c_649, plain, (k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_646, c_605])).
% 6.95/2.34  tff(c_1898, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_3'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_1846])).
% 6.95/2.34  tff(c_111, plain, (![A_3, A_197, B_196]: (m1_subset_1(A_3, u1_struct_0(A_197)) | ~r2_hidden(A_3, u1_struct_0(B_196)) | ~m1_pre_topc(B_196, A_197) | ~l1_pre_topc(A_197))), inference(resolution, [status(thm)], [c_108, c_4])).
% 6.95/2.34  tff(c_1928, plain, (![A_449]: (m1_subset_1('#skF_1'('#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_3'), u1_struct_0(A_449)) | ~m1_pre_topc('#skF_3', A_449) | ~l1_pre_topc(A_449))), inference(resolution, [status(thm)], [c_1898, c_111])).
% 6.95/2.34  tff(c_166, plain, (![A_214]: (m1_subset_1(A_214, u1_struct_0('#skF_2')) | ~m1_subset_1(A_214, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_154, c_164])).
% 6.95/2.34  tff(c_153, plain, (![A_1]: (k1_funct_1('#skF_4', A_1)=A_1 | ~m1_subset_1(A_1, u1_struct_0('#skF_2')) | ~m1_subset_1(A_1, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_107])).
% 6.95/2.34  tff(c_170, plain, (![A_214]: (k1_funct_1('#skF_4', A_214)=A_214 | ~m1_subset_1(A_214, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_166, c_153])).
% 6.95/2.34  tff(c_1942, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_3'))='#skF_1'('#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_1928, c_170])).
% 6.95/2.34  tff(c_1951, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_3'))='#skF_1'('#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_450, c_1942])).
% 6.95/2.34  tff(c_436, plain, (![A_78]: (k3_tmap_1(A_78, '#skF_2', '#skF_3', A_78, '#skF_4')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(A_78)) | ~m1_pre_topc(A_78, '#skF_3') | ~m1_pre_topc('#skF_3', A_78) | ~v2_pre_topc(A_78) | v2_struct_0(A_78) | ~l1_pre_topc(A_78))), inference(resolution, [status(thm)], [c_38, c_425])).
% 6.95/2.34  tff(c_750, plain, (![A_319]: (k3_tmap_1(A_319, '#skF_2', '#skF_3', A_319, '#skF_4')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(A_319)) | ~m1_pre_topc(A_319, '#skF_3') | ~m1_pre_topc('#skF_3', A_319) | ~v2_pre_topc(A_319) | v2_struct_0(A_319) | ~l1_pre_topc(A_319))), inference(resolution, [status(thm)], [c_38, c_425])).
% 6.95/2.34  tff(c_762, plain, (![A_319]: (m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(A_319)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_319), u1_struct_0('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc(A_319, A_319) | ~m1_pre_topc('#skF_3', A_319) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_319) | ~v2_pre_topc(A_319) | v2_struct_0(A_319) | ~m1_pre_topc(A_319, '#skF_3') | ~m1_pre_topc('#skF_3', A_319) | ~v2_pre_topc(A_319) | v2_struct_0(A_319) | ~l1_pre_topc(A_319))), inference(superposition, [status(thm), theory('equality')], [c_750, c_24])).
% 6.95/2.34  tff(c_790, plain, (![A_319]: (m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(A_319)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_319), u1_struct_0('#skF_2')))) | ~m1_pre_topc(A_319, A_319) | v2_struct_0('#skF_2') | ~m1_pre_topc(A_319, '#skF_3') | ~m1_pre_topc('#skF_3', A_319) | ~v2_pre_topc(A_319) | v2_struct_0(A_319) | ~l1_pre_topc(A_319))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_60, c_58, c_56, c_762])).
% 6.95/2.34  tff(c_820, plain, (![A_326]: (m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(A_326)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_326), u1_struct_0('#skF_2')))) | ~m1_pre_topc(A_326, A_326) | ~m1_pre_topc(A_326, '#skF_3') | ~m1_pre_topc('#skF_3', A_326) | ~v2_pre_topc(A_326) | v2_struct_0(A_326) | ~l1_pre_topc(A_326))), inference(negUnitSimplification, [status(thm)], [c_70, c_790])).
% 6.95/2.34  tff(c_846, plain, (![A_78]: (m1_subset_1(k3_tmap_1(A_78, '#skF_2', '#skF_3', A_78, '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_78), u1_struct_0('#skF_2')))) | ~m1_pre_topc(A_78, A_78) | ~m1_pre_topc(A_78, '#skF_3') | ~m1_pre_topc('#skF_3', A_78) | ~v2_pre_topc(A_78) | v2_struct_0(A_78) | ~l1_pre_topc(A_78) | ~m1_pre_topc(A_78, '#skF_3') | ~m1_pre_topc('#skF_3', A_78) | ~v2_pre_topc(A_78) | v2_struct_0(A_78) | ~l1_pre_topc(A_78))), inference(superposition, [status(thm), theory('equality')], [c_436, c_820])).
% 6.95/2.34  tff(c_6, plain, (![A_6, B_7, C_8, D_9]: (k3_funct_2(A_6, B_7, C_8, D_9)=k1_funct_1(C_8, D_9) | ~m1_subset_1(D_9, A_6) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))) | ~v1_funct_2(C_8, A_6, B_7) | ~v1_funct_1(C_8) | v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.95/2.34  tff(c_1991, plain, (![B_7, C_8]: (k3_funct_2(u1_struct_0('#skF_3'), B_7, C_8, '#skF_1'('#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_3'))=k1_funct_1(C_8, '#skF_1'('#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_3')) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), B_7))) | ~v1_funct_2(C_8, u1_struct_0('#skF_3'), B_7) | ~v1_funct_1(C_8) | v1_xboole_0(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_1982, c_6])).
% 6.95/2.34  tff(c_2064, plain, (![B_456, C_457]: (k3_funct_2(u1_struct_0('#skF_3'), B_456, C_457, '#skF_1'('#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_3'))=k1_funct_1(C_457, '#skF_1'('#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_3')) | ~m1_subset_1(C_457, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), B_456))) | ~v1_funct_2(C_457, u1_struct_0('#skF_3'), B_456) | ~v1_funct_1(C_457))), inference(negUnitSimplification, [status(thm)], [c_154, c_1991])).
% 6.95/2.34  tff(c_2068, plain, (k3_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_3', '#skF_4'), '#skF_1'('#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_3'))=k1_funct_1(k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_3', '#skF_4'), '#skF_1'('#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_3')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_846, c_2064])).
% 6.95/2.34  tff(c_2090, plain, (k3_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_1'('#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_3'))='#skF_1'('#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_96, c_450, c_60, c_649, c_58, c_649, c_1951, c_649, c_649, c_2068])).
% 6.95/2.34  tff(c_2091, plain, (k3_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_1'('#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_3'))='#skF_1'('#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_64, c_2090])).
% 6.95/2.34  tff(c_40, plain, (![B_111, C_127, D_135, E_139, A_79]: (k3_funct_2(u1_struct_0(B_111), u1_struct_0(A_79), D_135, '#skF_1'(C_127, A_79, E_139, D_135, B_111))!=k1_funct_1(E_139, '#skF_1'(C_127, A_79, E_139, D_135, B_111)) | r2_funct_2(u1_struct_0(C_127), u1_struct_0(A_79), k2_tmap_1(B_111, A_79, D_135, C_127), E_139) | ~m1_subset_1(E_139, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_127), u1_struct_0(A_79)))) | ~v1_funct_2(E_139, u1_struct_0(C_127), u1_struct_0(A_79)) | ~v1_funct_1(E_139) | ~m1_subset_1(D_135, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_111), u1_struct_0(A_79)))) | ~v1_funct_2(D_135, u1_struct_0(B_111), u1_struct_0(A_79)) | ~v1_funct_1(D_135) | ~m1_pre_topc(C_127, B_111) | v2_struct_0(C_127) | ~l1_pre_topc(B_111) | ~v2_pre_topc(B_111) | v2_struct_0(B_111) | ~l1_pre_topc(A_79) | ~v2_pre_topc(A_79) | v2_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_253])).
% 6.95/2.34  tff(c_2107, plain, (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_3'))!='#skF_1'('#skF_3', '#skF_2', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4', '#skF_3') | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2091, c_40])).
% 6.95/2.34  tff(c_2111, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_96, c_84, c_450, c_60, c_58, c_56, c_1818, c_1847, c_646, c_2000, c_2107])).
% 6.95/2.34  tff(c_2112, plain, (~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_1899, c_2111])).
% 6.95/2.34  tff(c_2116, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_2112])).
% 6.95/2.34  tff(c_2119, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_62, c_2116])).
% 6.95/2.34  tff(c_2121, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_2119])).
% 6.95/2.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.95/2.34  
% 6.95/2.34  Inference rules
% 6.95/2.34  ----------------------
% 6.95/2.34  #Ref     : 0
% 6.95/2.34  #Sup     : 408
% 6.95/2.34  #Fact    : 0
% 6.95/2.34  #Define  : 0
% 6.95/2.34  #Split   : 13
% 6.95/2.34  #Chain   : 0
% 6.95/2.34  #Close   : 0
% 6.95/2.34  
% 6.95/2.34  Ordering : KBO
% 6.95/2.34  
% 6.95/2.34  Simplification rules
% 6.95/2.34  ----------------------
% 6.95/2.34  #Subsume      : 61
% 6.95/2.34  #Demod        : 1043
% 6.95/2.34  #Tautology    : 151
% 6.95/2.34  #SimpNegUnit  : 166
% 6.95/2.34  #BackRed      : 14
% 6.95/2.34  
% 6.95/2.34  #Partial instantiations: 0
% 6.95/2.34  #Strategies tried      : 1
% 6.95/2.34  
% 6.95/2.34  Timing (in seconds)
% 6.95/2.34  ----------------------
% 6.95/2.34  Preprocessing        : 0.45
% 6.95/2.34  Parsing              : 0.23
% 6.95/2.34  CNF conversion       : 0.05
% 6.95/2.34  Main loop            : 1.08
% 6.95/2.34  Inferencing          : 0.37
% 6.95/2.34  Reduction            : 0.34
% 6.95/2.34  Demodulation         : 0.25
% 6.95/2.34  BG Simplification    : 0.05
% 6.95/2.34  Subsumption          : 0.27
% 6.95/2.34  Abstraction          : 0.05
% 6.95/2.34  MUC search           : 0.00
% 6.95/2.34  Cooper               : 0.00
% 6.95/2.34  Total                : 1.60
% 6.95/2.34  Index Insertion      : 0.00
% 6.95/2.34  Index Deletion       : 0.00
% 6.95/2.34  Index Matching       : 0.00
% 6.95/2.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
