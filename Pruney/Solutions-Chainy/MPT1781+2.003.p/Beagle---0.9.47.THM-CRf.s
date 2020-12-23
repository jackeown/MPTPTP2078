%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:45 EST 2020

% Result     : Theorem 4.76s
% Output     : CNFRefutation 4.76s
% Verified   : 
% Statistics : Number of formulae       :  196 (48910 expanded)
%              Number of leaves         :   44 (18644 expanded)
%              Depth                    :   39
%              Number of atoms          :  716 (310312 expanded)
%              Number of equality atoms :   57 (27830 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_tmap_1 > k2_partfun1 > k4_tmap_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(f_328,negated_conjecture,(
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

tff(f_188,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_funct_1(k4_tmap_1(A,B))
        & v1_funct_2(k4_tmap_1(A,B),u1_struct_0(B),u1_struct_0(A))
        & m1_subset_1(k4_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_tmap_1)).

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

tff(f_192,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_155,axiom,(
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

tff(f_173,axiom,(
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

tff(f_123,axiom,(
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

tff(f_266,axiom,(
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

tff(f_236,axiom,(
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

tff(f_96,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => m1_subset_1(C,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_298,axiom,(
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

tff(c_68,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_328])).

tff(c_66,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_328])).

tff(c_64,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_328])).

tff(c_60,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_328])).

tff(c_30,plain,(
    ! [A_77,B_78] :
      ( m1_subset_1(k4_tmap_1(A_77,B_78),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_78),u1_struct_0(A_77))))
      | ~ m1_pre_topc(B_78,A_77)
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_328])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_328])).

tff(c_56,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_328])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_328])).

tff(c_124,plain,(
    ! [A_204,B_205,D_206] :
      ( r2_funct_2(A_204,B_205,D_206,D_206)
      | ~ m1_subset_1(D_206,k1_zfmisc_1(k2_zfmisc_1(A_204,B_205)))
      | ~ v1_funct_2(D_206,A_204,B_205)
      | ~ v1_funct_1(D_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_126,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5','#skF_5')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_124])).

tff(c_129,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_126])).

tff(c_34,plain,(
    ! [A_77,B_78] :
      ( v1_funct_1(k4_tmap_1(A_77,B_78))
      | ~ m1_pre_topc(B_78,A_77)
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_88,plain,(
    ! [B_190,A_191] :
      ( v2_pre_topc(B_190)
      | ~ m1_pre_topc(B_190,A_191)
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_94,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_88])).

tff(c_98,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_94])).

tff(c_77,plain,(
    ! [B_188,A_189] :
      ( l1_pre_topc(B_188)
      | ~ m1_pre_topc(B_188,A_189)
      | ~ l1_pre_topc(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_83,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_77])).

tff(c_87,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_83])).

tff(c_36,plain,(
    ! [A_79] :
      ( m1_pre_topc(A_79,A_79)
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_270,plain,(
    ! [B_261,A_263,D_265,E_264,C_262] :
      ( k3_tmap_1(A_263,B_261,C_262,D_265,E_264) = k2_partfun1(u1_struct_0(C_262),u1_struct_0(B_261),E_264,u1_struct_0(D_265))
      | ~ m1_pre_topc(D_265,C_262)
      | ~ m1_subset_1(E_264,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_262),u1_struct_0(B_261))))
      | ~ v1_funct_2(E_264,u1_struct_0(C_262),u1_struct_0(B_261))
      | ~ v1_funct_1(E_264)
      | ~ m1_pre_topc(D_265,A_263)
      | ~ m1_pre_topc(C_262,A_263)
      | ~ l1_pre_topc(B_261)
      | ~ v2_pre_topc(B_261)
      | v2_struct_0(B_261)
      | ~ l1_pre_topc(A_263)
      | ~ v2_pre_topc(A_263)
      | v2_struct_0(A_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_276,plain,(
    ! [A_263,D_265] :
      ( k3_tmap_1(A_263,'#skF_3','#skF_4',D_265,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_265))
      | ~ m1_pre_topc(D_265,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_265,A_263)
      | ~ m1_pre_topc('#skF_4',A_263)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_263)
      | ~ v2_pre_topc(A_263)
      | v2_struct_0(A_263) ) ),
    inference(resolution,[status(thm)],[c_54,c_270])).

tff(c_281,plain,(
    ! [A_263,D_265] :
      ( k3_tmap_1(A_263,'#skF_3','#skF_4',D_265,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_265))
      | ~ m1_pre_topc(D_265,'#skF_4')
      | ~ m1_pre_topc(D_265,A_263)
      | ~ m1_pre_topc('#skF_4',A_263)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_263)
      | ~ v2_pre_topc(A_263)
      | v2_struct_0(A_263) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_56,c_276])).

tff(c_283,plain,(
    ! [A_266,D_267] :
      ( k3_tmap_1(A_266,'#skF_3','#skF_4',D_267,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_267))
      | ~ m1_pre_topc(D_267,'#skF_4')
      | ~ m1_pre_topc(D_267,A_266)
      | ~ m1_pre_topc('#skF_4',A_266)
      | ~ l1_pre_topc(A_266)
      | ~ v2_pre_topc(A_266)
      | v2_struct_0(A_266) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_281])).

tff(c_287,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_3','#skF_4','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_283])).

tff(c_291,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_3','#skF_4','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_287])).

tff(c_292,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_3','#skF_4','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_291])).

tff(c_293,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_292])).

tff(c_296,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_293])).

tff(c_300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_296])).

tff(c_302,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_292])).

tff(c_14,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_147,plain,(
    ! [A_216,B_217,C_218,D_219] :
      ( v1_funct_1(k2_tmap_1(A_216,B_217,C_218,D_219))
      | ~ l1_struct_0(D_219)
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_216),u1_struct_0(B_217))))
      | ~ v1_funct_2(C_218,u1_struct_0(A_216),u1_struct_0(B_217))
      | ~ v1_funct_1(C_218)
      | ~ l1_struct_0(B_217)
      | ~ l1_struct_0(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_151,plain,(
    ! [D_219] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_3','#skF_5',D_219))
      | ~ l1_struct_0(D_219)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_3')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_147])).

tff(c_155,plain,(
    ! [D_219] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_3','#skF_5',D_219))
      | ~ l1_struct_0(D_219)
      | ~ l1_struct_0('#skF_3')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_151])).

tff(c_156,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_155])).

tff(c_159,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_156])).

tff(c_163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_159])).

tff(c_165,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_155])).

tff(c_164,plain,(
    ! [D_219] :
      ( ~ l1_struct_0('#skF_3')
      | v1_funct_1(k2_tmap_1('#skF_4','#skF_3','#skF_5',D_219))
      | ~ l1_struct_0(D_219) ) ),
    inference(splitRight,[status(thm)],[c_155])).

tff(c_173,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_164])).

tff(c_176,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_173])).

tff(c_180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_176])).

tff(c_182,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_185,plain,(
    ! [A_227,B_228,C_229,D_230] :
      ( v1_funct_2(k2_tmap_1(A_227,B_228,C_229,D_230),u1_struct_0(D_230),u1_struct_0(B_228))
      | ~ l1_struct_0(D_230)
      | ~ m1_subset_1(C_229,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_227),u1_struct_0(B_228))))
      | ~ v1_funct_2(C_229,u1_struct_0(A_227),u1_struct_0(B_228))
      | ~ v1_funct_1(C_229)
      | ~ l1_struct_0(B_228)
      | ~ l1_struct_0(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_189,plain,(
    ! [D_230] :
      ( v1_funct_2(k2_tmap_1('#skF_4','#skF_3','#skF_5',D_230),u1_struct_0(D_230),u1_struct_0('#skF_3'))
      | ~ l1_struct_0(D_230)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_3')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_185])).

tff(c_193,plain,(
    ! [D_230] :
      ( v1_funct_2(k2_tmap_1('#skF_4','#skF_3','#skF_5',D_230),u1_struct_0(D_230),u1_struct_0('#skF_3'))
      | ~ l1_struct_0(D_230) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_182,c_58,c_56,c_189])).

tff(c_24,plain,(
    ! [A_73,B_74,C_75,D_76] :
      ( m1_subset_1(k2_tmap_1(A_73,B_74,C_75,D_76),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_76),u1_struct_0(B_74))))
      | ~ l1_struct_0(D_76)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_73),u1_struct_0(B_74))))
      | ~ v1_funct_2(C_75,u1_struct_0(A_73),u1_struct_0(B_74))
      | ~ v1_funct_1(C_75)
      | ~ l1_struct_0(B_74)
      | ~ l1_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_181,plain,(
    ! [D_219] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_3','#skF_5',D_219))
      | ~ l1_struct_0(D_219) ) ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_301,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_3','#skF_4','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_292])).

tff(c_219,plain,(
    ! [A_247,B_248,C_249,D_250] :
      ( k2_partfun1(u1_struct_0(A_247),u1_struct_0(B_248),C_249,u1_struct_0(D_250)) = k2_tmap_1(A_247,B_248,C_249,D_250)
      | ~ m1_pre_topc(D_250,A_247)
      | ~ m1_subset_1(C_249,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_247),u1_struct_0(B_248))))
      | ~ v1_funct_2(C_249,u1_struct_0(A_247),u1_struct_0(B_248))
      | ~ v1_funct_1(C_249)
      | ~ l1_pre_topc(B_248)
      | ~ v2_pre_topc(B_248)
      | v2_struct_0(B_248)
      | ~ l1_pre_topc(A_247)
      | ~ v2_pre_topc(A_247)
      | v2_struct_0(A_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_225,plain,(
    ! [D_250] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_250)) = k2_tmap_1('#skF_4','#skF_3','#skF_5',D_250)
      | ~ m1_pre_topc(D_250,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_219])).

tff(c_230,plain,(
    ! [D_250] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_250)) = k2_tmap_1('#skF_4','#skF_3','#skF_5',D_250)
      | ~ m1_pre_topc(D_250,'#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_87,c_66,c_64,c_58,c_56,c_225])).

tff(c_231,plain,(
    ! [D_250] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_250)) = k2_tmap_1('#skF_4','#skF_3','#skF_5',D_250)
      | ~ m1_pre_topc(D_250,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_68,c_230])).

tff(c_327,plain,
    ( k3_tmap_1('#skF_3','#skF_3','#skF_4','#skF_4','#skF_5') = k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_231])).

tff(c_334,plain,(
    k3_tmap_1('#skF_3','#skF_3','#skF_4','#skF_4','#skF_5') = k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_327])).

tff(c_338,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0('#skF_4')) = k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_301])).

tff(c_282,plain,(
    ! [A_263,D_265] :
      ( k3_tmap_1(A_263,'#skF_3','#skF_4',D_265,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_265))
      | ~ m1_pre_topc(D_265,'#skF_4')
      | ~ m1_pre_topc(D_265,A_263)
      | ~ m1_pre_topc('#skF_4',A_263)
      | ~ l1_pre_topc(A_263)
      | ~ v2_pre_topc(A_263)
      | v2_struct_0(A_263) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_281])).

tff(c_304,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_4','#skF_3','#skF_4','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_302,c_282])).

tff(c_315,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_4','#skF_3','#skF_4','#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_87,c_302,c_304])).

tff(c_316,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_4','#skF_3','#skF_4','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_315])).

tff(c_390,plain,(
    k3_tmap_1('#skF_4','#skF_3','#skF_4','#skF_4','#skF_5') = k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_316])).

tff(c_241,plain,(
    ! [C_252,B_253,D_254,A_255] :
      ( r2_funct_2(u1_struct_0(C_252),u1_struct_0(B_253),D_254,k3_tmap_1(A_255,B_253,C_252,C_252,D_254))
      | ~ m1_subset_1(D_254,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_252),u1_struct_0(B_253))))
      | ~ v1_funct_2(D_254,u1_struct_0(C_252),u1_struct_0(B_253))
      | ~ v1_funct_1(D_254)
      | ~ m1_pre_topc(C_252,A_255)
      | v2_struct_0(C_252)
      | ~ l1_pre_topc(B_253)
      | ~ v2_pre_topc(B_253)
      | v2_struct_0(B_253)
      | ~ l1_pre_topc(A_255)
      | ~ v2_pre_topc(A_255)
      | v2_struct_0(A_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_266])).

tff(c_247,plain,(
    ! [A_255] :
      ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k3_tmap_1(A_255,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_255)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_255)
      | ~ v2_pre_topc(A_255)
      | v2_struct_0(A_255) ) ),
    inference(resolution,[status(thm)],[c_54,c_241])).

tff(c_252,plain,(
    ! [A_255] :
      ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k3_tmap_1(A_255,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_255)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_255)
      | ~ v2_pre_topc(A_255)
      | v2_struct_0(A_255) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_56,c_247])).

tff(c_254,plain,(
    ! [A_256] :
      ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k3_tmap_1(A_256,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_256)
      | ~ l1_pre_topc(A_256)
      | ~ v2_pre_topc(A_256)
      | v2_struct_0(A_256) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_252])).

tff(c_10,plain,(
    ! [D_12,C_11,A_9,B_10] :
      ( D_12 = C_11
      | ~ r2_funct_2(A_9,B_10,C_11,D_12)
      | ~ m1_subset_1(D_12,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10)))
      | ~ v1_funct_2(D_12,A_9,B_10)
      | ~ v1_funct_1(D_12)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10)))
      | ~ v1_funct_2(C_11,A_9,B_10)
      | ~ v1_funct_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_256,plain,(
    ! [A_256] :
      ( k3_tmap_1(A_256,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ m1_subset_1(k3_tmap_1(A_256,'#skF_3','#skF_4','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(k3_tmap_1(A_256,'#skF_3','#skF_4','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k3_tmap_1(A_256,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_256)
      | ~ l1_pre_topc(A_256)
      | ~ v2_pre_topc(A_256)
      | v2_struct_0(A_256) ) ),
    inference(resolution,[status(thm)],[c_254,c_10])).

tff(c_259,plain,(
    ! [A_256] :
      ( k3_tmap_1(A_256,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ m1_subset_1(k3_tmap_1(A_256,'#skF_3','#skF_4','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(k3_tmap_1(A_256,'#skF_3','#skF_4','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k3_tmap_1(A_256,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_256)
      | ~ l1_pre_topc(A_256)
      | ~ v2_pre_topc(A_256)
      | v2_struct_0(A_256) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_256])).

tff(c_394,plain,
    ( k3_tmap_1('#skF_4','#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
    | ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_3','#skF_4','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k3_tmap_1('#skF_4','#skF_3','#skF_4','#skF_4','#skF_5'))
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_390,c_259])).

tff(c_401,plain,
    ( k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4') = '#skF_5'
    | ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_87,c_302,c_390,c_390,c_390,c_394])).

tff(c_402,plain,
    ( k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4') = '#skF_5'
    | ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_401])).

tff(c_456,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_402])).

tff(c_459,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_181,c_456])).

tff(c_463,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_459])).

tff(c_464,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_402])).

tff(c_466,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_464])).

tff(c_469,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_466])).

tff(c_473,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_182,c_58,c_56,c_54,c_469])).

tff(c_474,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_464])).

tff(c_538,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_474])).

tff(c_541,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_193,c_538])).

tff(c_545,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_541])).

tff(c_546,plain,(
    k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_474])).

tff(c_476,plain,(
    ! [B_278,A_275,E_279,D_277,C_276] :
      ( m1_subset_1('#skF_2'(A_275,C_276,D_277,B_278,E_279),u1_struct_0(B_278))
      | r2_funct_2(u1_struct_0(C_276),u1_struct_0(A_275),k2_tmap_1(B_278,A_275,D_277,C_276),E_279)
      | ~ m1_subset_1(E_279,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_276),u1_struct_0(A_275))))
      | ~ v1_funct_2(E_279,u1_struct_0(C_276),u1_struct_0(A_275))
      | ~ v1_funct_1(E_279)
      | ~ m1_subset_1(D_277,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_278),u1_struct_0(A_275))))
      | ~ v1_funct_2(D_277,u1_struct_0(B_278),u1_struct_0(A_275))
      | ~ v1_funct_1(D_277)
      | ~ m1_pre_topc(C_276,B_278)
      | v2_struct_0(C_276)
      | ~ l1_pre_topc(B_278)
      | ~ v2_pre_topc(B_278)
      | v2_struct_0(B_278)
      | ~ l1_pre_topc(A_275)
      | ~ v2_pre_topc(A_275)
      | v2_struct_0(A_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_895,plain,(
    ! [A_325,B_326,D_327,B_328] :
      ( m1_subset_1('#skF_2'(A_325,B_326,D_327,B_328,k4_tmap_1(A_325,B_326)),u1_struct_0(B_328))
      | r2_funct_2(u1_struct_0(B_326),u1_struct_0(A_325),k2_tmap_1(B_328,A_325,D_327,B_326),k4_tmap_1(A_325,B_326))
      | ~ v1_funct_2(k4_tmap_1(A_325,B_326),u1_struct_0(B_326),u1_struct_0(A_325))
      | ~ v1_funct_1(k4_tmap_1(A_325,B_326))
      | ~ m1_subset_1(D_327,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_328),u1_struct_0(A_325))))
      | ~ v1_funct_2(D_327,u1_struct_0(B_328),u1_struct_0(A_325))
      | ~ v1_funct_1(D_327)
      | ~ m1_pre_topc(B_326,B_328)
      | v2_struct_0(B_326)
      | ~ l1_pre_topc(B_328)
      | ~ v2_pre_topc(B_328)
      | v2_struct_0(B_328)
      | ~ m1_pre_topc(B_326,A_325)
      | ~ l1_pre_topc(A_325)
      | ~ v2_pre_topc(A_325)
      | v2_struct_0(A_325) ) ),
    inference(resolution,[status(thm)],[c_30,c_476])).

tff(c_904,plain,
    ( m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4')),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_546,c_895])).

tff(c_909,plain,
    ( m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4')),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_98,c_87,c_302,c_58,c_56,c_54,c_904])).

tff(c_910,plain,
    ( m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4')),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_909])).

tff(c_911,plain,(
    ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_910])).

tff(c_914,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_911])).

tff(c_917,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_914])).

tff(c_919,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_917])).

tff(c_921,plain,(
    v1_funct_1(k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_910])).

tff(c_32,plain,(
    ! [A_77,B_78] :
      ( v1_funct_2(k4_tmap_1(A_77,B_78),u1_struct_0(B_78),u1_struct_0(A_77))
      | ~ m1_pre_topc(B_78,A_77)
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_920,plain,
    ( ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4')),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_910])).

tff(c_924,plain,(
    ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_920])).

tff(c_927,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_924])).

tff(c_930,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_927])).

tff(c_932,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_930])).

tff(c_934,plain,(
    v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_920])).

tff(c_933,plain,
    ( m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4')),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_920])).

tff(c_935,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_933])).

tff(c_937,plain,
    ( k4_tmap_1('#skF_3','#skF_4') = '#skF_5'
    | ~ m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_935,c_10])).

tff(c_940,plain,
    ( k4_tmap_1('#skF_3','#skF_4') = '#skF_5'
    | ~ m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_921,c_934,c_937])).

tff(c_951,plain,(
    ~ m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_940])).

tff(c_954,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_951])).

tff(c_957,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_954])).

tff(c_959,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_957])).

tff(c_960,plain,(
    k4_tmap_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_940])).

tff(c_50,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_328])).

tff(c_965,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_960,c_50])).

tff(c_971,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_965])).

tff(c_973,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_933])).

tff(c_972,plain,(
    m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4')),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_933])).

tff(c_18,plain,(
    ! [C_26,A_20,B_24] :
      ( m1_subset_1(C_26,u1_struct_0(A_20))
      | ~ m1_subset_1(C_26,u1_struct_0(B_24))
      | ~ m1_pre_topc(B_24,A_20)
      | v2_struct_0(B_24)
      | ~ l1_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_990,plain,(
    ! [A_20] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4')),u1_struct_0(A_20))
      | ~ m1_pre_topc('#skF_4',A_20)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(resolution,[status(thm)],[c_972,c_18])).

tff(c_995,plain,(
    ! [A_336] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4')),u1_struct_0(A_336))
      | ~ m1_pre_topc('#skF_4',A_336)
      | ~ l1_pre_topc(A_336)
      | v2_struct_0(A_336) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_990])).

tff(c_1002,plain,(
    ! [A_337,A_338] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4')),u1_struct_0(A_337))
      | ~ m1_pre_topc(A_338,A_337)
      | ~ l1_pre_topc(A_337)
      | v2_struct_0(A_337)
      | ~ m1_pre_topc('#skF_4',A_338)
      | ~ l1_pre_topc(A_338)
      | v2_struct_0(A_338) ) ),
    inference(resolution,[status(thm)],[c_995,c_18])).

tff(c_1008,plain,
    ( m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4')),u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_1002])).

tff(c_1016,plain,
    ( m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4')),u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_302,c_64,c_1008])).

tff(c_1017,plain,(
    m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4')),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_68,c_1016])).

tff(c_377,plain,(
    ! [A_268,C_269,D_270,E_272,B_271] :
      ( r2_hidden('#skF_2'(A_268,C_269,D_270,B_271,E_272),u1_struct_0(C_269))
      | r2_funct_2(u1_struct_0(C_269),u1_struct_0(A_268),k2_tmap_1(B_271,A_268,D_270,C_269),E_272)
      | ~ m1_subset_1(E_272,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_269),u1_struct_0(A_268))))
      | ~ v1_funct_2(E_272,u1_struct_0(C_269),u1_struct_0(A_268))
      | ~ v1_funct_1(E_272)
      | ~ m1_subset_1(D_270,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_271),u1_struct_0(A_268))))
      | ~ v1_funct_2(D_270,u1_struct_0(B_271),u1_struct_0(A_268))
      | ~ v1_funct_1(D_270)
      | ~ m1_pre_topc(C_269,B_271)
      | v2_struct_0(C_269)
      | ~ l1_pre_topc(B_271)
      | ~ v2_pre_topc(B_271)
      | v2_struct_0(B_271)
      | ~ l1_pre_topc(A_268)
      | ~ v2_pre_topc(A_268)
      | v2_struct_0(A_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_1026,plain,(
    ! [A_339,B_340,D_341,B_342] :
      ( r2_hidden('#skF_2'(A_339,B_340,D_341,B_342,k4_tmap_1(A_339,B_340)),u1_struct_0(B_340))
      | r2_funct_2(u1_struct_0(B_340),u1_struct_0(A_339),k2_tmap_1(B_342,A_339,D_341,B_340),k4_tmap_1(A_339,B_340))
      | ~ v1_funct_2(k4_tmap_1(A_339,B_340),u1_struct_0(B_340),u1_struct_0(A_339))
      | ~ v1_funct_1(k4_tmap_1(A_339,B_340))
      | ~ m1_subset_1(D_341,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_342),u1_struct_0(A_339))))
      | ~ v1_funct_2(D_341,u1_struct_0(B_342),u1_struct_0(A_339))
      | ~ v1_funct_1(D_341)
      | ~ m1_pre_topc(B_340,B_342)
      | v2_struct_0(B_340)
      | ~ l1_pre_topc(B_342)
      | ~ v2_pre_topc(B_342)
      | v2_struct_0(B_342)
      | ~ m1_pre_topc(B_340,A_339)
      | ~ l1_pre_topc(A_339)
      | ~ v2_pre_topc(A_339)
      | v2_struct_0(A_339) ) ),
    inference(resolution,[status(thm)],[c_30,c_377])).

tff(c_1031,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4')),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_546,c_1026])).

tff(c_1034,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4')),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_98,c_87,c_302,c_58,c_56,c_54,c_921,c_934,c_1031])).

tff(c_1035,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4')),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_973,c_1034])).

tff(c_52,plain,(
    ! [D_182] :
      ( k1_funct_1('#skF_5',D_182) = D_182
      | ~ r2_hidden(D_182,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(D_182,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_328])).

tff(c_1040,plain,
    ( k1_funct_1('#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'))) = '#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4')),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1035,c_52])).

tff(c_1049,plain,(
    k1_funct_1('#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'))) = '#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1017,c_1040])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1050,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1035,c_2])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7,D_8] :
      ( k3_funct_2(A_5,B_6,C_7,D_8) = k1_funct_1(C_7,D_8)
      | ~ m1_subset_1(D_8,A_5)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6)))
      | ~ v1_funct_2(C_7,A_5,B_6)
      | ~ v1_funct_1(C_7)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_991,plain,(
    ! [B_6,C_7] :
      ( k3_funct_2(u1_struct_0('#skF_4'),B_6,C_7,'#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'))) = k1_funct_1(C_7,'#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4')))
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),B_6)))
      | ~ v1_funct_2(C_7,u1_struct_0('#skF_4'),B_6)
      | ~ v1_funct_1(C_7)
      | v1_xboole_0(u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_972,c_6])).

tff(c_1086,plain,(
    ! [B_346,C_347] :
      ( k3_funct_2(u1_struct_0('#skF_4'),B_346,C_347,'#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'))) = k1_funct_1(C_347,'#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4')))
      | ~ m1_subset_1(C_347,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),B_346)))
      | ~ v1_funct_2(C_347,u1_struct_0('#skF_4'),B_346)
      | ~ v1_funct_1(C_347) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1050,c_991])).

tff(c_1097,plain,
    ( k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'))) = k1_funct_1('#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_1086])).

tff(c_1104,plain,(
    k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'))) = '#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1049,c_1097])).

tff(c_38,plain,(
    ! [E_140,C_128,D_136,A_80,B_112] :
      ( k3_funct_2(u1_struct_0(B_112),u1_struct_0(A_80),D_136,'#skF_2'(A_80,C_128,D_136,B_112,E_140)) != k1_funct_1(E_140,'#skF_2'(A_80,C_128,D_136,B_112,E_140))
      | r2_funct_2(u1_struct_0(C_128),u1_struct_0(A_80),k2_tmap_1(B_112,A_80,D_136,C_128),E_140)
      | ~ m1_subset_1(E_140,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_128),u1_struct_0(A_80))))
      | ~ v1_funct_2(E_140,u1_struct_0(C_128),u1_struct_0(A_80))
      | ~ v1_funct_1(E_140)
      | ~ m1_subset_1(D_136,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_112),u1_struct_0(A_80))))
      | ~ v1_funct_2(D_136,u1_struct_0(B_112),u1_struct_0(A_80))
      | ~ v1_funct_1(D_136)
      | ~ m1_pre_topc(C_128,B_112)
      | v2_struct_0(C_128)
      | ~ l1_pre_topc(B_112)
      | ~ v2_pre_topc(B_112)
      | v2_struct_0(B_112)
      | ~ l1_pre_topc(A_80)
      | ~ v2_pre_topc(A_80)
      | v2_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_1107,plain,
    ( k1_funct_1(k4_tmap_1('#skF_3','#skF_4'),'#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'))) != '#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4'),k4_tmap_1('#skF_3','#skF_4'))
    | ~ m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1104,c_38])).

tff(c_1111,plain,
    ( k1_funct_1(k4_tmap_1('#skF_3','#skF_4'),'#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'))) != '#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | ~ m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_98,c_87,c_302,c_58,c_56,c_54,c_921,c_934,c_546,c_1107])).

tff(c_1112,plain,
    ( k1_funct_1(k4_tmap_1('#skF_3','#skF_4'),'#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'))) != '#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'))
    | ~ m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_973,c_1111])).

tff(c_1115,plain,(
    ~ m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_1112])).

tff(c_1118,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_1115])).

tff(c_1121,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_1118])).

tff(c_1123,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1121])).

tff(c_1124,plain,(
    k1_funct_1(k4_tmap_1('#skF_3','#skF_4'),'#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'))) != '#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1112])).

tff(c_48,plain,(
    ! [A_164,B_168,C_170] :
      ( k1_funct_1(k4_tmap_1(A_164,B_168),C_170) = C_170
      | ~ r2_hidden(C_170,u1_struct_0(B_168))
      | ~ m1_subset_1(C_170,u1_struct_0(A_164))
      | ~ m1_pre_topc(B_168,A_164)
      | v2_struct_0(B_168)
      | ~ l1_pre_topc(A_164)
      | ~ v2_pre_topc(A_164)
      | v2_struct_0(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_1037,plain,(
    ! [A_164] :
      ( k1_funct_1(k4_tmap_1(A_164,'#skF_4'),'#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'))) = '#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4')),u1_struct_0(A_164))
      | ~ m1_pre_topc('#skF_4',A_164)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_164)
      | ~ v2_pre_topc(A_164)
      | v2_struct_0(A_164) ) ),
    inference(resolution,[status(thm)],[c_1035,c_48])).

tff(c_1453,plain,(
    ! [A_374] :
      ( k1_funct_1(k4_tmap_1(A_374,'#skF_4'),'#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'))) = '#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4')),u1_struct_0(A_374))
      | ~ m1_pre_topc('#skF_4',A_374)
      | ~ l1_pre_topc(A_374)
      | ~ v2_pre_topc(A_374)
      | v2_struct_0(A_374) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1037])).

tff(c_1459,plain,
    ( k1_funct_1(k4_tmap_1('#skF_3','#skF_4'),'#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'))) = '#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1017,c_1453])).

tff(c_1471,plain,
    ( k1_funct_1(k4_tmap_1('#skF_3','#skF_4'),'#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'))) = '#skF_2'('#skF_3','#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_1459])).

tff(c_1473,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1124,c_1471])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:23:47 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.76/1.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.76/1.83  
% 4.76/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.76/1.83  %$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_tmap_1 > k2_partfun1 > k4_tmap_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 4.76/1.83  
% 4.76/1.83  %Foreground sorts:
% 4.76/1.83  
% 4.76/1.83  
% 4.76/1.83  %Background operators:
% 4.76/1.83  
% 4.76/1.83  
% 4.76/1.83  %Foreground operators:
% 4.76/1.83  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.76/1.83  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.76/1.83  tff(k4_tmap_1, type, k4_tmap_1: ($i * $i) > $i).
% 4.76/1.83  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.76/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.76/1.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.76/1.83  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 4.76/1.83  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.76/1.83  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.76/1.83  tff('#skF_5', type, '#skF_5': $i).
% 4.76/1.83  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.76/1.83  tff('#skF_3', type, '#skF_3': $i).
% 4.76/1.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.76/1.83  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.76/1.83  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.76/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.76/1.83  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.76/1.83  tff('#skF_4', type, '#skF_4': $i).
% 4.76/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.76/1.83  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.76/1.83  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 4.76/1.83  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.76/1.83  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 4.76/1.83  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.76/1.83  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.76/1.83  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 4.76/1.83  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 4.76/1.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.76/1.83  
% 4.76/1.86  tff(f_328, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, u1_struct_0(B)) => (D = k1_funct_1(C, D))))) => r2_funct_2(u1_struct_0(B), u1_struct_0(A), k4_tmap_1(A, B), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_tmap_1)).
% 4.76/1.86  tff(f_188, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_funct_1(k4_tmap_1(A, B)) & v1_funct_2(k4_tmap_1(A, B), u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(k4_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_tmap_1)).
% 4.76/1.86  tff(f_60, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 4.76/1.86  tff(f_69, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.76/1.86  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.76/1.86  tff(f_192, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 4.76/1.86  tff(f_155, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 4.76/1.86  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.76/1.86  tff(f_173, axiom, (![A, B, C, D]: ((((((l1_struct_0(A) & l1_struct_0(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & l1_struct_0(D)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 4.76/1.86  tff(f_123, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 4.76/1.86  tff(f_266, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), D, k3_tmap_1(A, B, C, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tmap_1)).
% 4.76/1.86  tff(f_236, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(A))))) => ((![F]: (m1_subset_1(F, u1_struct_0(B)) => (r2_hidden(F, u1_struct_0(C)) => (k3_funct_2(u1_struct_0(B), u1_struct_0(A), D, F) = k1_funct_1(E, F))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(A), k2_tmap_1(B, A, D, C), E)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_tmap_1)).
% 4.76/1.86  tff(f_96, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 4.76/1.86  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.76/1.86  tff(f_44, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 4.76/1.86  tff(f_298, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, u1_struct_0(B)) => (k1_funct_1(k4_tmap_1(A, B), C) = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_tmap_1)).
% 4.76/1.86  tff(c_68, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_328])).
% 4.76/1.86  tff(c_66, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_328])).
% 4.76/1.86  tff(c_64, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_328])).
% 4.76/1.86  tff(c_60, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_328])).
% 4.76/1.86  tff(c_30, plain, (![A_77, B_78]: (m1_subset_1(k4_tmap_1(A_77, B_78), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_78), u1_struct_0(A_77)))) | ~m1_pre_topc(B_78, A_77) | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.76/1.86  tff(c_62, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_328])).
% 4.76/1.86  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_328])).
% 4.76/1.86  tff(c_56, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_328])).
% 4.76/1.86  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_328])).
% 4.76/1.86  tff(c_124, plain, (![A_204, B_205, D_206]: (r2_funct_2(A_204, B_205, D_206, D_206) | ~m1_subset_1(D_206, k1_zfmisc_1(k2_zfmisc_1(A_204, B_205))) | ~v1_funct_2(D_206, A_204, B_205) | ~v1_funct_1(D_206))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.76/1.86  tff(c_126, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', '#skF_5') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_124])).
% 4.76/1.86  tff(c_129, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_126])).
% 4.76/1.86  tff(c_34, plain, (![A_77, B_78]: (v1_funct_1(k4_tmap_1(A_77, B_78)) | ~m1_pre_topc(B_78, A_77) | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.76/1.86  tff(c_88, plain, (![B_190, A_191]: (v2_pre_topc(B_190) | ~m1_pre_topc(B_190, A_191) | ~l1_pre_topc(A_191) | ~v2_pre_topc(A_191))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.76/1.86  tff(c_94, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_60, c_88])).
% 4.76/1.86  tff(c_98, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_94])).
% 4.76/1.86  tff(c_77, plain, (![B_188, A_189]: (l1_pre_topc(B_188) | ~m1_pre_topc(B_188, A_189) | ~l1_pre_topc(A_189))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.76/1.86  tff(c_83, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_60, c_77])).
% 4.76/1.86  tff(c_87, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_83])).
% 4.76/1.86  tff(c_36, plain, (![A_79]: (m1_pre_topc(A_79, A_79) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_192])).
% 4.76/1.86  tff(c_270, plain, (![B_261, A_263, D_265, E_264, C_262]: (k3_tmap_1(A_263, B_261, C_262, D_265, E_264)=k2_partfun1(u1_struct_0(C_262), u1_struct_0(B_261), E_264, u1_struct_0(D_265)) | ~m1_pre_topc(D_265, C_262) | ~m1_subset_1(E_264, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_262), u1_struct_0(B_261)))) | ~v1_funct_2(E_264, u1_struct_0(C_262), u1_struct_0(B_261)) | ~v1_funct_1(E_264) | ~m1_pre_topc(D_265, A_263) | ~m1_pre_topc(C_262, A_263) | ~l1_pre_topc(B_261) | ~v2_pre_topc(B_261) | v2_struct_0(B_261) | ~l1_pre_topc(A_263) | ~v2_pre_topc(A_263) | v2_struct_0(A_263))), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.76/1.86  tff(c_276, plain, (![A_263, D_265]: (k3_tmap_1(A_263, '#skF_3', '#skF_4', D_265, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_265)) | ~m1_pre_topc(D_265, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_265, A_263) | ~m1_pre_topc('#skF_4', A_263) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_263) | ~v2_pre_topc(A_263) | v2_struct_0(A_263))), inference(resolution, [status(thm)], [c_54, c_270])).
% 4.76/1.86  tff(c_281, plain, (![A_263, D_265]: (k3_tmap_1(A_263, '#skF_3', '#skF_4', D_265, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_265)) | ~m1_pre_topc(D_265, '#skF_4') | ~m1_pre_topc(D_265, A_263) | ~m1_pre_topc('#skF_4', A_263) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_263) | ~v2_pre_topc(A_263) | v2_struct_0(A_263))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_56, c_276])).
% 4.76/1.86  tff(c_283, plain, (![A_266, D_267]: (k3_tmap_1(A_266, '#skF_3', '#skF_4', D_267, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_267)) | ~m1_pre_topc(D_267, '#skF_4') | ~m1_pre_topc(D_267, A_266) | ~m1_pre_topc('#skF_4', A_266) | ~l1_pre_topc(A_266) | ~v2_pre_topc(A_266) | v2_struct_0(A_266))), inference(negUnitSimplification, [status(thm)], [c_68, c_281])).
% 4.76/1.86  tff(c_287, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_3', '#skF_4', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_283])).
% 4.76/1.86  tff(c_291, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_3', '#skF_4', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_287])).
% 4.76/1.86  tff(c_292, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_3', '#skF_4', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_68, c_291])).
% 4.76/1.86  tff(c_293, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_292])).
% 4.76/1.86  tff(c_296, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_36, c_293])).
% 4.76/1.86  tff(c_300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_296])).
% 4.76/1.86  tff(c_302, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_292])).
% 4.76/1.86  tff(c_14, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.76/1.86  tff(c_147, plain, (![A_216, B_217, C_218, D_219]: (v1_funct_1(k2_tmap_1(A_216, B_217, C_218, D_219)) | ~l1_struct_0(D_219) | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_216), u1_struct_0(B_217)))) | ~v1_funct_2(C_218, u1_struct_0(A_216), u1_struct_0(B_217)) | ~v1_funct_1(C_218) | ~l1_struct_0(B_217) | ~l1_struct_0(A_216))), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.76/1.86  tff(c_151, plain, (![D_219]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_219)) | ~l1_struct_0(D_219) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_147])).
% 4.76/1.86  tff(c_155, plain, (![D_219]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_219)) | ~l1_struct_0(D_219) | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_151])).
% 4.76/1.86  tff(c_156, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_155])).
% 4.76/1.86  tff(c_159, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_14, c_156])).
% 4.76/1.86  tff(c_163, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_159])).
% 4.76/1.86  tff(c_165, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_155])).
% 4.76/1.86  tff(c_164, plain, (![D_219]: (~l1_struct_0('#skF_3') | v1_funct_1(k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_219)) | ~l1_struct_0(D_219))), inference(splitRight, [status(thm)], [c_155])).
% 4.76/1.86  tff(c_173, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_164])).
% 4.76/1.86  tff(c_176, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_14, c_173])).
% 4.76/1.86  tff(c_180, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_176])).
% 4.76/1.86  tff(c_182, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_164])).
% 4.76/1.86  tff(c_185, plain, (![A_227, B_228, C_229, D_230]: (v1_funct_2(k2_tmap_1(A_227, B_228, C_229, D_230), u1_struct_0(D_230), u1_struct_0(B_228)) | ~l1_struct_0(D_230) | ~m1_subset_1(C_229, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_227), u1_struct_0(B_228)))) | ~v1_funct_2(C_229, u1_struct_0(A_227), u1_struct_0(B_228)) | ~v1_funct_1(C_229) | ~l1_struct_0(B_228) | ~l1_struct_0(A_227))), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.76/1.86  tff(c_189, plain, (![D_230]: (v1_funct_2(k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_230), u1_struct_0(D_230), u1_struct_0('#skF_3')) | ~l1_struct_0(D_230) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_185])).
% 4.76/1.86  tff(c_193, plain, (![D_230]: (v1_funct_2(k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_230), u1_struct_0(D_230), u1_struct_0('#skF_3')) | ~l1_struct_0(D_230))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_182, c_58, c_56, c_189])).
% 4.76/1.86  tff(c_24, plain, (![A_73, B_74, C_75, D_76]: (m1_subset_1(k2_tmap_1(A_73, B_74, C_75, D_76), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_76), u1_struct_0(B_74)))) | ~l1_struct_0(D_76) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_73), u1_struct_0(B_74)))) | ~v1_funct_2(C_75, u1_struct_0(A_73), u1_struct_0(B_74)) | ~v1_funct_1(C_75) | ~l1_struct_0(B_74) | ~l1_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.76/1.86  tff(c_181, plain, (![D_219]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_219)) | ~l1_struct_0(D_219))), inference(splitRight, [status(thm)], [c_164])).
% 4.76/1.86  tff(c_301, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_3', '#skF_4', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_292])).
% 4.76/1.86  tff(c_219, plain, (![A_247, B_248, C_249, D_250]: (k2_partfun1(u1_struct_0(A_247), u1_struct_0(B_248), C_249, u1_struct_0(D_250))=k2_tmap_1(A_247, B_248, C_249, D_250) | ~m1_pre_topc(D_250, A_247) | ~m1_subset_1(C_249, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_247), u1_struct_0(B_248)))) | ~v1_funct_2(C_249, u1_struct_0(A_247), u1_struct_0(B_248)) | ~v1_funct_1(C_249) | ~l1_pre_topc(B_248) | ~v2_pre_topc(B_248) | v2_struct_0(B_248) | ~l1_pre_topc(A_247) | ~v2_pre_topc(A_247) | v2_struct_0(A_247))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.76/1.86  tff(c_225, plain, (![D_250]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_250))=k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_250) | ~m1_pre_topc(D_250, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_219])).
% 4.76/1.86  tff(c_230, plain, (![D_250]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_250))=k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_250) | ~m1_pre_topc(D_250, '#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_87, c_66, c_64, c_58, c_56, c_225])).
% 4.76/1.86  tff(c_231, plain, (![D_250]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_250))=k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_250) | ~m1_pre_topc(D_250, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_62, c_68, c_230])).
% 4.76/1.86  tff(c_327, plain, (k3_tmap_1('#skF_3', '#skF_3', '#skF_4', '#skF_4', '#skF_5')=k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_301, c_231])).
% 4.76/1.86  tff(c_334, plain, (k3_tmap_1('#skF_3', '#skF_3', '#skF_4', '#skF_4', '#skF_5')=k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_302, c_327])).
% 4.76/1.86  tff(c_338, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0('#skF_4'))=k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_334, c_301])).
% 4.76/1.86  tff(c_282, plain, (![A_263, D_265]: (k3_tmap_1(A_263, '#skF_3', '#skF_4', D_265, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_265)) | ~m1_pre_topc(D_265, '#skF_4') | ~m1_pre_topc(D_265, A_263) | ~m1_pre_topc('#skF_4', A_263) | ~l1_pre_topc(A_263) | ~v2_pre_topc(A_263) | v2_struct_0(A_263))), inference(negUnitSimplification, [status(thm)], [c_68, c_281])).
% 4.76/1.86  tff(c_304, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_4', '#skF_3', '#skF_4', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_302, c_282])).
% 4.76/1.86  tff(c_315, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_4', '#skF_3', '#skF_4', '#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_87, c_302, c_304])).
% 4.76/1.86  tff(c_316, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_4', '#skF_3', '#skF_4', '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_62, c_315])).
% 4.76/1.86  tff(c_390, plain, (k3_tmap_1('#skF_4', '#skF_3', '#skF_4', '#skF_4', '#skF_5')=k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_338, c_316])).
% 4.76/1.86  tff(c_241, plain, (![C_252, B_253, D_254, A_255]: (r2_funct_2(u1_struct_0(C_252), u1_struct_0(B_253), D_254, k3_tmap_1(A_255, B_253, C_252, C_252, D_254)) | ~m1_subset_1(D_254, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_252), u1_struct_0(B_253)))) | ~v1_funct_2(D_254, u1_struct_0(C_252), u1_struct_0(B_253)) | ~v1_funct_1(D_254) | ~m1_pre_topc(C_252, A_255) | v2_struct_0(C_252) | ~l1_pre_topc(B_253) | ~v2_pre_topc(B_253) | v2_struct_0(B_253) | ~l1_pre_topc(A_255) | ~v2_pre_topc(A_255) | v2_struct_0(A_255))), inference(cnfTransformation, [status(thm)], [f_266])).
% 4.76/1.86  tff(c_247, plain, (![A_255]: (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k3_tmap_1(A_255, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_255) | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_255) | ~v2_pre_topc(A_255) | v2_struct_0(A_255))), inference(resolution, [status(thm)], [c_54, c_241])).
% 4.76/1.86  tff(c_252, plain, (![A_255]: (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k3_tmap_1(A_255, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_255) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_255) | ~v2_pre_topc(A_255) | v2_struct_0(A_255))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_56, c_247])).
% 4.76/1.86  tff(c_254, plain, (![A_256]: (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k3_tmap_1(A_256, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_256) | ~l1_pre_topc(A_256) | ~v2_pre_topc(A_256) | v2_struct_0(A_256))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_252])).
% 4.76/1.86  tff(c_10, plain, (![D_12, C_11, A_9, B_10]: (D_12=C_11 | ~r2_funct_2(A_9, B_10, C_11, D_12) | ~m1_subset_1(D_12, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))) | ~v1_funct_2(D_12, A_9, B_10) | ~v1_funct_1(D_12) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))) | ~v1_funct_2(C_11, A_9, B_10) | ~v1_funct_1(C_11))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.76/1.86  tff(c_256, plain, (![A_256]: (k3_tmap_1(A_256, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~m1_subset_1(k3_tmap_1(A_256, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k3_tmap_1(A_256, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k3_tmap_1(A_256, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_256) | ~l1_pre_topc(A_256) | ~v2_pre_topc(A_256) | v2_struct_0(A_256))), inference(resolution, [status(thm)], [c_254, c_10])).
% 4.76/1.86  tff(c_259, plain, (![A_256]: (k3_tmap_1(A_256, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~m1_subset_1(k3_tmap_1(A_256, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k3_tmap_1(A_256, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k3_tmap_1(A_256, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_256) | ~l1_pre_topc(A_256) | ~v2_pre_topc(A_256) | v2_struct_0(A_256))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_256])).
% 4.76/1.86  tff(c_394, plain, (k3_tmap_1('#skF_4', '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k3_tmap_1('#skF_4', '#skF_3', '#skF_4', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k3_tmap_1('#skF_4', '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_390, c_259])).
% 4.76/1.86  tff(c_401, plain, (k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4')='#skF_5' | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_87, c_302, c_390, c_390, c_390, c_394])).
% 4.76/1.86  tff(c_402, plain, (k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4')='#skF_5' | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_62, c_401])).
% 4.76/1.86  tff(c_456, plain, (~v1_funct_1(k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4'))), inference(splitLeft, [status(thm)], [c_402])).
% 4.76/1.86  tff(c_459, plain, (~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_181, c_456])).
% 4.76/1.86  tff(c_463, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_165, c_459])).
% 4.76/1.86  tff(c_464, plain, (~v1_funct_2(k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_402])).
% 4.76/1.86  tff(c_466, plain, (~m1_subset_1(k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(splitLeft, [status(thm)], [c_464])).
% 4.76/1.86  tff(c_469, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_24, c_466])).
% 4.76/1.86  tff(c_473, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_165, c_182, c_58, c_56, c_54, c_469])).
% 4.76/1.86  tff(c_474, plain, (~v1_funct_2(k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_464])).
% 4.76/1.86  tff(c_538, plain, (~v1_funct_2(k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_474])).
% 4.76/1.86  tff(c_541, plain, (~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_193, c_538])).
% 4.76/1.86  tff(c_545, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_165, c_541])).
% 4.76/1.86  tff(c_546, plain, (k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_474])).
% 4.76/1.86  tff(c_476, plain, (![B_278, A_275, E_279, D_277, C_276]: (m1_subset_1('#skF_2'(A_275, C_276, D_277, B_278, E_279), u1_struct_0(B_278)) | r2_funct_2(u1_struct_0(C_276), u1_struct_0(A_275), k2_tmap_1(B_278, A_275, D_277, C_276), E_279) | ~m1_subset_1(E_279, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_276), u1_struct_0(A_275)))) | ~v1_funct_2(E_279, u1_struct_0(C_276), u1_struct_0(A_275)) | ~v1_funct_1(E_279) | ~m1_subset_1(D_277, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_278), u1_struct_0(A_275)))) | ~v1_funct_2(D_277, u1_struct_0(B_278), u1_struct_0(A_275)) | ~v1_funct_1(D_277) | ~m1_pre_topc(C_276, B_278) | v2_struct_0(C_276) | ~l1_pre_topc(B_278) | ~v2_pre_topc(B_278) | v2_struct_0(B_278) | ~l1_pre_topc(A_275) | ~v2_pre_topc(A_275) | v2_struct_0(A_275))), inference(cnfTransformation, [status(thm)], [f_236])).
% 4.76/1.86  tff(c_895, plain, (![A_325, B_326, D_327, B_328]: (m1_subset_1('#skF_2'(A_325, B_326, D_327, B_328, k4_tmap_1(A_325, B_326)), u1_struct_0(B_328)) | r2_funct_2(u1_struct_0(B_326), u1_struct_0(A_325), k2_tmap_1(B_328, A_325, D_327, B_326), k4_tmap_1(A_325, B_326)) | ~v1_funct_2(k4_tmap_1(A_325, B_326), u1_struct_0(B_326), u1_struct_0(A_325)) | ~v1_funct_1(k4_tmap_1(A_325, B_326)) | ~m1_subset_1(D_327, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_328), u1_struct_0(A_325)))) | ~v1_funct_2(D_327, u1_struct_0(B_328), u1_struct_0(A_325)) | ~v1_funct_1(D_327) | ~m1_pre_topc(B_326, B_328) | v2_struct_0(B_326) | ~l1_pre_topc(B_328) | ~v2_pre_topc(B_328) | v2_struct_0(B_328) | ~m1_pre_topc(B_326, A_325) | ~l1_pre_topc(A_325) | ~v2_pre_topc(A_325) | v2_struct_0(A_325))), inference(resolution, [status(thm)], [c_30, c_476])).
% 4.76/1.86  tff(c_904, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_546, c_895])).
% 4.76/1.86  tff(c_909, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_98, c_87, c_302, c_58, c_56, c_54, c_904])).
% 4.76/1.86  tff(c_910, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_909])).
% 4.76/1.86  tff(c_911, plain, (~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_910])).
% 4.76/1.86  tff(c_914, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_911])).
% 4.76/1.86  tff(c_917, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_914])).
% 4.76/1.86  tff(c_919, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_917])).
% 4.76/1.86  tff(c_921, plain, (v1_funct_1(k4_tmap_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_910])).
% 4.76/1.86  tff(c_32, plain, (![A_77, B_78]: (v1_funct_2(k4_tmap_1(A_77, B_78), u1_struct_0(B_78), u1_struct_0(A_77)) | ~m1_pre_topc(B_78, A_77) | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.76/1.86  tff(c_920, plain, (~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_910])).
% 4.76/1.86  tff(c_924, plain, (~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_920])).
% 4.76/1.86  tff(c_927, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_924])).
% 4.76/1.86  tff(c_930, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_927])).
% 4.76/1.86  tff(c_932, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_930])).
% 4.76/1.86  tff(c_934, plain, (v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_920])).
% 4.76/1.86  tff(c_933, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_920])).
% 4.76/1.86  tff(c_935, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_933])).
% 4.76/1.86  tff(c_937, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5' | ~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_935, c_10])).
% 4.76/1.86  tff(c_940, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5' | ~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_921, c_934, c_937])).
% 4.76/1.86  tff(c_951, plain, (~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(splitLeft, [status(thm)], [c_940])).
% 4.76/1.86  tff(c_954, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_30, c_951])).
% 4.76/1.86  tff(c_957, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_954])).
% 4.76/1.86  tff(c_959, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_957])).
% 4.76/1.86  tff(c_960, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_940])).
% 4.76/1.86  tff(c_50, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_328])).
% 4.76/1.86  tff(c_965, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_960, c_50])).
% 4.76/1.86  tff(c_971, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_129, c_965])).
% 4.76/1.86  tff(c_973, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_933])).
% 4.76/1.86  tff(c_972, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_933])).
% 4.76/1.86  tff(c_18, plain, (![C_26, A_20, B_24]: (m1_subset_1(C_26, u1_struct_0(A_20)) | ~m1_subset_1(C_26, u1_struct_0(B_24)) | ~m1_pre_topc(B_24, A_20) | v2_struct_0(B_24) | ~l1_pre_topc(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.76/1.86  tff(c_990, plain, (![A_20]: (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')), u1_struct_0(A_20)) | ~m1_pre_topc('#skF_4', A_20) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_20) | v2_struct_0(A_20))), inference(resolution, [status(thm)], [c_972, c_18])).
% 4.76/1.86  tff(c_995, plain, (![A_336]: (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')), u1_struct_0(A_336)) | ~m1_pre_topc('#skF_4', A_336) | ~l1_pre_topc(A_336) | v2_struct_0(A_336))), inference(negUnitSimplification, [status(thm)], [c_62, c_990])).
% 4.76/1.86  tff(c_1002, plain, (![A_337, A_338]: (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')), u1_struct_0(A_337)) | ~m1_pre_topc(A_338, A_337) | ~l1_pre_topc(A_337) | v2_struct_0(A_337) | ~m1_pre_topc('#skF_4', A_338) | ~l1_pre_topc(A_338) | v2_struct_0(A_338))), inference(resolution, [status(thm)], [c_995, c_18])).
% 4.76/1.86  tff(c_1008, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')), u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_60, c_1002])).
% 4.76/1.86  tff(c_1016, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')), u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_302, c_64, c_1008])).
% 4.76/1.86  tff(c_1017, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_68, c_1016])).
% 4.76/1.86  tff(c_377, plain, (![A_268, C_269, D_270, E_272, B_271]: (r2_hidden('#skF_2'(A_268, C_269, D_270, B_271, E_272), u1_struct_0(C_269)) | r2_funct_2(u1_struct_0(C_269), u1_struct_0(A_268), k2_tmap_1(B_271, A_268, D_270, C_269), E_272) | ~m1_subset_1(E_272, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_269), u1_struct_0(A_268)))) | ~v1_funct_2(E_272, u1_struct_0(C_269), u1_struct_0(A_268)) | ~v1_funct_1(E_272) | ~m1_subset_1(D_270, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_271), u1_struct_0(A_268)))) | ~v1_funct_2(D_270, u1_struct_0(B_271), u1_struct_0(A_268)) | ~v1_funct_1(D_270) | ~m1_pre_topc(C_269, B_271) | v2_struct_0(C_269) | ~l1_pre_topc(B_271) | ~v2_pre_topc(B_271) | v2_struct_0(B_271) | ~l1_pre_topc(A_268) | ~v2_pre_topc(A_268) | v2_struct_0(A_268))), inference(cnfTransformation, [status(thm)], [f_236])).
% 4.76/1.86  tff(c_1026, plain, (![A_339, B_340, D_341, B_342]: (r2_hidden('#skF_2'(A_339, B_340, D_341, B_342, k4_tmap_1(A_339, B_340)), u1_struct_0(B_340)) | r2_funct_2(u1_struct_0(B_340), u1_struct_0(A_339), k2_tmap_1(B_342, A_339, D_341, B_340), k4_tmap_1(A_339, B_340)) | ~v1_funct_2(k4_tmap_1(A_339, B_340), u1_struct_0(B_340), u1_struct_0(A_339)) | ~v1_funct_1(k4_tmap_1(A_339, B_340)) | ~m1_subset_1(D_341, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_342), u1_struct_0(A_339)))) | ~v1_funct_2(D_341, u1_struct_0(B_342), u1_struct_0(A_339)) | ~v1_funct_1(D_341) | ~m1_pre_topc(B_340, B_342) | v2_struct_0(B_340) | ~l1_pre_topc(B_342) | ~v2_pre_topc(B_342) | v2_struct_0(B_342) | ~m1_pre_topc(B_340, A_339) | ~l1_pre_topc(A_339) | ~v2_pre_topc(A_339) | v2_struct_0(A_339))), inference(resolution, [status(thm)], [c_30, c_377])).
% 4.76/1.86  tff(c_1031, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_546, c_1026])).
% 4.76/1.86  tff(c_1034, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_98, c_87, c_302, c_58, c_56, c_54, c_921, c_934, c_1031])).
% 4.76/1.86  tff(c_1035, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_973, c_1034])).
% 4.76/1.86  tff(c_52, plain, (![D_182]: (k1_funct_1('#skF_5', D_182)=D_182 | ~r2_hidden(D_182, u1_struct_0('#skF_4')) | ~m1_subset_1(D_182, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_328])).
% 4.76/1.86  tff(c_1040, plain, (k1_funct_1('#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')))='#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_1035, c_52])).
% 4.76/1.86  tff(c_1049, plain, (k1_funct_1('#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')))='#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1017, c_1040])).
% 4.76/1.86  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.76/1.86  tff(c_1050, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_1035, c_2])).
% 4.76/1.86  tff(c_6, plain, (![A_5, B_6, C_7, D_8]: (k3_funct_2(A_5, B_6, C_7, D_8)=k1_funct_1(C_7, D_8) | ~m1_subset_1(D_8, A_5) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))) | ~v1_funct_2(C_7, A_5, B_6) | ~v1_funct_1(C_7) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.76/1.86  tff(c_991, plain, (![B_6, C_7]: (k3_funct_2(u1_struct_0('#skF_4'), B_6, C_7, '#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')))=k1_funct_1(C_7, '#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'))) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), B_6))) | ~v1_funct_2(C_7, u1_struct_0('#skF_4'), B_6) | ~v1_funct_1(C_7) | v1_xboole_0(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_972, c_6])).
% 4.76/1.86  tff(c_1086, plain, (![B_346, C_347]: (k3_funct_2(u1_struct_0('#skF_4'), B_346, C_347, '#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')))=k1_funct_1(C_347, '#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'))) | ~m1_subset_1(C_347, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), B_346))) | ~v1_funct_2(C_347, u1_struct_0('#skF_4'), B_346) | ~v1_funct_1(C_347))), inference(negUnitSimplification, [status(thm)], [c_1050, c_991])).
% 4.76/1.86  tff(c_1097, plain, (k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')))=k1_funct_1('#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_1086])).
% 4.76/1.86  tff(c_1104, plain, (k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')))='#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1049, c_1097])).
% 4.76/1.86  tff(c_38, plain, (![E_140, C_128, D_136, A_80, B_112]: (k3_funct_2(u1_struct_0(B_112), u1_struct_0(A_80), D_136, '#skF_2'(A_80, C_128, D_136, B_112, E_140))!=k1_funct_1(E_140, '#skF_2'(A_80, C_128, D_136, B_112, E_140)) | r2_funct_2(u1_struct_0(C_128), u1_struct_0(A_80), k2_tmap_1(B_112, A_80, D_136, C_128), E_140) | ~m1_subset_1(E_140, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_128), u1_struct_0(A_80)))) | ~v1_funct_2(E_140, u1_struct_0(C_128), u1_struct_0(A_80)) | ~v1_funct_1(E_140) | ~m1_subset_1(D_136, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_112), u1_struct_0(A_80)))) | ~v1_funct_2(D_136, u1_struct_0(B_112), u1_struct_0(A_80)) | ~v1_funct_1(D_136) | ~m1_pre_topc(C_128, B_112) | v2_struct_0(C_128) | ~l1_pre_topc(B_112) | ~v2_pre_topc(B_112) | v2_struct_0(B_112) | ~l1_pre_topc(A_80) | ~v2_pre_topc(A_80) | v2_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_236])).
% 4.76/1.86  tff(c_1107, plain, (k1_funct_1(k4_tmap_1('#skF_3', '#skF_4'), '#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')))!='#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4'), k4_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1104, c_38])).
% 4.76/1.86  tff(c_1111, plain, (k1_funct_1(k4_tmap_1('#skF_3', '#skF_4'), '#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')))!='#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_98, c_87, c_302, c_58, c_56, c_54, c_921, c_934, c_546, c_1107])).
% 4.76/1.86  tff(c_1112, plain, (k1_funct_1(k4_tmap_1('#skF_3', '#skF_4'), '#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')))!='#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_973, c_1111])).
% 4.76/1.86  tff(c_1115, plain, (~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(splitLeft, [status(thm)], [c_1112])).
% 4.76/1.86  tff(c_1118, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_30, c_1115])).
% 4.76/1.86  tff(c_1121, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_1118])).
% 4.76/1.86  tff(c_1123, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1121])).
% 4.76/1.86  tff(c_1124, plain, (k1_funct_1(k4_tmap_1('#skF_3', '#skF_4'), '#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')))!='#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_1112])).
% 4.76/1.86  tff(c_48, plain, (![A_164, B_168, C_170]: (k1_funct_1(k4_tmap_1(A_164, B_168), C_170)=C_170 | ~r2_hidden(C_170, u1_struct_0(B_168)) | ~m1_subset_1(C_170, u1_struct_0(A_164)) | ~m1_pre_topc(B_168, A_164) | v2_struct_0(B_168) | ~l1_pre_topc(A_164) | ~v2_pre_topc(A_164) | v2_struct_0(A_164))), inference(cnfTransformation, [status(thm)], [f_298])).
% 4.76/1.86  tff(c_1037, plain, (![A_164]: (k1_funct_1(k4_tmap_1(A_164, '#skF_4'), '#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')))='#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')), u1_struct_0(A_164)) | ~m1_pre_topc('#skF_4', A_164) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_164) | ~v2_pre_topc(A_164) | v2_struct_0(A_164))), inference(resolution, [status(thm)], [c_1035, c_48])).
% 4.76/1.86  tff(c_1453, plain, (![A_374]: (k1_funct_1(k4_tmap_1(A_374, '#skF_4'), '#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')))='#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')), u1_struct_0(A_374)) | ~m1_pre_topc('#skF_4', A_374) | ~l1_pre_topc(A_374) | ~v2_pre_topc(A_374) | v2_struct_0(A_374))), inference(negUnitSimplification, [status(thm)], [c_62, c_1037])).
% 4.76/1.86  tff(c_1459, plain, (k1_funct_1(k4_tmap_1('#skF_3', '#skF_4'), '#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')))='#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1017, c_1453])).
% 4.76/1.86  tff(c_1471, plain, (k1_funct_1(k4_tmap_1('#skF_3', '#skF_4'), '#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')))='#skF_2'('#skF_3', '#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_1459])).
% 4.76/1.86  tff(c_1473, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1124, c_1471])).
% 4.76/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.76/1.86  
% 4.76/1.86  Inference rules
% 4.76/1.86  ----------------------
% 4.76/1.87  #Ref     : 0
% 4.76/1.87  #Sup     : 267
% 4.76/1.87  #Fact    : 0
% 4.76/1.87  #Define  : 0
% 4.76/1.87  #Split   : 16
% 4.76/1.87  #Chain   : 0
% 4.76/1.87  #Close   : 0
% 4.76/1.87  
% 4.76/1.87  Ordering : KBO
% 4.76/1.87  
% 4.76/1.87  Simplification rules
% 4.76/1.87  ----------------------
% 4.76/1.87  #Subsume      : 27
% 4.76/1.87  #Demod        : 701
% 4.76/1.87  #Tautology    : 125
% 4.76/1.87  #SimpNegUnit  : 84
% 4.76/1.87  #BackRed      : 17
% 4.76/1.87  
% 4.76/1.87  #Partial instantiations: 0
% 4.76/1.87  #Strategies tried      : 1
% 4.76/1.87  
% 4.76/1.87  Timing (in seconds)
% 4.76/1.87  ----------------------
% 4.76/1.87  Preprocessing        : 0.40
% 4.76/1.87  Parsing              : 0.21
% 4.76/1.87  CNF conversion       : 0.04
% 4.76/1.87  Main loop            : 0.66
% 4.76/1.87  Inferencing          : 0.23
% 4.76/1.87  Reduction            : 0.22
% 4.76/1.87  Demodulation         : 0.17
% 4.76/1.87  BG Simplification    : 0.04
% 4.76/1.87  Subsumption          : 0.13
% 4.76/1.87  Abstraction          : 0.04
% 4.76/1.87  MUC search           : 0.00
% 4.76/1.87  Cooper               : 0.00
% 4.76/1.87  Total                : 1.12
% 4.76/1.87  Index Insertion      : 0.00
% 4.76/1.87  Index Deletion       : 0.00
% 4.76/1.87  Index Matching       : 0.00
% 4.76/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
