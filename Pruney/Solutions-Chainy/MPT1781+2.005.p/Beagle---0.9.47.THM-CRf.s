%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:45 EST 2020

% Result     : Theorem 10.07s
% Output     : CNFRefutation 10.32s
% Verified   : 
% Statistics : Number of formulae       :  272 (23644 expanded)
%              Number of leaves         :   43 (9309 expanded)
%              Depth                    :   38
%              Number of atoms          : 1288 (162091 expanded)
%              Number of equality atoms :   90 (11536 expanded)
%              Maximal formula depth    :   22 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_tmap_1 > k2_partfun1 > k4_tmap_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

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

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_342,negated_conjecture,(
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

tff(f_202,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_funct_1(k4_tmap_1(A,B))
        & v1_funct_2(k4_tmap_1(A,B),u1_struct_0(B),u1_struct_0(A))
        & m1_subset_1(k4_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_tmap_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_206,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_187,axiom,(
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

tff(f_280,axiom,(
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

tff(f_157,axiom,(
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

tff(f_125,axiom,(
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

tff(f_250,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_98,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => m1_subset_1(C,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_312,axiom,(
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

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_103,plain,(
    ! [D_195] :
      ( k1_funct_1('#skF_5',D_195) = D_195
      | ~ r2_hidden(D_195,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(D_195,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_342])).

tff(c_112,plain,(
    ! [A_5] :
      ( k1_funct_1('#skF_5',A_5) = A_5
      | ~ m1_subset_1(A_5,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_5,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_6,c_103])).

tff(c_115,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_342])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_342])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_342])).

tff(c_56,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_342])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_342])).

tff(c_132,plain,(
    ! [A_204,B_205,D_206] :
      ( r2_funct_2(A_204,B_205,D_206,D_206)
      | ~ m1_subset_1(D_206,k1_zfmisc_1(k2_zfmisc_1(A_204,B_205)))
      | ~ v1_funct_2(D_206,A_204,B_205)
      | ~ v1_funct_1(D_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_134,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5','#skF_5')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_132])).

tff(c_137,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_134])).

tff(c_66,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_342])).

tff(c_64,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_342])).

tff(c_60,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_342])).

tff(c_30,plain,(
    ! [A_79,B_80] :
      ( m1_subset_1(k4_tmap_1(A_79,B_80),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_80),u1_struct_0(A_79))))
      | ~ m1_pre_topc(B_80,A_79)
      | ~ l1_pre_topc(A_79)
      | ~ v2_pre_topc(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_34,plain,(
    ! [A_79,B_80] :
      ( v1_funct_1(k4_tmap_1(A_79,B_80))
      | ~ m1_pre_topc(B_80,A_79)
      | ~ l1_pre_topc(A_79)
      | ~ v2_pre_topc(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_92,plain,(
    ! [B_193,A_194] :
      ( v2_pre_topc(B_193)
      | ~ m1_pre_topc(B_193,A_194)
      | ~ l1_pre_topc(A_194)
      | ~ v2_pre_topc(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_98,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_92])).

tff(c_102,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_98])).

tff(c_76,plain,(
    ! [B_189,A_190] :
      ( l1_pre_topc(B_189)
      | ~ m1_pre_topc(B_189,A_190)
      | ~ l1_pre_topc(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_82,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_76])).

tff(c_86,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_82])).

tff(c_36,plain,(
    ! [A_81] :
      ( m1_pre_topc(A_81,A_81)
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_174,plain,(
    ! [B_234,A_233,C_231,E_232,D_230] :
      ( v1_funct_1(k3_tmap_1(A_233,B_234,C_231,D_230,E_232))
      | ~ m1_subset_1(E_232,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_231),u1_struct_0(B_234))))
      | ~ v1_funct_2(E_232,u1_struct_0(C_231),u1_struct_0(B_234))
      | ~ v1_funct_1(E_232)
      | ~ m1_pre_topc(D_230,A_233)
      | ~ m1_pre_topc(C_231,A_233)
      | ~ l1_pre_topc(B_234)
      | ~ v2_pre_topc(B_234)
      | v2_struct_0(B_234)
      | ~ l1_pre_topc(A_233)
      | ~ v2_pre_topc(A_233)
      | v2_struct_0(A_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_178,plain,(
    ! [A_233,D_230] :
      ( v1_funct_1(k3_tmap_1(A_233,'#skF_3','#skF_4',D_230,'#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_230,A_233)
      | ~ m1_pre_topc('#skF_4',A_233)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_233)
      | ~ v2_pre_topc(A_233)
      | v2_struct_0(A_233) ) ),
    inference(resolution,[status(thm)],[c_54,c_174])).

tff(c_182,plain,(
    ! [A_233,D_230] :
      ( v1_funct_1(k3_tmap_1(A_233,'#skF_3','#skF_4',D_230,'#skF_5'))
      | ~ m1_pre_topc(D_230,A_233)
      | ~ m1_pre_topc('#skF_4',A_233)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_233)
      | ~ v2_pre_topc(A_233)
      | v2_struct_0(A_233) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_56,c_178])).

tff(c_183,plain,(
    ! [A_233,D_230] :
      ( v1_funct_1(k3_tmap_1(A_233,'#skF_3','#skF_4',D_230,'#skF_5'))
      | ~ m1_pre_topc(D_230,A_233)
      | ~ m1_pre_topc('#skF_4',A_233)
      | ~ l1_pre_topc(A_233)
      | ~ v2_pre_topc(A_233)
      | v2_struct_0(A_233) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_182])).

tff(c_210,plain,(
    ! [E_252,D_250,B_254,A_253,C_251] :
      ( v1_funct_2(k3_tmap_1(A_253,B_254,C_251,D_250,E_252),u1_struct_0(D_250),u1_struct_0(B_254))
      | ~ m1_subset_1(E_252,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_251),u1_struct_0(B_254))))
      | ~ v1_funct_2(E_252,u1_struct_0(C_251),u1_struct_0(B_254))
      | ~ v1_funct_1(E_252)
      | ~ m1_pre_topc(D_250,A_253)
      | ~ m1_pre_topc(C_251,A_253)
      | ~ l1_pre_topc(B_254)
      | ~ v2_pre_topc(B_254)
      | v2_struct_0(B_254)
      | ~ l1_pre_topc(A_253)
      | ~ v2_pre_topc(A_253)
      | v2_struct_0(A_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_214,plain,(
    ! [A_253,D_250] :
      ( v1_funct_2(k3_tmap_1(A_253,'#skF_3','#skF_4',D_250,'#skF_5'),u1_struct_0(D_250),u1_struct_0('#skF_3'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_250,A_253)
      | ~ m1_pre_topc('#skF_4',A_253)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_253)
      | ~ v2_pre_topc(A_253)
      | v2_struct_0(A_253) ) ),
    inference(resolution,[status(thm)],[c_54,c_210])).

tff(c_218,plain,(
    ! [A_253,D_250] :
      ( v1_funct_2(k3_tmap_1(A_253,'#skF_3','#skF_4',D_250,'#skF_5'),u1_struct_0(D_250),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_250,A_253)
      | ~ m1_pre_topc('#skF_4',A_253)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_253)
      | ~ v2_pre_topc(A_253)
      | v2_struct_0(A_253) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_56,c_214])).

tff(c_219,plain,(
    ! [A_253,D_250] :
      ( v1_funct_2(k3_tmap_1(A_253,'#skF_3','#skF_4',D_250,'#skF_5'),u1_struct_0(D_250),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_250,A_253)
      | ~ m1_pre_topc('#skF_4',A_253)
      | ~ l1_pre_topc(A_253)
      | ~ v2_pre_topc(A_253)
      | v2_struct_0(A_253) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_218])).

tff(c_24,plain,(
    ! [A_74,D_77,B_75,C_76,E_78] :
      ( m1_subset_1(k3_tmap_1(A_74,B_75,C_76,D_77,E_78),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_77),u1_struct_0(B_75))))
      | ~ m1_subset_1(E_78,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_76),u1_struct_0(B_75))))
      | ~ v1_funct_2(E_78,u1_struct_0(C_76),u1_struct_0(B_75))
      | ~ v1_funct_1(E_78)
      | ~ m1_pre_topc(D_77,A_74)
      | ~ m1_pre_topc(C_76,A_74)
      | ~ l1_pre_topc(B_75)
      | ~ v2_pre_topc(B_75)
      | v2_struct_0(B_75)
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_221,plain,(
    ! [C_257,B_258,D_259,A_260] :
      ( r2_funct_2(u1_struct_0(C_257),u1_struct_0(B_258),D_259,k3_tmap_1(A_260,B_258,C_257,C_257,D_259))
      | ~ m1_subset_1(D_259,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_257),u1_struct_0(B_258))))
      | ~ v1_funct_2(D_259,u1_struct_0(C_257),u1_struct_0(B_258))
      | ~ v1_funct_1(D_259)
      | ~ m1_pre_topc(C_257,A_260)
      | v2_struct_0(C_257)
      | ~ l1_pre_topc(B_258)
      | ~ v2_pre_topc(B_258)
      | v2_struct_0(B_258)
      | ~ l1_pre_topc(A_260)
      | ~ v2_pre_topc(A_260)
      | v2_struct_0(A_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_280])).

tff(c_225,plain,(
    ! [A_260] :
      ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k3_tmap_1(A_260,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_260)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_260)
      | ~ v2_pre_topc(A_260)
      | v2_struct_0(A_260) ) ),
    inference(resolution,[status(thm)],[c_54,c_221])).

tff(c_229,plain,(
    ! [A_260] :
      ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k3_tmap_1(A_260,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_260)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_260)
      | ~ v2_pre_topc(A_260)
      | v2_struct_0(A_260) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_56,c_225])).

tff(c_231,plain,(
    ! [A_261] :
      ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k3_tmap_1(A_261,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_261)
      | ~ l1_pre_topc(A_261)
      | ~ v2_pre_topc(A_261)
      | v2_struct_0(A_261) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_229])).

tff(c_12,plain,(
    ! [D_14,C_13,A_11,B_12] :
      ( D_14 = C_13
      | ~ r2_funct_2(A_11,B_12,C_13,D_14)
      | ~ m1_subset_1(D_14,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12)))
      | ~ v1_funct_2(D_14,A_11,B_12)
      | ~ v1_funct_1(D_14)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12)))
      | ~ v1_funct_2(C_13,A_11,B_12)
      | ~ v1_funct_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_233,plain,(
    ! [A_261] :
      ( k3_tmap_1(A_261,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ m1_subset_1(k3_tmap_1(A_261,'#skF_3','#skF_4','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(k3_tmap_1(A_261,'#skF_3','#skF_4','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k3_tmap_1(A_261,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_261)
      | ~ l1_pre_topc(A_261)
      | ~ v2_pre_topc(A_261)
      | v2_struct_0(A_261) ) ),
    inference(resolution,[status(thm)],[c_231,c_12])).

tff(c_257,plain,(
    ! [A_271] :
      ( k3_tmap_1(A_271,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ m1_subset_1(k3_tmap_1(A_271,'#skF_3','#skF_4','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(k3_tmap_1(A_271,'#skF_3','#skF_4','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k3_tmap_1(A_271,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_271)
      | ~ l1_pre_topc(A_271)
      | ~ v2_pre_topc(A_271)
      | v2_struct_0(A_271) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_233])).

tff(c_261,plain,(
    ! [A_74] :
      ( k3_tmap_1(A_74,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ v1_funct_2(k3_tmap_1(A_74,'#skF_3','#skF_4','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k3_tmap_1(A_74,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_74)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74)
      | v2_struct_0(A_74) ) ),
    inference(resolution,[status(thm)],[c_24,c_257])).

tff(c_264,plain,(
    ! [A_74] :
      ( k3_tmap_1(A_74,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ v1_funct_2(k3_tmap_1(A_74,'#skF_3','#skF_4','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k3_tmap_1(A_74,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_74)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74)
      | v2_struct_0(A_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_56,c_54,c_261])).

tff(c_266,plain,(
    ! [A_272] :
      ( k3_tmap_1(A_272,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ v1_funct_2(k3_tmap_1(A_272,'#skF_3','#skF_4','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k3_tmap_1(A_272,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_272)
      | ~ l1_pre_topc(A_272)
      | ~ v2_pre_topc(A_272)
      | v2_struct_0(A_272) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_264])).

tff(c_272,plain,(
    ! [A_273] :
      ( k3_tmap_1(A_273,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ v1_funct_1(k3_tmap_1(A_273,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_273)
      | ~ l1_pre_topc(A_273)
      | ~ v2_pre_topc(A_273)
      | v2_struct_0(A_273) ) ),
    inference(resolution,[status(thm)],[c_219,c_266])).

tff(c_278,plain,(
    ! [A_274] :
      ( k3_tmap_1(A_274,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ m1_pre_topc('#skF_4',A_274)
      | ~ l1_pre_topc(A_274)
      | ~ v2_pre_topc(A_274)
      | v2_struct_0(A_274) ) ),
    inference(resolution,[status(thm)],[c_183,c_272])).

tff(c_285,plain,
    ( k3_tmap_1('#skF_3','#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_278])).

tff(c_292,plain,
    ( k3_tmap_1('#skF_3','#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_285])).

tff(c_293,plain,(
    k3_tmap_1('#skF_3','#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_292])).

tff(c_350,plain,(
    ! [C_277,A_278,B_275,D_276,E_279] :
      ( k3_tmap_1(A_278,B_275,C_277,D_276,E_279) = k2_partfun1(u1_struct_0(C_277),u1_struct_0(B_275),E_279,u1_struct_0(D_276))
      | ~ m1_pre_topc(D_276,C_277)
      | ~ m1_subset_1(E_279,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_277),u1_struct_0(B_275))))
      | ~ v1_funct_2(E_279,u1_struct_0(C_277),u1_struct_0(B_275))
      | ~ v1_funct_1(E_279)
      | ~ m1_pre_topc(D_276,A_278)
      | ~ m1_pre_topc(C_277,A_278)
      | ~ l1_pre_topc(B_275)
      | ~ v2_pre_topc(B_275)
      | v2_struct_0(B_275)
      | ~ l1_pre_topc(A_278)
      | ~ v2_pre_topc(A_278)
      | v2_struct_0(A_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_356,plain,(
    ! [A_278,D_276] :
      ( k3_tmap_1(A_278,'#skF_3','#skF_4',D_276,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_276))
      | ~ m1_pre_topc(D_276,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_276,A_278)
      | ~ m1_pre_topc('#skF_4',A_278)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_278)
      | ~ v2_pre_topc(A_278)
      | v2_struct_0(A_278) ) ),
    inference(resolution,[status(thm)],[c_54,c_350])).

tff(c_361,plain,(
    ! [A_278,D_276] :
      ( k3_tmap_1(A_278,'#skF_3','#skF_4',D_276,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_276))
      | ~ m1_pre_topc(D_276,'#skF_4')
      | ~ m1_pre_topc(D_276,A_278)
      | ~ m1_pre_topc('#skF_4',A_278)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_278)
      | ~ v2_pre_topc(A_278)
      | v2_struct_0(A_278) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_56,c_356])).

tff(c_363,plain,(
    ! [A_280,D_281] :
      ( k3_tmap_1(A_280,'#skF_3','#skF_4',D_281,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_281))
      | ~ m1_pre_topc(D_281,'#skF_4')
      | ~ m1_pre_topc(D_281,A_280)
      | ~ m1_pre_topc('#skF_4',A_280)
      | ~ l1_pre_topc(A_280)
      | ~ v2_pre_topc(A_280)
      | v2_struct_0(A_280) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_361])).

tff(c_367,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_3','#skF_4','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_363])).

tff(c_371,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0('#skF_4')) = '#skF_5'
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_293,c_367])).

tff(c_372,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0('#skF_4')) = '#skF_5'
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_371])).

tff(c_373,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_372])).

tff(c_376,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_373])).

tff(c_380,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_376])).

tff(c_382,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_372])).

tff(c_381,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0('#skF_4')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_372])).

tff(c_191,plain,(
    ! [A_245,B_246,C_247,D_248] :
      ( k2_partfun1(u1_struct_0(A_245),u1_struct_0(B_246),C_247,u1_struct_0(D_248)) = k2_tmap_1(A_245,B_246,C_247,D_248)
      | ~ m1_pre_topc(D_248,A_245)
      | ~ m1_subset_1(C_247,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_245),u1_struct_0(B_246))))
      | ~ v1_funct_2(C_247,u1_struct_0(A_245),u1_struct_0(B_246))
      | ~ v1_funct_1(C_247)
      | ~ l1_pre_topc(B_246)
      | ~ v2_pre_topc(B_246)
      | v2_struct_0(B_246)
      | ~ l1_pre_topc(A_245)
      | ~ v2_pre_topc(A_245)
      | v2_struct_0(A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_195,plain,(
    ! [D_248] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_248)) = k2_tmap_1('#skF_4','#skF_3','#skF_5',D_248)
      | ~ m1_pre_topc(D_248,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_191])).

tff(c_199,plain,(
    ! [D_248] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_248)) = k2_tmap_1('#skF_4','#skF_3','#skF_5',D_248)
      | ~ m1_pre_topc(D_248,'#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_86,c_66,c_64,c_58,c_56,c_195])).

tff(c_200,plain,(
    ! [D_248] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_248)) = k2_tmap_1('#skF_4','#skF_3','#skF_5',D_248)
      | ~ m1_pre_topc(D_248,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_68,c_199])).

tff(c_414,plain,
    ( k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4') = '#skF_5'
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_381,c_200])).

tff(c_421,plain,(
    k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_414])).

tff(c_478,plain,(
    ! [D_284,E_286,C_285,A_287,B_283] :
      ( m1_subset_1('#skF_2'(B_283,D_284,C_285,E_286,A_287),u1_struct_0(B_283))
      | r2_funct_2(u1_struct_0(C_285),u1_struct_0(A_287),k2_tmap_1(B_283,A_287,D_284,C_285),E_286)
      | ~ m1_subset_1(E_286,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_285),u1_struct_0(A_287))))
      | ~ v1_funct_2(E_286,u1_struct_0(C_285),u1_struct_0(A_287))
      | ~ v1_funct_1(E_286)
      | ~ m1_subset_1(D_284,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_283),u1_struct_0(A_287))))
      | ~ v1_funct_2(D_284,u1_struct_0(B_283),u1_struct_0(A_287))
      | ~ v1_funct_1(D_284)
      | ~ m1_pre_topc(C_285,B_283)
      | v2_struct_0(C_285)
      | ~ l1_pre_topc(B_283)
      | ~ v2_pre_topc(B_283)
      | v2_struct_0(B_283)
      | ~ l1_pre_topc(A_287)
      | ~ v2_pre_topc(A_287)
      | v2_struct_0(A_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_1224,plain,(
    ! [B_362,D_363,B_364,A_365] :
      ( m1_subset_1('#skF_2'(B_362,D_363,B_364,k4_tmap_1(A_365,B_364),A_365),u1_struct_0(B_362))
      | r2_funct_2(u1_struct_0(B_364),u1_struct_0(A_365),k2_tmap_1(B_362,A_365,D_363,B_364),k4_tmap_1(A_365,B_364))
      | ~ v1_funct_2(k4_tmap_1(A_365,B_364),u1_struct_0(B_364),u1_struct_0(A_365))
      | ~ v1_funct_1(k4_tmap_1(A_365,B_364))
      | ~ m1_subset_1(D_363,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_362),u1_struct_0(A_365))))
      | ~ v1_funct_2(D_363,u1_struct_0(B_362),u1_struct_0(A_365))
      | ~ v1_funct_1(D_363)
      | ~ m1_pre_topc(B_364,B_362)
      | v2_struct_0(B_364)
      | ~ l1_pre_topc(B_362)
      | ~ v2_pre_topc(B_362)
      | v2_struct_0(B_362)
      | ~ m1_pre_topc(B_364,A_365)
      | ~ l1_pre_topc(A_365)
      | ~ v2_pre_topc(A_365)
      | v2_struct_0(A_365) ) ),
    inference(resolution,[status(thm)],[c_30,c_478])).

tff(c_1235,plain,
    ( m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3'),u1_struct_0('#skF_4'))
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
    inference(superposition,[status(thm),theory(equality)],[c_421,c_1224])).

tff(c_1241,plain,
    ( m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3'),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_102,c_86,c_382,c_58,c_56,c_54,c_1235])).

tff(c_1242,plain,
    ( m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3'),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_1241])).

tff(c_1243,plain,(
    ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1242])).

tff(c_1246,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_1243])).

tff(c_1249,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_1246])).

tff(c_1251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1249])).

tff(c_1253,plain,(
    v1_funct_1(k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1242])).

tff(c_32,plain,(
    ! [A_79,B_80] :
      ( v1_funct_2(k4_tmap_1(A_79,B_80),u1_struct_0(B_80),u1_struct_0(A_79))
      | ~ m1_pre_topc(B_80,A_79)
      | ~ l1_pre_topc(A_79)
      | ~ v2_pre_topc(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_1252,plain,
    ( ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1242])).

tff(c_1272,plain,(
    ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1252])).

tff(c_1275,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_1272])).

tff(c_1278,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_1275])).

tff(c_1280,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1278])).

tff(c_1282,plain,(
    v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1252])).

tff(c_1281,plain,
    ( m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3'),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1252])).

tff(c_1283,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1281])).

tff(c_1285,plain,
    ( k4_tmap_1('#skF_3','#skF_4') = '#skF_5'
    | ~ m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1283,c_12])).

tff(c_1288,plain,
    ( k4_tmap_1('#skF_3','#skF_4') = '#skF_5'
    | ~ m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_1253,c_1282,c_1285])).

tff(c_1299,plain,(
    ~ m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_1288])).

tff(c_1302,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_1299])).

tff(c_1305,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_1302])).

tff(c_1307,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1305])).

tff(c_1308,plain,(
    k4_tmap_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1288])).

tff(c_50,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_342])).

tff(c_1313,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1308,c_50])).

tff(c_1319,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_1313])).

tff(c_1321,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1281])).

tff(c_676,plain,(
    ! [C_299,B_297,E_300,A_301,D_298] :
      ( r2_hidden('#skF_2'(B_297,D_298,C_299,E_300,A_301),u1_struct_0(C_299))
      | r2_funct_2(u1_struct_0(C_299),u1_struct_0(A_301),k2_tmap_1(B_297,A_301,D_298,C_299),E_300)
      | ~ m1_subset_1(E_300,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_299),u1_struct_0(A_301))))
      | ~ v1_funct_2(E_300,u1_struct_0(C_299),u1_struct_0(A_301))
      | ~ v1_funct_1(E_300)
      | ~ m1_subset_1(D_298,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_297),u1_struct_0(A_301))))
      | ~ v1_funct_2(D_298,u1_struct_0(B_297),u1_struct_0(A_301))
      | ~ v1_funct_1(D_298)
      | ~ m1_pre_topc(C_299,B_297)
      | v2_struct_0(C_299)
      | ~ l1_pre_topc(B_297)
      | ~ v2_pre_topc(B_297)
      | v2_struct_0(B_297)
      | ~ l1_pre_topc(A_301)
      | ~ v2_pre_topc(A_301)
      | v2_struct_0(A_301) ) ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_1393,plain,(
    ! [B_377,D_378,B_379,A_380] :
      ( r2_hidden('#skF_2'(B_377,D_378,B_379,k4_tmap_1(A_380,B_379),A_380),u1_struct_0(B_379))
      | r2_funct_2(u1_struct_0(B_379),u1_struct_0(A_380),k2_tmap_1(B_377,A_380,D_378,B_379),k4_tmap_1(A_380,B_379))
      | ~ v1_funct_2(k4_tmap_1(A_380,B_379),u1_struct_0(B_379),u1_struct_0(A_380))
      | ~ v1_funct_1(k4_tmap_1(A_380,B_379))
      | ~ m1_subset_1(D_378,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_377),u1_struct_0(A_380))))
      | ~ v1_funct_2(D_378,u1_struct_0(B_377),u1_struct_0(A_380))
      | ~ v1_funct_1(D_378)
      | ~ m1_pre_topc(B_379,B_377)
      | v2_struct_0(B_379)
      | ~ l1_pre_topc(B_377)
      | ~ v2_pre_topc(B_377)
      | v2_struct_0(B_377)
      | ~ m1_pre_topc(B_379,A_380)
      | ~ l1_pre_topc(A_380)
      | ~ v2_pre_topc(A_380)
      | v2_struct_0(A_380) ) ),
    inference(resolution,[status(thm)],[c_30,c_676])).

tff(c_1398,plain,
    ( r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3'),u1_struct_0('#skF_4'))
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
    inference(superposition,[status(thm),theory(equality)],[c_421,c_1393])).

tff(c_1401,plain,
    ( r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3'),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_102,c_86,c_382,c_58,c_56,c_54,c_1253,c_1282,c_1398])).

tff(c_1402,plain,(
    r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_1321,c_1401])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1410,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1402,c_2])).

tff(c_1420,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_1410])).

tff(c_1422,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_1441,plain,(
    ! [A_386,B_387,D_388] :
      ( r2_funct_2(A_386,B_387,D_388,D_388)
      | ~ m1_subset_1(D_388,k1_zfmisc_1(k2_zfmisc_1(A_386,B_387)))
      | ~ v1_funct_2(D_388,A_386,B_387)
      | ~ v1_funct_1(D_388) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1443,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5','#skF_5')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_1441])).

tff(c_1446,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_1443])).

tff(c_1483,plain,(
    ! [B_418,D_414,C_415,E_416,A_417] :
      ( v1_funct_1(k3_tmap_1(A_417,B_418,C_415,D_414,E_416))
      | ~ m1_subset_1(E_416,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_415),u1_struct_0(B_418))))
      | ~ v1_funct_2(E_416,u1_struct_0(C_415),u1_struct_0(B_418))
      | ~ v1_funct_1(E_416)
      | ~ m1_pre_topc(D_414,A_417)
      | ~ m1_pre_topc(C_415,A_417)
      | ~ l1_pre_topc(B_418)
      | ~ v2_pre_topc(B_418)
      | v2_struct_0(B_418)
      | ~ l1_pre_topc(A_417)
      | ~ v2_pre_topc(A_417)
      | v2_struct_0(A_417) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_1487,plain,(
    ! [A_417,D_414] :
      ( v1_funct_1(k3_tmap_1(A_417,'#skF_3','#skF_4',D_414,'#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_414,A_417)
      | ~ m1_pre_topc('#skF_4',A_417)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_417)
      | ~ v2_pre_topc(A_417)
      | v2_struct_0(A_417) ) ),
    inference(resolution,[status(thm)],[c_54,c_1483])).

tff(c_1491,plain,(
    ! [A_417,D_414] :
      ( v1_funct_1(k3_tmap_1(A_417,'#skF_3','#skF_4',D_414,'#skF_5'))
      | ~ m1_pre_topc(D_414,A_417)
      | ~ m1_pre_topc('#skF_4',A_417)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_417)
      | ~ v2_pre_topc(A_417)
      | v2_struct_0(A_417) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_56,c_1487])).

tff(c_1492,plain,(
    ! [A_417,D_414] :
      ( v1_funct_1(k3_tmap_1(A_417,'#skF_3','#skF_4',D_414,'#skF_5'))
      | ~ m1_pre_topc(D_414,A_417)
      | ~ m1_pre_topc('#skF_4',A_417)
      | ~ l1_pre_topc(A_417)
      | ~ v2_pre_topc(A_417)
      | v2_struct_0(A_417) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1491])).

tff(c_1535,plain,(
    ! [D_439,E_441,A_442,B_443,C_440] :
      ( v1_funct_2(k3_tmap_1(A_442,B_443,C_440,D_439,E_441),u1_struct_0(D_439),u1_struct_0(B_443))
      | ~ m1_subset_1(E_441,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_440),u1_struct_0(B_443))))
      | ~ v1_funct_2(E_441,u1_struct_0(C_440),u1_struct_0(B_443))
      | ~ v1_funct_1(E_441)
      | ~ m1_pre_topc(D_439,A_442)
      | ~ m1_pre_topc(C_440,A_442)
      | ~ l1_pre_topc(B_443)
      | ~ v2_pre_topc(B_443)
      | v2_struct_0(B_443)
      | ~ l1_pre_topc(A_442)
      | ~ v2_pre_topc(A_442)
      | v2_struct_0(A_442) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_1539,plain,(
    ! [A_442,D_439] :
      ( v1_funct_2(k3_tmap_1(A_442,'#skF_3','#skF_4',D_439,'#skF_5'),u1_struct_0(D_439),u1_struct_0('#skF_3'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_439,A_442)
      | ~ m1_pre_topc('#skF_4',A_442)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_442)
      | ~ v2_pre_topc(A_442)
      | v2_struct_0(A_442) ) ),
    inference(resolution,[status(thm)],[c_54,c_1535])).

tff(c_1543,plain,(
    ! [A_442,D_439] :
      ( v1_funct_2(k3_tmap_1(A_442,'#skF_3','#skF_4',D_439,'#skF_5'),u1_struct_0(D_439),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_439,A_442)
      | ~ m1_pre_topc('#skF_4',A_442)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_442)
      | ~ v2_pre_topc(A_442)
      | v2_struct_0(A_442) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_56,c_1539])).

tff(c_1544,plain,(
    ! [A_442,D_439] :
      ( v1_funct_2(k3_tmap_1(A_442,'#skF_3','#skF_4',D_439,'#skF_5'),u1_struct_0(D_439),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_439,A_442)
      | ~ m1_pre_topc('#skF_4',A_442)
      | ~ l1_pre_topc(A_442)
      | ~ v2_pre_topc(A_442)
      | v2_struct_0(A_442) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1543])).

tff(c_1519,plain,(
    ! [C_434,B_435,D_436,A_437] :
      ( r2_funct_2(u1_struct_0(C_434),u1_struct_0(B_435),D_436,k3_tmap_1(A_437,B_435,C_434,C_434,D_436))
      | ~ m1_subset_1(D_436,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_434),u1_struct_0(B_435))))
      | ~ v1_funct_2(D_436,u1_struct_0(C_434),u1_struct_0(B_435))
      | ~ v1_funct_1(D_436)
      | ~ m1_pre_topc(C_434,A_437)
      | v2_struct_0(C_434)
      | ~ l1_pre_topc(B_435)
      | ~ v2_pre_topc(B_435)
      | v2_struct_0(B_435)
      | ~ l1_pre_topc(A_437)
      | ~ v2_pre_topc(A_437)
      | v2_struct_0(A_437) ) ),
    inference(cnfTransformation,[status(thm)],[f_280])).

tff(c_1523,plain,(
    ! [A_437] :
      ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k3_tmap_1(A_437,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_437)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_437)
      | ~ v2_pre_topc(A_437)
      | v2_struct_0(A_437) ) ),
    inference(resolution,[status(thm)],[c_54,c_1519])).

tff(c_1527,plain,(
    ! [A_437] :
      ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k3_tmap_1(A_437,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_437)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_437)
      | ~ v2_pre_topc(A_437)
      | v2_struct_0(A_437) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_56,c_1523])).

tff(c_1529,plain,(
    ! [A_438] :
      ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k3_tmap_1(A_438,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_438)
      | ~ l1_pre_topc(A_438)
      | ~ v2_pre_topc(A_438)
      | v2_struct_0(A_438) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_1527])).

tff(c_1531,plain,(
    ! [A_438] :
      ( k3_tmap_1(A_438,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ m1_subset_1(k3_tmap_1(A_438,'#skF_3','#skF_4','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(k3_tmap_1(A_438,'#skF_3','#skF_4','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k3_tmap_1(A_438,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_438)
      | ~ l1_pre_topc(A_438)
      | ~ v2_pre_topc(A_438)
      | v2_struct_0(A_438) ) ),
    inference(resolution,[status(thm)],[c_1529,c_12])).

tff(c_1575,plain,(
    ! [A_458] :
      ( k3_tmap_1(A_458,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ m1_subset_1(k3_tmap_1(A_458,'#skF_3','#skF_4','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(k3_tmap_1(A_458,'#skF_3','#skF_4','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k3_tmap_1(A_458,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_458)
      | ~ l1_pre_topc(A_458)
      | ~ v2_pre_topc(A_458)
      | v2_struct_0(A_458) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_1531])).

tff(c_1579,plain,(
    ! [A_74] :
      ( k3_tmap_1(A_74,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ v1_funct_2(k3_tmap_1(A_74,'#skF_3','#skF_4','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k3_tmap_1(A_74,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_74)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74)
      | v2_struct_0(A_74) ) ),
    inference(resolution,[status(thm)],[c_24,c_1575])).

tff(c_1582,plain,(
    ! [A_74] :
      ( k3_tmap_1(A_74,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ v1_funct_2(k3_tmap_1(A_74,'#skF_3','#skF_4','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k3_tmap_1(A_74,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_74)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74)
      | v2_struct_0(A_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_56,c_54,c_1579])).

tff(c_1584,plain,(
    ! [A_459] :
      ( k3_tmap_1(A_459,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ v1_funct_2(k3_tmap_1(A_459,'#skF_3','#skF_4','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k3_tmap_1(A_459,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_459)
      | ~ l1_pre_topc(A_459)
      | ~ v2_pre_topc(A_459)
      | v2_struct_0(A_459) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1582])).

tff(c_1590,plain,(
    ! [A_460] :
      ( k3_tmap_1(A_460,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ v1_funct_1(k3_tmap_1(A_460,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_460)
      | ~ l1_pre_topc(A_460)
      | ~ v2_pre_topc(A_460)
      | v2_struct_0(A_460) ) ),
    inference(resolution,[status(thm)],[c_1544,c_1584])).

tff(c_1596,plain,(
    ! [A_461] :
      ( k3_tmap_1(A_461,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ m1_pre_topc('#skF_4',A_461)
      | ~ l1_pre_topc(A_461)
      | ~ v2_pre_topc(A_461)
      | v2_struct_0(A_461) ) ),
    inference(resolution,[status(thm)],[c_1492,c_1590])).

tff(c_1603,plain,
    ( k3_tmap_1('#skF_3','#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1596])).

tff(c_1610,plain,
    ( k3_tmap_1('#skF_3','#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1603])).

tff(c_1611,plain,(
    k3_tmap_1('#skF_3','#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1610])).

tff(c_1668,plain,(
    ! [D_463,A_465,B_462,C_464,E_466] :
      ( k3_tmap_1(A_465,B_462,C_464,D_463,E_466) = k2_partfun1(u1_struct_0(C_464),u1_struct_0(B_462),E_466,u1_struct_0(D_463))
      | ~ m1_pre_topc(D_463,C_464)
      | ~ m1_subset_1(E_466,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_464),u1_struct_0(B_462))))
      | ~ v1_funct_2(E_466,u1_struct_0(C_464),u1_struct_0(B_462))
      | ~ v1_funct_1(E_466)
      | ~ m1_pre_topc(D_463,A_465)
      | ~ m1_pre_topc(C_464,A_465)
      | ~ l1_pre_topc(B_462)
      | ~ v2_pre_topc(B_462)
      | v2_struct_0(B_462)
      | ~ l1_pre_topc(A_465)
      | ~ v2_pre_topc(A_465)
      | v2_struct_0(A_465) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_1674,plain,(
    ! [A_465,D_463] :
      ( k3_tmap_1(A_465,'#skF_3','#skF_4',D_463,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_463))
      | ~ m1_pre_topc(D_463,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_463,A_465)
      | ~ m1_pre_topc('#skF_4',A_465)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_465)
      | ~ v2_pre_topc(A_465)
      | v2_struct_0(A_465) ) ),
    inference(resolution,[status(thm)],[c_54,c_1668])).

tff(c_1679,plain,(
    ! [A_465,D_463] :
      ( k3_tmap_1(A_465,'#skF_3','#skF_4',D_463,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_463))
      | ~ m1_pre_topc(D_463,'#skF_4')
      | ~ m1_pre_topc(D_463,A_465)
      | ~ m1_pre_topc('#skF_4',A_465)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_465)
      | ~ v2_pre_topc(A_465)
      | v2_struct_0(A_465) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_56,c_1674])).

tff(c_1681,plain,(
    ! [A_467,D_468] :
      ( k3_tmap_1(A_467,'#skF_3','#skF_4',D_468,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_468))
      | ~ m1_pre_topc(D_468,'#skF_4')
      | ~ m1_pre_topc(D_468,A_467)
      | ~ m1_pre_topc('#skF_4',A_467)
      | ~ l1_pre_topc(A_467)
      | ~ v2_pre_topc(A_467)
      | v2_struct_0(A_467) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1679])).

tff(c_1685,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_3','#skF_4','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1681])).

tff(c_1689,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0('#skF_4')) = '#skF_5'
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_1611,c_1685])).

tff(c_1690,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0('#skF_4')) = '#skF_5'
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1689])).

tff(c_1691,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1690])).

tff(c_1694,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_1691])).

tff(c_1698,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1694])).

tff(c_1700,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_1690])).

tff(c_1699,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0('#skF_4')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1690])).

tff(c_1493,plain,(
    ! [A_419,B_420,C_421,D_422] :
      ( k2_partfun1(u1_struct_0(A_419),u1_struct_0(B_420),C_421,u1_struct_0(D_422)) = k2_tmap_1(A_419,B_420,C_421,D_422)
      | ~ m1_pre_topc(D_422,A_419)
      | ~ m1_subset_1(C_421,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_419),u1_struct_0(B_420))))
      | ~ v1_funct_2(C_421,u1_struct_0(A_419),u1_struct_0(B_420))
      | ~ v1_funct_1(C_421)
      | ~ l1_pre_topc(B_420)
      | ~ v2_pre_topc(B_420)
      | v2_struct_0(B_420)
      | ~ l1_pre_topc(A_419)
      | ~ v2_pre_topc(A_419)
      | v2_struct_0(A_419) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1497,plain,(
    ! [D_422] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_422)) = k2_tmap_1('#skF_4','#skF_3','#skF_5',D_422)
      | ~ m1_pre_topc(D_422,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_1493])).

tff(c_1501,plain,(
    ! [D_422] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_422)) = k2_tmap_1('#skF_4','#skF_3','#skF_5',D_422)
      | ~ m1_pre_topc(D_422,'#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_86,c_66,c_64,c_58,c_56,c_1497])).

tff(c_1502,plain,(
    ! [D_422] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_422)) = k2_tmap_1('#skF_4','#skF_3','#skF_5',D_422)
      | ~ m1_pre_topc(D_422,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_68,c_1501])).

tff(c_1732,plain,
    ( k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4') = '#skF_5'
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1699,c_1502])).

tff(c_1739,plain,(
    k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1700,c_1732])).

tff(c_1994,plain,(
    ! [B_484,D_485,E_487,A_488,C_486] :
      ( r2_hidden('#skF_2'(B_484,D_485,C_486,E_487,A_488),u1_struct_0(C_486))
      | r2_funct_2(u1_struct_0(C_486),u1_struct_0(A_488),k2_tmap_1(B_484,A_488,D_485,C_486),E_487)
      | ~ m1_subset_1(E_487,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_486),u1_struct_0(A_488))))
      | ~ v1_funct_2(E_487,u1_struct_0(C_486),u1_struct_0(A_488))
      | ~ v1_funct_1(E_487)
      | ~ m1_subset_1(D_485,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_484),u1_struct_0(A_488))))
      | ~ v1_funct_2(D_485,u1_struct_0(B_484),u1_struct_0(A_488))
      | ~ v1_funct_1(D_485)
      | ~ m1_pre_topc(C_486,B_484)
      | v2_struct_0(C_486)
      | ~ l1_pre_topc(B_484)
      | ~ v2_pre_topc(B_484)
      | v2_struct_0(B_484)
      | ~ l1_pre_topc(A_488)
      | ~ v2_pre_topc(A_488)
      | v2_struct_0(A_488) ) ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_2554,plain,(
    ! [B_547,D_548,B_549,A_550] :
      ( r2_hidden('#skF_2'(B_547,D_548,B_549,k4_tmap_1(A_550,B_549),A_550),u1_struct_0(B_549))
      | r2_funct_2(u1_struct_0(B_549),u1_struct_0(A_550),k2_tmap_1(B_547,A_550,D_548,B_549),k4_tmap_1(A_550,B_549))
      | ~ v1_funct_2(k4_tmap_1(A_550,B_549),u1_struct_0(B_549),u1_struct_0(A_550))
      | ~ v1_funct_1(k4_tmap_1(A_550,B_549))
      | ~ m1_subset_1(D_548,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_547),u1_struct_0(A_550))))
      | ~ v1_funct_2(D_548,u1_struct_0(B_547),u1_struct_0(A_550))
      | ~ v1_funct_1(D_548)
      | ~ m1_pre_topc(B_549,B_547)
      | v2_struct_0(B_549)
      | ~ l1_pre_topc(B_547)
      | ~ v2_pre_topc(B_547)
      | v2_struct_0(B_547)
      | ~ m1_pre_topc(B_549,A_550)
      | ~ l1_pre_topc(A_550)
      | ~ v2_pre_topc(A_550)
      | v2_struct_0(A_550) ) ),
    inference(resolution,[status(thm)],[c_30,c_1994])).

tff(c_2559,plain,
    ( r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3'),u1_struct_0('#skF_4'))
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
    inference(superposition,[status(thm),theory(equality)],[c_1739,c_2554])).

tff(c_2562,plain,
    ( r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3'),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_102,c_86,c_1700,c_58,c_56,c_54,c_2559])).

tff(c_2563,plain,
    ( r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3'),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_2562])).

tff(c_2564,plain,(
    ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2563])).

tff(c_2567,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_2564])).

tff(c_2570,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_2567])).

tff(c_2572,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2570])).

tff(c_2574,plain,(
    v1_funct_1(k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2563])).

tff(c_2573,plain,
    ( ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2563])).

tff(c_2593,plain,(
    ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2573])).

tff(c_2596,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_2593])).

tff(c_2599,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_2596])).

tff(c_2601,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2599])).

tff(c_2603,plain,(
    v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2573])).

tff(c_2602,plain,
    ( r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3'),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2573])).

tff(c_2604,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2602])).

tff(c_2606,plain,
    ( k4_tmap_1('#skF_3','#skF_4') = '#skF_5'
    | ~ m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2604,c_12])).

tff(c_2609,plain,
    ( k4_tmap_1('#skF_3','#skF_4') = '#skF_5'
    | ~ m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2574,c_2603,c_2606])).

tff(c_2631,plain,(
    ~ m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_2609])).

tff(c_2634,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_2631])).

tff(c_2637,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_2634])).

tff(c_2639,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2637])).

tff(c_2640,plain,(
    k4_tmap_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2609])).

tff(c_2645,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2640,c_50])).

tff(c_2651,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1446,c_2645])).

tff(c_2653,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2602])).

tff(c_1600,plain,
    ( k3_tmap_1('#skF_4','#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_1596])).

tff(c_1606,plain,
    ( k3_tmap_1('#skF_4','#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_102,c_1600])).

tff(c_1607,plain,(
    k3_tmap_1('#skF_4','#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1606])).

tff(c_1796,plain,(
    ! [D_471,C_472,B_470,A_474,E_473] :
      ( m1_subset_1('#skF_2'(B_470,D_471,C_472,E_473,A_474),u1_struct_0(B_470))
      | r2_funct_2(u1_struct_0(C_472),u1_struct_0(A_474),k2_tmap_1(B_470,A_474,D_471,C_472),E_473)
      | ~ m1_subset_1(E_473,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_472),u1_struct_0(A_474))))
      | ~ v1_funct_2(E_473,u1_struct_0(C_472),u1_struct_0(A_474))
      | ~ v1_funct_1(E_473)
      | ~ m1_subset_1(D_471,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_470),u1_struct_0(A_474))))
      | ~ v1_funct_2(D_471,u1_struct_0(B_470),u1_struct_0(A_474))
      | ~ v1_funct_1(D_471)
      | ~ m1_pre_topc(C_472,B_470)
      | v2_struct_0(C_472)
      | ~ l1_pre_topc(B_470)
      | ~ v2_pre_topc(B_470)
      | v2_struct_0(B_470)
      | ~ l1_pre_topc(A_474)
      | ~ v2_pre_topc(A_474)
      | v2_struct_0(A_474) ) ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_2685,plain,(
    ! [B_560,D_561,B_562,A_563] :
      ( m1_subset_1('#skF_2'(B_560,D_561,B_562,k4_tmap_1(A_563,B_562),A_563),u1_struct_0(B_560))
      | r2_funct_2(u1_struct_0(B_562),u1_struct_0(A_563),k2_tmap_1(B_560,A_563,D_561,B_562),k4_tmap_1(A_563,B_562))
      | ~ v1_funct_2(k4_tmap_1(A_563,B_562),u1_struct_0(B_562),u1_struct_0(A_563))
      | ~ v1_funct_1(k4_tmap_1(A_563,B_562))
      | ~ m1_subset_1(D_561,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_560),u1_struct_0(A_563))))
      | ~ v1_funct_2(D_561,u1_struct_0(B_560),u1_struct_0(A_563))
      | ~ v1_funct_1(D_561)
      | ~ m1_pre_topc(B_562,B_560)
      | v2_struct_0(B_562)
      | ~ l1_pre_topc(B_560)
      | ~ v2_pre_topc(B_560)
      | v2_struct_0(B_560)
      | ~ m1_pre_topc(B_562,A_563)
      | ~ l1_pre_topc(A_563)
      | ~ v2_pre_topc(A_563)
      | v2_struct_0(A_563) ) ),
    inference(resolution,[status(thm)],[c_30,c_1796])).

tff(c_2700,plain,
    ( m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3'),u1_struct_0('#skF_4'))
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
    inference(superposition,[status(thm),theory(equality)],[c_1739,c_2685])).

tff(c_2706,plain,
    ( m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3'),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_102,c_86,c_1700,c_58,c_56,c_54,c_2574,c_2603,c_2700])).

tff(c_2707,plain,(
    m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_2653,c_2706])).

tff(c_18,plain,(
    ! [C_27,A_21,B_25] :
      ( m1_subset_1(C_27,u1_struct_0(A_21))
      | ~ m1_subset_1(C_27,u1_struct_0(B_25))
      | ~ m1_pre_topc(B_25,A_21)
      | v2_struct_0(B_25)
      | ~ l1_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2716,plain,(
    ! [A_21] :
      ( m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3'),u1_struct_0(A_21))
      | ~ m1_pre_topc('#skF_4',A_21)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(resolution,[status(thm)],[c_2707,c_18])).

tff(c_2731,plain,(
    ! [A_564] :
      ( m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3'),u1_struct_0(A_564))
      | ~ m1_pre_topc('#skF_4',A_564)
      | ~ l1_pre_topc(A_564)
      | v2_struct_0(A_564) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2716])).

tff(c_2652,plain,(
    r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2602])).

tff(c_52,plain,(
    ! [D_184] :
      ( k1_funct_1('#skF_5',D_184) = D_184
      | ~ r2_hidden(D_184,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(D_184,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_342])).

tff(c_2681,plain,
    ( k1_funct_1('#skF_5','#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3')) = '#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3')
    | ~ m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2652,c_52])).

tff(c_2683,plain,(
    ~ m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2681])).

tff(c_2737,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2731,c_2683])).

tff(c_2751,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_2737])).

tff(c_2753,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2751])).

tff(c_2754,plain,(
    k1_funct_1('#skF_5','#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3')) = '#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_2681])).

tff(c_1686,plain,(
    ! [A_81] :
      ( k3_tmap_1(A_81,'#skF_3','#skF_4',A_81,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(A_81))
      | ~ m1_pre_topc(A_81,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_81)
      | ~ v2_pre_topc(A_81)
      | v2_struct_0(A_81)
      | ~ l1_pre_topc(A_81) ) ),
    inference(resolution,[status(thm)],[c_36,c_1681])).

tff(c_1749,plain,(
    ! [A_469] :
      ( k3_tmap_1(A_469,'#skF_3','#skF_4',A_469,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(A_469))
      | ~ m1_pre_topc(A_469,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_469)
      | ~ v2_pre_topc(A_469)
      | v2_struct_0(A_469)
      | ~ l1_pre_topc(A_469) ) ),
    inference(resolution,[status(thm)],[c_36,c_1681])).

tff(c_1764,plain,(
    ! [A_469] :
      ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(A_469)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_469),u1_struct_0('#skF_3'))))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(A_469,A_469)
      | ~ m1_pre_topc('#skF_4',A_469)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_469)
      | ~ v2_pre_topc(A_469)
      | v2_struct_0(A_469)
      | ~ m1_pre_topc(A_469,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_469)
      | ~ v2_pre_topc(A_469)
      | v2_struct_0(A_469)
      | ~ l1_pre_topc(A_469) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1749,c_24])).

tff(c_1789,plain,(
    ! [A_469] :
      ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(A_469)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_469),u1_struct_0('#skF_3'))))
      | ~ m1_pre_topc(A_469,A_469)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(A_469,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_469)
      | ~ v2_pre_topc(A_469)
      | v2_struct_0(A_469)
      | ~ l1_pre_topc(A_469) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_56,c_54,c_1764])).

tff(c_1823,plain,(
    ! [A_476] :
      ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(A_476)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_476),u1_struct_0('#skF_3'))))
      | ~ m1_pre_topc(A_476,A_476)
      | ~ m1_pre_topc(A_476,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_476)
      | ~ v2_pre_topc(A_476)
      | v2_struct_0(A_476)
      | ~ l1_pre_topc(A_476) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1789])).

tff(c_1842,plain,(
    ! [A_81] :
      ( m1_subset_1(k3_tmap_1(A_81,'#skF_3','#skF_4',A_81,'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_81),u1_struct_0('#skF_3'))))
      | ~ m1_pre_topc(A_81,A_81)
      | ~ m1_pre_topc(A_81,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_81)
      | ~ v2_pre_topc(A_81)
      | v2_struct_0(A_81)
      | ~ l1_pre_topc(A_81)
      | ~ m1_pre_topc(A_81,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_81)
      | ~ v2_pre_topc(A_81)
      | v2_struct_0(A_81)
      | ~ l1_pre_topc(A_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1686,c_1823])).

tff(c_2814,plain,(
    ! [B_568,D_569,B_570,A_571] :
      ( m1_subset_1('#skF_2'(B_568,D_569,B_570,k4_tmap_1(A_571,B_570),A_571),u1_struct_0(B_568))
      | r2_funct_2(u1_struct_0(B_570),u1_struct_0(A_571),k2_tmap_1(B_568,A_571,D_569,B_570),k4_tmap_1(A_571,B_570))
      | ~ v1_funct_2(k4_tmap_1(A_571,B_570),u1_struct_0(B_570),u1_struct_0(A_571))
      | ~ v1_funct_1(k4_tmap_1(A_571,B_570))
      | ~ m1_subset_1(D_569,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_568),u1_struct_0(A_571))))
      | ~ v1_funct_2(D_569,u1_struct_0(B_568),u1_struct_0(A_571))
      | ~ v1_funct_1(D_569)
      | ~ m1_pre_topc(B_570,B_568)
      | v2_struct_0(B_570)
      | ~ l1_pre_topc(B_568)
      | ~ v2_pre_topc(B_568)
      | v2_struct_0(B_568)
      | ~ m1_pre_topc(B_570,A_571)
      | ~ l1_pre_topc(A_571)
      | ~ v2_pre_topc(A_571)
      | v2_struct_0(A_571) ) ),
    inference(resolution,[status(thm)],[c_30,c_1796])).

tff(c_2827,plain,
    ( m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3'),u1_struct_0('#skF_4'))
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
    inference(superposition,[status(thm),theory(equality)],[c_1739,c_2814])).

tff(c_2833,plain,
    ( m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3'),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_102,c_86,c_1700,c_58,c_56,c_54,c_2574,c_2603,c_2827])).

tff(c_2834,plain,(
    m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_2653,c_2833])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9,D_10] :
      ( k3_funct_2(A_7,B_8,C_9,D_10) = k1_funct_1(C_9,D_10)
      | ~ m1_subset_1(D_10,A_7)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8)))
      | ~ v1_funct_2(C_9,A_7,B_8)
      | ~ v1_funct_1(C_9)
      | v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2838,plain,(
    ! [B_8,C_9] :
      ( k3_funct_2(u1_struct_0('#skF_4'),B_8,C_9,'#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3')) = k1_funct_1(C_9,'#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3'))
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),B_8)))
      | ~ v1_funct_2(C_9,u1_struct_0('#skF_4'),B_8)
      | ~ v1_funct_1(C_9)
      | v1_xboole_0(u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_2834,c_8])).

tff(c_2887,plain,(
    ! [B_575,C_576] :
      ( k3_funct_2(u1_struct_0('#skF_4'),B_575,C_576,'#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3')) = k1_funct_1(C_576,'#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3'))
      | ~ m1_subset_1(C_576,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),B_575)))
      | ~ v1_funct_2(C_576,u1_struct_0('#skF_4'),B_575)
      | ~ v1_funct_1(C_576) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1422,c_2838])).

tff(c_2891,plain,
    ( k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_4','#skF_3','#skF_4','#skF_4','#skF_5'),'#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3')) = k1_funct_1(k3_tmap_1('#skF_4','#skF_3','#skF_4','#skF_4','#skF_5'),'#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3'))
    | ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_3','#skF_4','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k3_tmap_1('#skF_4','#skF_3','#skF_4','#skF_4','#skF_5'))
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_1842,c_2887])).

tff(c_2913,plain,
    ( k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5','#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3')) = '#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_102,c_1700,c_58,c_1607,c_56,c_1607,c_2754,c_1607,c_1607,c_2891])).

tff(c_2914,plain,(
    k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5','#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3')) = '#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2913])).

tff(c_38,plain,(
    ! [D_138,A_82,B_114,C_130,E_142] :
      ( k3_funct_2(u1_struct_0(B_114),u1_struct_0(A_82),D_138,'#skF_2'(B_114,D_138,C_130,E_142,A_82)) != k1_funct_1(E_142,'#skF_2'(B_114,D_138,C_130,E_142,A_82))
      | r2_funct_2(u1_struct_0(C_130),u1_struct_0(A_82),k2_tmap_1(B_114,A_82,D_138,C_130),E_142)
      | ~ m1_subset_1(E_142,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_130),u1_struct_0(A_82))))
      | ~ v1_funct_2(E_142,u1_struct_0(C_130),u1_struct_0(A_82))
      | ~ v1_funct_1(E_142)
      | ~ m1_subset_1(D_138,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_114),u1_struct_0(A_82))))
      | ~ v1_funct_2(D_138,u1_struct_0(B_114),u1_struct_0(A_82))
      | ~ v1_funct_1(D_138)
      | ~ m1_pre_topc(C_130,B_114)
      | v2_struct_0(C_130)
      | ~ l1_pre_topc(B_114)
      | ~ v2_pre_topc(B_114)
      | v2_struct_0(B_114)
      | ~ l1_pre_topc(A_82)
      | ~ v2_pre_topc(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_2930,plain,
    ( k1_funct_1(k4_tmap_1('#skF_3','#skF_4'),'#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3')) != '#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3')
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
    inference(superposition,[status(thm),theory(equality)],[c_2914,c_38])).

tff(c_2934,plain,
    ( k1_funct_1(k4_tmap_1('#skF_3','#skF_4'),'#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3')) != '#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3')
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | ~ m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_102,c_86,c_1700,c_58,c_56,c_54,c_2574,c_2603,c_1739,c_2930])).

tff(c_2935,plain,
    ( k1_funct_1(k4_tmap_1('#skF_3','#skF_4'),'#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3')) != '#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3')
    | ~ m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_2653,c_2934])).

tff(c_2973,plain,(
    ~ m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_2935])).

tff(c_2976,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_2973])).

tff(c_2979,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_2976])).

tff(c_2981,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2979])).

tff(c_2982,plain,(
    k1_funct_1(k4_tmap_1('#skF_3','#skF_4'),'#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3')) != '#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_2935])).

tff(c_2755,plain,(
    m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2681])).

tff(c_1453,plain,(
    ! [A_396,B_397,C_398] :
      ( k1_funct_1(k4_tmap_1(A_396,B_397),C_398) = C_398
      | ~ r2_hidden(C_398,u1_struct_0(B_397))
      | ~ m1_subset_1(C_398,u1_struct_0(A_396))
      | ~ m1_pre_topc(B_397,A_396)
      | v2_struct_0(B_397)
      | ~ l1_pre_topc(A_396)
      | ~ v2_pre_topc(A_396)
      | v2_struct_0(A_396) ) ),
    inference(cnfTransformation,[status(thm)],[f_312])).

tff(c_1460,plain,(
    ! [A_396,B_397,A_5] :
      ( k1_funct_1(k4_tmap_1(A_396,B_397),A_5) = A_5
      | ~ m1_subset_1(A_5,u1_struct_0(A_396))
      | ~ m1_pre_topc(B_397,A_396)
      | v2_struct_0(B_397)
      | ~ l1_pre_topc(A_396)
      | ~ v2_pre_topc(A_396)
      | v2_struct_0(A_396)
      | v1_xboole_0(u1_struct_0(B_397))
      | ~ m1_subset_1(A_5,u1_struct_0(B_397)) ) ),
    inference(resolution,[status(thm)],[c_6,c_1453])).

tff(c_2757,plain,(
    ! [B_397] :
      ( k1_funct_1(k4_tmap_1('#skF_3',B_397),'#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3')) = '#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3')
      | ~ m1_pre_topc(B_397,'#skF_3')
      | v2_struct_0(B_397)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | v1_xboole_0(u1_struct_0(B_397))
      | ~ m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3'),u1_struct_0(B_397)) ) ),
    inference(resolution,[status(thm)],[c_2755,c_1460])).

tff(c_2767,plain,(
    ! [B_397] :
      ( k1_funct_1(k4_tmap_1('#skF_3',B_397),'#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3')) = '#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3')
      | ~ m1_pre_topc(B_397,'#skF_3')
      | v2_struct_0(B_397)
      | v2_struct_0('#skF_3')
      | v1_xboole_0(u1_struct_0(B_397))
      | ~ m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3'),u1_struct_0(B_397)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_2757])).

tff(c_9972,plain,(
    ! [B_880] :
      ( k1_funct_1(k4_tmap_1('#skF_3',B_880),'#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3')) = '#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3')
      | ~ m1_pre_topc(B_880,'#skF_3')
      | v2_struct_0(B_880)
      | v1_xboole_0(u1_struct_0(B_880))
      | ~ m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3'),u1_struct_0(B_880)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2767])).

tff(c_9982,plain,
    ( k1_funct_1(k4_tmap_1('#skF_3','#skF_4'),'#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3')) = '#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2834,c_9972])).

tff(c_9998,plain,
    ( k1_funct_1(k4_tmap_1('#skF_3','#skF_4'),'#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3')) = '#skF_2'('#skF_4','#skF_5','#skF_4',k4_tmap_1('#skF_3','#skF_4'),'#skF_3')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_9982])).

tff(c_10000,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1422,c_62,c_2982,c_9998])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:49:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.07/3.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.07/3.78  
% 10.07/3.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.07/3.79  %$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_tmap_1 > k2_partfun1 > k4_tmap_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 10.07/3.79  
% 10.07/3.79  %Foreground sorts:
% 10.07/3.79  
% 10.07/3.79  
% 10.07/3.79  %Background operators:
% 10.07/3.79  
% 10.07/3.79  
% 10.07/3.79  %Foreground operators:
% 10.07/3.79  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 10.07/3.79  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 10.07/3.79  tff(k4_tmap_1, type, k4_tmap_1: ($i * $i) > $i).
% 10.07/3.79  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.07/3.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.07/3.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.07/3.79  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 10.07/3.79  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.07/3.79  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.07/3.79  tff('#skF_5', type, '#skF_5': $i).
% 10.07/3.79  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.07/3.79  tff('#skF_3', type, '#skF_3': $i).
% 10.07/3.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.07/3.79  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 10.07/3.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.07/3.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.07/3.79  tff('#skF_4', type, '#skF_4': $i).
% 10.07/3.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.07/3.79  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 10.07/3.79  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 10.07/3.79  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.07/3.79  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 10.07/3.79  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.07/3.79  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.07/3.79  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 10.07/3.79  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 10.07/3.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.07/3.79  
% 10.32/3.83  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 10.32/3.83  tff(f_342, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, u1_struct_0(B)) => (D = k1_funct_1(C, D))))) => r2_funct_2(u1_struct_0(B), u1_struct_0(A), k4_tmap_1(A, B), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_tmap_1)).
% 10.32/3.83  tff(f_66, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 10.32/3.83  tff(f_202, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_funct_1(k4_tmap_1(A, B)) & v1_funct_2(k4_tmap_1(A, B), u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(k4_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_tmap_1)).
% 10.32/3.83  tff(f_75, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 10.32/3.83  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 10.32/3.83  tff(f_206, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 10.32/3.83  tff(f_187, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 10.32/3.83  tff(f_280, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), D, k3_tmap_1(A, B, C, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tmap_1)).
% 10.32/3.83  tff(f_157, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 10.32/3.83  tff(f_125, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 10.32/3.83  tff(f_250, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(A))))) => ((![F]: (m1_subset_1(F, u1_struct_0(B)) => (r2_hidden(F, u1_struct_0(C)) => (k3_funct_2(u1_struct_0(B), u1_struct_0(A), D, F) = k1_funct_1(E, F))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(A), k2_tmap_1(B, A, D, C), E)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_tmap_1)).
% 10.32/3.83  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 10.32/3.83  tff(f_98, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 10.32/3.83  tff(f_50, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 10.32/3.83  tff(f_312, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, u1_struct_0(B)) => (k1_funct_1(k4_tmap_1(A, B), C) = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_tmap_1)).
% 10.32/3.83  tff(c_6, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.32/3.83  tff(c_103, plain, (![D_195]: (k1_funct_1('#skF_5', D_195)=D_195 | ~r2_hidden(D_195, u1_struct_0('#skF_4')) | ~m1_subset_1(D_195, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_342])).
% 10.32/3.83  tff(c_112, plain, (![A_5]: (k1_funct_1('#skF_5', A_5)=A_5 | ~m1_subset_1(A_5, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(A_5, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_6, c_103])).
% 10.32/3.83  tff(c_115, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_112])).
% 10.32/3.83  tff(c_68, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_342])).
% 10.32/3.83  tff(c_62, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_342])).
% 10.32/3.83  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_342])).
% 10.32/3.83  tff(c_56, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_342])).
% 10.32/3.83  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_342])).
% 10.32/3.83  tff(c_132, plain, (![A_204, B_205, D_206]: (r2_funct_2(A_204, B_205, D_206, D_206) | ~m1_subset_1(D_206, k1_zfmisc_1(k2_zfmisc_1(A_204, B_205))) | ~v1_funct_2(D_206, A_204, B_205) | ~v1_funct_1(D_206))), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.32/3.83  tff(c_134, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', '#skF_5') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_132])).
% 10.32/3.83  tff(c_137, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_134])).
% 10.32/3.83  tff(c_66, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_342])).
% 10.32/3.83  tff(c_64, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_342])).
% 10.32/3.83  tff(c_60, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_342])).
% 10.32/3.83  tff(c_30, plain, (![A_79, B_80]: (m1_subset_1(k4_tmap_1(A_79, B_80), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_80), u1_struct_0(A_79)))) | ~m1_pre_topc(B_80, A_79) | ~l1_pre_topc(A_79) | ~v2_pre_topc(A_79) | v2_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_202])).
% 10.32/3.83  tff(c_34, plain, (![A_79, B_80]: (v1_funct_1(k4_tmap_1(A_79, B_80)) | ~m1_pre_topc(B_80, A_79) | ~l1_pre_topc(A_79) | ~v2_pre_topc(A_79) | v2_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_202])).
% 10.32/3.83  tff(c_92, plain, (![B_193, A_194]: (v2_pre_topc(B_193) | ~m1_pre_topc(B_193, A_194) | ~l1_pre_topc(A_194) | ~v2_pre_topc(A_194))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.32/3.83  tff(c_98, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_60, c_92])).
% 10.32/3.83  tff(c_102, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_98])).
% 10.32/3.83  tff(c_76, plain, (![B_189, A_190]: (l1_pre_topc(B_189) | ~m1_pre_topc(B_189, A_190) | ~l1_pre_topc(A_190))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.32/3.83  tff(c_82, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_60, c_76])).
% 10.32/3.83  tff(c_86, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_82])).
% 10.32/3.83  tff(c_36, plain, (![A_81]: (m1_pre_topc(A_81, A_81) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_206])).
% 10.32/3.83  tff(c_174, plain, (![B_234, A_233, C_231, E_232, D_230]: (v1_funct_1(k3_tmap_1(A_233, B_234, C_231, D_230, E_232)) | ~m1_subset_1(E_232, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_231), u1_struct_0(B_234)))) | ~v1_funct_2(E_232, u1_struct_0(C_231), u1_struct_0(B_234)) | ~v1_funct_1(E_232) | ~m1_pre_topc(D_230, A_233) | ~m1_pre_topc(C_231, A_233) | ~l1_pre_topc(B_234) | ~v2_pre_topc(B_234) | v2_struct_0(B_234) | ~l1_pre_topc(A_233) | ~v2_pre_topc(A_233) | v2_struct_0(A_233))), inference(cnfTransformation, [status(thm)], [f_187])).
% 10.32/3.83  tff(c_178, plain, (![A_233, D_230]: (v1_funct_1(k3_tmap_1(A_233, '#skF_3', '#skF_4', D_230, '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_230, A_233) | ~m1_pre_topc('#skF_4', A_233) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_233) | ~v2_pre_topc(A_233) | v2_struct_0(A_233))), inference(resolution, [status(thm)], [c_54, c_174])).
% 10.32/3.83  tff(c_182, plain, (![A_233, D_230]: (v1_funct_1(k3_tmap_1(A_233, '#skF_3', '#skF_4', D_230, '#skF_5')) | ~m1_pre_topc(D_230, A_233) | ~m1_pre_topc('#skF_4', A_233) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_233) | ~v2_pre_topc(A_233) | v2_struct_0(A_233))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_56, c_178])).
% 10.32/3.83  tff(c_183, plain, (![A_233, D_230]: (v1_funct_1(k3_tmap_1(A_233, '#skF_3', '#skF_4', D_230, '#skF_5')) | ~m1_pre_topc(D_230, A_233) | ~m1_pre_topc('#skF_4', A_233) | ~l1_pre_topc(A_233) | ~v2_pre_topc(A_233) | v2_struct_0(A_233))), inference(negUnitSimplification, [status(thm)], [c_68, c_182])).
% 10.32/3.83  tff(c_210, plain, (![E_252, D_250, B_254, A_253, C_251]: (v1_funct_2(k3_tmap_1(A_253, B_254, C_251, D_250, E_252), u1_struct_0(D_250), u1_struct_0(B_254)) | ~m1_subset_1(E_252, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_251), u1_struct_0(B_254)))) | ~v1_funct_2(E_252, u1_struct_0(C_251), u1_struct_0(B_254)) | ~v1_funct_1(E_252) | ~m1_pre_topc(D_250, A_253) | ~m1_pre_topc(C_251, A_253) | ~l1_pre_topc(B_254) | ~v2_pre_topc(B_254) | v2_struct_0(B_254) | ~l1_pre_topc(A_253) | ~v2_pre_topc(A_253) | v2_struct_0(A_253))), inference(cnfTransformation, [status(thm)], [f_187])).
% 10.32/3.83  tff(c_214, plain, (![A_253, D_250]: (v1_funct_2(k3_tmap_1(A_253, '#skF_3', '#skF_4', D_250, '#skF_5'), u1_struct_0(D_250), u1_struct_0('#skF_3')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_250, A_253) | ~m1_pre_topc('#skF_4', A_253) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_253) | ~v2_pre_topc(A_253) | v2_struct_0(A_253))), inference(resolution, [status(thm)], [c_54, c_210])).
% 10.32/3.83  tff(c_218, plain, (![A_253, D_250]: (v1_funct_2(k3_tmap_1(A_253, '#skF_3', '#skF_4', D_250, '#skF_5'), u1_struct_0(D_250), u1_struct_0('#skF_3')) | ~m1_pre_topc(D_250, A_253) | ~m1_pre_topc('#skF_4', A_253) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_253) | ~v2_pre_topc(A_253) | v2_struct_0(A_253))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_56, c_214])).
% 10.32/3.83  tff(c_219, plain, (![A_253, D_250]: (v1_funct_2(k3_tmap_1(A_253, '#skF_3', '#skF_4', D_250, '#skF_5'), u1_struct_0(D_250), u1_struct_0('#skF_3')) | ~m1_pre_topc(D_250, A_253) | ~m1_pre_topc('#skF_4', A_253) | ~l1_pre_topc(A_253) | ~v2_pre_topc(A_253) | v2_struct_0(A_253))), inference(negUnitSimplification, [status(thm)], [c_68, c_218])).
% 10.32/3.83  tff(c_24, plain, (![A_74, D_77, B_75, C_76, E_78]: (m1_subset_1(k3_tmap_1(A_74, B_75, C_76, D_77, E_78), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_77), u1_struct_0(B_75)))) | ~m1_subset_1(E_78, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_76), u1_struct_0(B_75)))) | ~v1_funct_2(E_78, u1_struct_0(C_76), u1_struct_0(B_75)) | ~v1_funct_1(E_78) | ~m1_pre_topc(D_77, A_74) | ~m1_pre_topc(C_76, A_74) | ~l1_pre_topc(B_75) | ~v2_pre_topc(B_75) | v2_struct_0(B_75) | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_187])).
% 10.32/3.83  tff(c_221, plain, (![C_257, B_258, D_259, A_260]: (r2_funct_2(u1_struct_0(C_257), u1_struct_0(B_258), D_259, k3_tmap_1(A_260, B_258, C_257, C_257, D_259)) | ~m1_subset_1(D_259, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_257), u1_struct_0(B_258)))) | ~v1_funct_2(D_259, u1_struct_0(C_257), u1_struct_0(B_258)) | ~v1_funct_1(D_259) | ~m1_pre_topc(C_257, A_260) | v2_struct_0(C_257) | ~l1_pre_topc(B_258) | ~v2_pre_topc(B_258) | v2_struct_0(B_258) | ~l1_pre_topc(A_260) | ~v2_pre_topc(A_260) | v2_struct_0(A_260))), inference(cnfTransformation, [status(thm)], [f_280])).
% 10.32/3.83  tff(c_225, plain, (![A_260]: (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k3_tmap_1(A_260, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_260) | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_260) | ~v2_pre_topc(A_260) | v2_struct_0(A_260))), inference(resolution, [status(thm)], [c_54, c_221])).
% 10.32/3.83  tff(c_229, plain, (![A_260]: (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k3_tmap_1(A_260, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_260) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_260) | ~v2_pre_topc(A_260) | v2_struct_0(A_260))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_56, c_225])).
% 10.32/3.83  tff(c_231, plain, (![A_261]: (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k3_tmap_1(A_261, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_261) | ~l1_pre_topc(A_261) | ~v2_pre_topc(A_261) | v2_struct_0(A_261))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_229])).
% 10.32/3.83  tff(c_12, plain, (![D_14, C_13, A_11, B_12]: (D_14=C_13 | ~r2_funct_2(A_11, B_12, C_13, D_14) | ~m1_subset_1(D_14, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))) | ~v1_funct_2(D_14, A_11, B_12) | ~v1_funct_1(D_14) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))) | ~v1_funct_2(C_13, A_11, B_12) | ~v1_funct_1(C_13))), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.32/3.83  tff(c_233, plain, (![A_261]: (k3_tmap_1(A_261, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~m1_subset_1(k3_tmap_1(A_261, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k3_tmap_1(A_261, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k3_tmap_1(A_261, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_261) | ~l1_pre_topc(A_261) | ~v2_pre_topc(A_261) | v2_struct_0(A_261))), inference(resolution, [status(thm)], [c_231, c_12])).
% 10.32/3.83  tff(c_257, plain, (![A_271]: (k3_tmap_1(A_271, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~m1_subset_1(k3_tmap_1(A_271, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k3_tmap_1(A_271, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k3_tmap_1(A_271, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_271) | ~l1_pre_topc(A_271) | ~v2_pre_topc(A_271) | v2_struct_0(A_271))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_233])).
% 10.32/3.83  tff(c_261, plain, (![A_74]: (k3_tmap_1(A_74, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~v1_funct_2(k3_tmap_1(A_74, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k3_tmap_1(A_74, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_74) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74) | v2_struct_0(A_74))), inference(resolution, [status(thm)], [c_24, c_257])).
% 10.32/3.83  tff(c_264, plain, (![A_74]: (k3_tmap_1(A_74, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~v1_funct_2(k3_tmap_1(A_74, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k3_tmap_1(A_74, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_74) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74) | v2_struct_0(A_74))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_56, c_54, c_261])).
% 10.32/3.83  tff(c_266, plain, (![A_272]: (k3_tmap_1(A_272, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~v1_funct_2(k3_tmap_1(A_272, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k3_tmap_1(A_272, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_272) | ~l1_pre_topc(A_272) | ~v2_pre_topc(A_272) | v2_struct_0(A_272))), inference(negUnitSimplification, [status(thm)], [c_68, c_264])).
% 10.32/3.83  tff(c_272, plain, (![A_273]: (k3_tmap_1(A_273, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~v1_funct_1(k3_tmap_1(A_273, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_273) | ~l1_pre_topc(A_273) | ~v2_pre_topc(A_273) | v2_struct_0(A_273))), inference(resolution, [status(thm)], [c_219, c_266])).
% 10.32/3.83  tff(c_278, plain, (![A_274]: (k3_tmap_1(A_274, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~m1_pre_topc('#skF_4', A_274) | ~l1_pre_topc(A_274) | ~v2_pre_topc(A_274) | v2_struct_0(A_274))), inference(resolution, [status(thm)], [c_183, c_272])).
% 10.32/3.83  tff(c_285, plain, (k3_tmap_1('#skF_3', '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_278])).
% 10.32/3.83  tff(c_292, plain, (k3_tmap_1('#skF_3', '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_285])).
% 10.32/3.83  tff(c_293, plain, (k3_tmap_1('#skF_3', '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_68, c_292])).
% 10.32/3.83  tff(c_350, plain, (![C_277, A_278, B_275, D_276, E_279]: (k3_tmap_1(A_278, B_275, C_277, D_276, E_279)=k2_partfun1(u1_struct_0(C_277), u1_struct_0(B_275), E_279, u1_struct_0(D_276)) | ~m1_pre_topc(D_276, C_277) | ~m1_subset_1(E_279, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_277), u1_struct_0(B_275)))) | ~v1_funct_2(E_279, u1_struct_0(C_277), u1_struct_0(B_275)) | ~v1_funct_1(E_279) | ~m1_pre_topc(D_276, A_278) | ~m1_pre_topc(C_277, A_278) | ~l1_pre_topc(B_275) | ~v2_pre_topc(B_275) | v2_struct_0(B_275) | ~l1_pre_topc(A_278) | ~v2_pre_topc(A_278) | v2_struct_0(A_278))), inference(cnfTransformation, [status(thm)], [f_157])).
% 10.32/3.83  tff(c_356, plain, (![A_278, D_276]: (k3_tmap_1(A_278, '#skF_3', '#skF_4', D_276, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_276)) | ~m1_pre_topc(D_276, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_276, A_278) | ~m1_pre_topc('#skF_4', A_278) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_278) | ~v2_pre_topc(A_278) | v2_struct_0(A_278))), inference(resolution, [status(thm)], [c_54, c_350])).
% 10.32/3.83  tff(c_361, plain, (![A_278, D_276]: (k3_tmap_1(A_278, '#skF_3', '#skF_4', D_276, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_276)) | ~m1_pre_topc(D_276, '#skF_4') | ~m1_pre_topc(D_276, A_278) | ~m1_pre_topc('#skF_4', A_278) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_278) | ~v2_pre_topc(A_278) | v2_struct_0(A_278))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_56, c_356])).
% 10.32/3.83  tff(c_363, plain, (![A_280, D_281]: (k3_tmap_1(A_280, '#skF_3', '#skF_4', D_281, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_281)) | ~m1_pre_topc(D_281, '#skF_4') | ~m1_pre_topc(D_281, A_280) | ~m1_pre_topc('#skF_4', A_280) | ~l1_pre_topc(A_280) | ~v2_pre_topc(A_280) | v2_struct_0(A_280))), inference(negUnitSimplification, [status(thm)], [c_68, c_361])).
% 10.32/3.83  tff(c_367, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_3', '#skF_4', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_363])).
% 10.32/3.83  tff(c_371, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0('#skF_4'))='#skF_5' | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_293, c_367])).
% 10.32/3.83  tff(c_372, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0('#skF_4'))='#skF_5' | ~m1_pre_topc('#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_68, c_371])).
% 10.32/3.83  tff(c_373, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_372])).
% 10.32/3.83  tff(c_376, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_36, c_373])).
% 10.32/3.83  tff(c_380, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_376])).
% 10.32/3.83  tff(c_382, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_372])).
% 10.32/3.83  tff(c_381, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0('#skF_4'))='#skF_5'), inference(splitRight, [status(thm)], [c_372])).
% 10.32/3.83  tff(c_191, plain, (![A_245, B_246, C_247, D_248]: (k2_partfun1(u1_struct_0(A_245), u1_struct_0(B_246), C_247, u1_struct_0(D_248))=k2_tmap_1(A_245, B_246, C_247, D_248) | ~m1_pre_topc(D_248, A_245) | ~m1_subset_1(C_247, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_245), u1_struct_0(B_246)))) | ~v1_funct_2(C_247, u1_struct_0(A_245), u1_struct_0(B_246)) | ~v1_funct_1(C_247) | ~l1_pre_topc(B_246) | ~v2_pre_topc(B_246) | v2_struct_0(B_246) | ~l1_pre_topc(A_245) | ~v2_pre_topc(A_245) | v2_struct_0(A_245))), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.32/3.83  tff(c_195, plain, (![D_248]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_248))=k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_248) | ~m1_pre_topc(D_248, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_191])).
% 10.32/3.83  tff(c_199, plain, (![D_248]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_248))=k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_248) | ~m1_pre_topc(D_248, '#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_86, c_66, c_64, c_58, c_56, c_195])).
% 10.32/3.83  tff(c_200, plain, (![D_248]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_248))=k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_248) | ~m1_pre_topc(D_248, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_62, c_68, c_199])).
% 10.32/3.83  tff(c_414, plain, (k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4')='#skF_5' | ~m1_pre_topc('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_381, c_200])).
% 10.32/3.83  tff(c_421, plain, (k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_382, c_414])).
% 10.32/3.83  tff(c_478, plain, (![D_284, E_286, C_285, A_287, B_283]: (m1_subset_1('#skF_2'(B_283, D_284, C_285, E_286, A_287), u1_struct_0(B_283)) | r2_funct_2(u1_struct_0(C_285), u1_struct_0(A_287), k2_tmap_1(B_283, A_287, D_284, C_285), E_286) | ~m1_subset_1(E_286, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_285), u1_struct_0(A_287)))) | ~v1_funct_2(E_286, u1_struct_0(C_285), u1_struct_0(A_287)) | ~v1_funct_1(E_286) | ~m1_subset_1(D_284, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_283), u1_struct_0(A_287)))) | ~v1_funct_2(D_284, u1_struct_0(B_283), u1_struct_0(A_287)) | ~v1_funct_1(D_284) | ~m1_pre_topc(C_285, B_283) | v2_struct_0(C_285) | ~l1_pre_topc(B_283) | ~v2_pre_topc(B_283) | v2_struct_0(B_283) | ~l1_pre_topc(A_287) | ~v2_pre_topc(A_287) | v2_struct_0(A_287))), inference(cnfTransformation, [status(thm)], [f_250])).
% 10.32/3.83  tff(c_1224, plain, (![B_362, D_363, B_364, A_365]: (m1_subset_1('#skF_2'(B_362, D_363, B_364, k4_tmap_1(A_365, B_364), A_365), u1_struct_0(B_362)) | r2_funct_2(u1_struct_0(B_364), u1_struct_0(A_365), k2_tmap_1(B_362, A_365, D_363, B_364), k4_tmap_1(A_365, B_364)) | ~v1_funct_2(k4_tmap_1(A_365, B_364), u1_struct_0(B_364), u1_struct_0(A_365)) | ~v1_funct_1(k4_tmap_1(A_365, B_364)) | ~m1_subset_1(D_363, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_362), u1_struct_0(A_365)))) | ~v1_funct_2(D_363, u1_struct_0(B_362), u1_struct_0(A_365)) | ~v1_funct_1(D_363) | ~m1_pre_topc(B_364, B_362) | v2_struct_0(B_364) | ~l1_pre_topc(B_362) | ~v2_pre_topc(B_362) | v2_struct_0(B_362) | ~m1_pre_topc(B_364, A_365) | ~l1_pre_topc(A_365) | ~v2_pre_topc(A_365) | v2_struct_0(A_365))), inference(resolution, [status(thm)], [c_30, c_478])).
% 10.32/3.83  tff(c_1235, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_421, c_1224])).
% 10.32/3.83  tff(c_1241, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_102, c_86, c_382, c_58, c_56, c_54, c_1235])).
% 10.32/3.83  tff(c_1242, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_1241])).
% 10.32/3.83  tff(c_1243, plain, (~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_1242])).
% 10.32/3.83  tff(c_1246, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_1243])).
% 10.32/3.83  tff(c_1249, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_1246])).
% 10.32/3.83  tff(c_1251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1249])).
% 10.32/3.83  tff(c_1253, plain, (v1_funct_1(k4_tmap_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_1242])).
% 10.32/3.83  tff(c_32, plain, (![A_79, B_80]: (v1_funct_2(k4_tmap_1(A_79, B_80), u1_struct_0(B_80), u1_struct_0(A_79)) | ~m1_pre_topc(B_80, A_79) | ~l1_pre_topc(A_79) | ~v2_pre_topc(A_79) | v2_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_202])).
% 10.32/3.83  tff(c_1252, plain, (~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_1242])).
% 10.32/3.83  tff(c_1272, plain, (~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_1252])).
% 10.32/3.83  tff(c_1275, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_1272])).
% 10.32/3.83  tff(c_1278, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_1275])).
% 10.32/3.83  tff(c_1280, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1278])).
% 10.32/3.83  tff(c_1282, plain, (v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_1252])).
% 10.32/3.83  tff(c_1281, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_1252])).
% 10.32/3.83  tff(c_1283, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_1281])).
% 10.32/3.83  tff(c_1285, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5' | ~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_1283, c_12])).
% 10.32/3.83  tff(c_1288, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5' | ~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_1253, c_1282, c_1285])).
% 10.32/3.83  tff(c_1299, plain, (~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(splitLeft, [status(thm)], [c_1288])).
% 10.32/3.83  tff(c_1302, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_30, c_1299])).
% 10.32/3.83  tff(c_1305, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_1302])).
% 10.32/3.83  tff(c_1307, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1305])).
% 10.32/3.83  tff(c_1308, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_1288])).
% 10.32/3.83  tff(c_50, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_342])).
% 10.32/3.83  tff(c_1313, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1308, c_50])).
% 10.32/3.83  tff(c_1319, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_137, c_1313])).
% 10.32/3.83  tff(c_1321, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_1281])).
% 10.32/3.83  tff(c_676, plain, (![C_299, B_297, E_300, A_301, D_298]: (r2_hidden('#skF_2'(B_297, D_298, C_299, E_300, A_301), u1_struct_0(C_299)) | r2_funct_2(u1_struct_0(C_299), u1_struct_0(A_301), k2_tmap_1(B_297, A_301, D_298, C_299), E_300) | ~m1_subset_1(E_300, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_299), u1_struct_0(A_301)))) | ~v1_funct_2(E_300, u1_struct_0(C_299), u1_struct_0(A_301)) | ~v1_funct_1(E_300) | ~m1_subset_1(D_298, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_297), u1_struct_0(A_301)))) | ~v1_funct_2(D_298, u1_struct_0(B_297), u1_struct_0(A_301)) | ~v1_funct_1(D_298) | ~m1_pre_topc(C_299, B_297) | v2_struct_0(C_299) | ~l1_pre_topc(B_297) | ~v2_pre_topc(B_297) | v2_struct_0(B_297) | ~l1_pre_topc(A_301) | ~v2_pre_topc(A_301) | v2_struct_0(A_301))), inference(cnfTransformation, [status(thm)], [f_250])).
% 10.32/3.83  tff(c_1393, plain, (![B_377, D_378, B_379, A_380]: (r2_hidden('#skF_2'(B_377, D_378, B_379, k4_tmap_1(A_380, B_379), A_380), u1_struct_0(B_379)) | r2_funct_2(u1_struct_0(B_379), u1_struct_0(A_380), k2_tmap_1(B_377, A_380, D_378, B_379), k4_tmap_1(A_380, B_379)) | ~v1_funct_2(k4_tmap_1(A_380, B_379), u1_struct_0(B_379), u1_struct_0(A_380)) | ~v1_funct_1(k4_tmap_1(A_380, B_379)) | ~m1_subset_1(D_378, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_377), u1_struct_0(A_380)))) | ~v1_funct_2(D_378, u1_struct_0(B_377), u1_struct_0(A_380)) | ~v1_funct_1(D_378) | ~m1_pre_topc(B_379, B_377) | v2_struct_0(B_379) | ~l1_pre_topc(B_377) | ~v2_pre_topc(B_377) | v2_struct_0(B_377) | ~m1_pre_topc(B_379, A_380) | ~l1_pre_topc(A_380) | ~v2_pre_topc(A_380) | v2_struct_0(A_380))), inference(resolution, [status(thm)], [c_30, c_676])).
% 10.32/3.83  tff(c_1398, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_421, c_1393])).
% 10.32/3.83  tff(c_1401, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_102, c_86, c_382, c_58, c_56, c_54, c_1253, c_1282, c_1398])).
% 10.32/3.83  tff(c_1402, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_1321, c_1401])).
% 10.32/3.83  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.32/3.83  tff(c_1410, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_1402, c_2])).
% 10.32/3.83  tff(c_1420, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_115, c_1410])).
% 10.32/3.83  tff(c_1422, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_112])).
% 10.32/3.83  tff(c_1441, plain, (![A_386, B_387, D_388]: (r2_funct_2(A_386, B_387, D_388, D_388) | ~m1_subset_1(D_388, k1_zfmisc_1(k2_zfmisc_1(A_386, B_387))) | ~v1_funct_2(D_388, A_386, B_387) | ~v1_funct_1(D_388))), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.32/3.83  tff(c_1443, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', '#skF_5') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_1441])).
% 10.32/3.83  tff(c_1446, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_1443])).
% 10.32/3.83  tff(c_1483, plain, (![B_418, D_414, C_415, E_416, A_417]: (v1_funct_1(k3_tmap_1(A_417, B_418, C_415, D_414, E_416)) | ~m1_subset_1(E_416, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_415), u1_struct_0(B_418)))) | ~v1_funct_2(E_416, u1_struct_0(C_415), u1_struct_0(B_418)) | ~v1_funct_1(E_416) | ~m1_pre_topc(D_414, A_417) | ~m1_pre_topc(C_415, A_417) | ~l1_pre_topc(B_418) | ~v2_pre_topc(B_418) | v2_struct_0(B_418) | ~l1_pre_topc(A_417) | ~v2_pre_topc(A_417) | v2_struct_0(A_417))), inference(cnfTransformation, [status(thm)], [f_187])).
% 10.32/3.83  tff(c_1487, plain, (![A_417, D_414]: (v1_funct_1(k3_tmap_1(A_417, '#skF_3', '#skF_4', D_414, '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_414, A_417) | ~m1_pre_topc('#skF_4', A_417) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_417) | ~v2_pre_topc(A_417) | v2_struct_0(A_417))), inference(resolution, [status(thm)], [c_54, c_1483])).
% 10.32/3.83  tff(c_1491, plain, (![A_417, D_414]: (v1_funct_1(k3_tmap_1(A_417, '#skF_3', '#skF_4', D_414, '#skF_5')) | ~m1_pre_topc(D_414, A_417) | ~m1_pre_topc('#skF_4', A_417) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_417) | ~v2_pre_topc(A_417) | v2_struct_0(A_417))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_56, c_1487])).
% 10.32/3.83  tff(c_1492, plain, (![A_417, D_414]: (v1_funct_1(k3_tmap_1(A_417, '#skF_3', '#skF_4', D_414, '#skF_5')) | ~m1_pre_topc(D_414, A_417) | ~m1_pre_topc('#skF_4', A_417) | ~l1_pre_topc(A_417) | ~v2_pre_topc(A_417) | v2_struct_0(A_417))), inference(negUnitSimplification, [status(thm)], [c_68, c_1491])).
% 10.32/3.83  tff(c_1535, plain, (![D_439, E_441, A_442, B_443, C_440]: (v1_funct_2(k3_tmap_1(A_442, B_443, C_440, D_439, E_441), u1_struct_0(D_439), u1_struct_0(B_443)) | ~m1_subset_1(E_441, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_440), u1_struct_0(B_443)))) | ~v1_funct_2(E_441, u1_struct_0(C_440), u1_struct_0(B_443)) | ~v1_funct_1(E_441) | ~m1_pre_topc(D_439, A_442) | ~m1_pre_topc(C_440, A_442) | ~l1_pre_topc(B_443) | ~v2_pre_topc(B_443) | v2_struct_0(B_443) | ~l1_pre_topc(A_442) | ~v2_pre_topc(A_442) | v2_struct_0(A_442))), inference(cnfTransformation, [status(thm)], [f_187])).
% 10.32/3.83  tff(c_1539, plain, (![A_442, D_439]: (v1_funct_2(k3_tmap_1(A_442, '#skF_3', '#skF_4', D_439, '#skF_5'), u1_struct_0(D_439), u1_struct_0('#skF_3')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_439, A_442) | ~m1_pre_topc('#skF_4', A_442) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_442) | ~v2_pre_topc(A_442) | v2_struct_0(A_442))), inference(resolution, [status(thm)], [c_54, c_1535])).
% 10.32/3.83  tff(c_1543, plain, (![A_442, D_439]: (v1_funct_2(k3_tmap_1(A_442, '#skF_3', '#skF_4', D_439, '#skF_5'), u1_struct_0(D_439), u1_struct_0('#skF_3')) | ~m1_pre_topc(D_439, A_442) | ~m1_pre_topc('#skF_4', A_442) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_442) | ~v2_pre_topc(A_442) | v2_struct_0(A_442))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_56, c_1539])).
% 10.32/3.83  tff(c_1544, plain, (![A_442, D_439]: (v1_funct_2(k3_tmap_1(A_442, '#skF_3', '#skF_4', D_439, '#skF_5'), u1_struct_0(D_439), u1_struct_0('#skF_3')) | ~m1_pre_topc(D_439, A_442) | ~m1_pre_topc('#skF_4', A_442) | ~l1_pre_topc(A_442) | ~v2_pre_topc(A_442) | v2_struct_0(A_442))), inference(negUnitSimplification, [status(thm)], [c_68, c_1543])).
% 10.32/3.83  tff(c_1519, plain, (![C_434, B_435, D_436, A_437]: (r2_funct_2(u1_struct_0(C_434), u1_struct_0(B_435), D_436, k3_tmap_1(A_437, B_435, C_434, C_434, D_436)) | ~m1_subset_1(D_436, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_434), u1_struct_0(B_435)))) | ~v1_funct_2(D_436, u1_struct_0(C_434), u1_struct_0(B_435)) | ~v1_funct_1(D_436) | ~m1_pre_topc(C_434, A_437) | v2_struct_0(C_434) | ~l1_pre_topc(B_435) | ~v2_pre_topc(B_435) | v2_struct_0(B_435) | ~l1_pre_topc(A_437) | ~v2_pre_topc(A_437) | v2_struct_0(A_437))), inference(cnfTransformation, [status(thm)], [f_280])).
% 10.32/3.83  tff(c_1523, plain, (![A_437]: (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k3_tmap_1(A_437, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_437) | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_437) | ~v2_pre_topc(A_437) | v2_struct_0(A_437))), inference(resolution, [status(thm)], [c_54, c_1519])).
% 10.32/3.83  tff(c_1527, plain, (![A_437]: (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k3_tmap_1(A_437, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_437) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_437) | ~v2_pre_topc(A_437) | v2_struct_0(A_437))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_56, c_1523])).
% 10.32/3.83  tff(c_1529, plain, (![A_438]: (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k3_tmap_1(A_438, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_438) | ~l1_pre_topc(A_438) | ~v2_pre_topc(A_438) | v2_struct_0(A_438))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_1527])).
% 10.32/3.83  tff(c_1531, plain, (![A_438]: (k3_tmap_1(A_438, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~m1_subset_1(k3_tmap_1(A_438, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k3_tmap_1(A_438, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k3_tmap_1(A_438, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_438) | ~l1_pre_topc(A_438) | ~v2_pre_topc(A_438) | v2_struct_0(A_438))), inference(resolution, [status(thm)], [c_1529, c_12])).
% 10.32/3.83  tff(c_1575, plain, (![A_458]: (k3_tmap_1(A_458, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~m1_subset_1(k3_tmap_1(A_458, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k3_tmap_1(A_458, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k3_tmap_1(A_458, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_458) | ~l1_pre_topc(A_458) | ~v2_pre_topc(A_458) | v2_struct_0(A_458))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_1531])).
% 10.32/3.83  tff(c_1579, plain, (![A_74]: (k3_tmap_1(A_74, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~v1_funct_2(k3_tmap_1(A_74, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k3_tmap_1(A_74, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_74) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74) | v2_struct_0(A_74))), inference(resolution, [status(thm)], [c_24, c_1575])).
% 10.32/3.83  tff(c_1582, plain, (![A_74]: (k3_tmap_1(A_74, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~v1_funct_2(k3_tmap_1(A_74, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k3_tmap_1(A_74, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_74) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74) | v2_struct_0(A_74))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_56, c_54, c_1579])).
% 10.32/3.83  tff(c_1584, plain, (![A_459]: (k3_tmap_1(A_459, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~v1_funct_2(k3_tmap_1(A_459, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k3_tmap_1(A_459, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_459) | ~l1_pre_topc(A_459) | ~v2_pre_topc(A_459) | v2_struct_0(A_459))), inference(negUnitSimplification, [status(thm)], [c_68, c_1582])).
% 10.32/3.83  tff(c_1590, plain, (![A_460]: (k3_tmap_1(A_460, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~v1_funct_1(k3_tmap_1(A_460, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_460) | ~l1_pre_topc(A_460) | ~v2_pre_topc(A_460) | v2_struct_0(A_460))), inference(resolution, [status(thm)], [c_1544, c_1584])).
% 10.32/3.83  tff(c_1596, plain, (![A_461]: (k3_tmap_1(A_461, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~m1_pre_topc('#skF_4', A_461) | ~l1_pre_topc(A_461) | ~v2_pre_topc(A_461) | v2_struct_0(A_461))), inference(resolution, [status(thm)], [c_1492, c_1590])).
% 10.32/3.83  tff(c_1603, plain, (k3_tmap_1('#skF_3', '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_1596])).
% 10.32/3.83  tff(c_1610, plain, (k3_tmap_1('#skF_3', '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1603])).
% 10.32/3.83  tff(c_1611, plain, (k3_tmap_1('#skF_3', '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_68, c_1610])).
% 10.32/3.83  tff(c_1668, plain, (![D_463, A_465, B_462, C_464, E_466]: (k3_tmap_1(A_465, B_462, C_464, D_463, E_466)=k2_partfun1(u1_struct_0(C_464), u1_struct_0(B_462), E_466, u1_struct_0(D_463)) | ~m1_pre_topc(D_463, C_464) | ~m1_subset_1(E_466, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_464), u1_struct_0(B_462)))) | ~v1_funct_2(E_466, u1_struct_0(C_464), u1_struct_0(B_462)) | ~v1_funct_1(E_466) | ~m1_pre_topc(D_463, A_465) | ~m1_pre_topc(C_464, A_465) | ~l1_pre_topc(B_462) | ~v2_pre_topc(B_462) | v2_struct_0(B_462) | ~l1_pre_topc(A_465) | ~v2_pre_topc(A_465) | v2_struct_0(A_465))), inference(cnfTransformation, [status(thm)], [f_157])).
% 10.32/3.83  tff(c_1674, plain, (![A_465, D_463]: (k3_tmap_1(A_465, '#skF_3', '#skF_4', D_463, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_463)) | ~m1_pre_topc(D_463, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_463, A_465) | ~m1_pre_topc('#skF_4', A_465) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_465) | ~v2_pre_topc(A_465) | v2_struct_0(A_465))), inference(resolution, [status(thm)], [c_54, c_1668])).
% 10.32/3.83  tff(c_1679, plain, (![A_465, D_463]: (k3_tmap_1(A_465, '#skF_3', '#skF_4', D_463, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_463)) | ~m1_pre_topc(D_463, '#skF_4') | ~m1_pre_topc(D_463, A_465) | ~m1_pre_topc('#skF_4', A_465) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_465) | ~v2_pre_topc(A_465) | v2_struct_0(A_465))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_56, c_1674])).
% 10.32/3.83  tff(c_1681, plain, (![A_467, D_468]: (k3_tmap_1(A_467, '#skF_3', '#skF_4', D_468, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_468)) | ~m1_pre_topc(D_468, '#skF_4') | ~m1_pre_topc(D_468, A_467) | ~m1_pre_topc('#skF_4', A_467) | ~l1_pre_topc(A_467) | ~v2_pre_topc(A_467) | v2_struct_0(A_467))), inference(negUnitSimplification, [status(thm)], [c_68, c_1679])).
% 10.32/3.83  tff(c_1685, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_3', '#skF_4', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_1681])).
% 10.32/3.83  tff(c_1689, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0('#skF_4'))='#skF_5' | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_1611, c_1685])).
% 10.32/3.83  tff(c_1690, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0('#skF_4'))='#skF_5' | ~m1_pre_topc('#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_68, c_1689])).
% 10.32/3.83  tff(c_1691, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_1690])).
% 10.32/3.83  tff(c_1694, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_36, c_1691])).
% 10.32/3.83  tff(c_1698, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_1694])).
% 10.32/3.83  tff(c_1700, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_1690])).
% 10.32/3.83  tff(c_1699, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0('#skF_4'))='#skF_5'), inference(splitRight, [status(thm)], [c_1690])).
% 10.32/3.83  tff(c_1493, plain, (![A_419, B_420, C_421, D_422]: (k2_partfun1(u1_struct_0(A_419), u1_struct_0(B_420), C_421, u1_struct_0(D_422))=k2_tmap_1(A_419, B_420, C_421, D_422) | ~m1_pre_topc(D_422, A_419) | ~m1_subset_1(C_421, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_419), u1_struct_0(B_420)))) | ~v1_funct_2(C_421, u1_struct_0(A_419), u1_struct_0(B_420)) | ~v1_funct_1(C_421) | ~l1_pre_topc(B_420) | ~v2_pre_topc(B_420) | v2_struct_0(B_420) | ~l1_pre_topc(A_419) | ~v2_pre_topc(A_419) | v2_struct_0(A_419))), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.32/3.83  tff(c_1497, plain, (![D_422]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_422))=k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_422) | ~m1_pre_topc(D_422, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_1493])).
% 10.32/3.83  tff(c_1501, plain, (![D_422]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_422))=k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_422) | ~m1_pre_topc(D_422, '#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_86, c_66, c_64, c_58, c_56, c_1497])).
% 10.32/3.83  tff(c_1502, plain, (![D_422]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_422))=k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_422) | ~m1_pre_topc(D_422, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_62, c_68, c_1501])).
% 10.32/3.83  tff(c_1732, plain, (k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4')='#skF_5' | ~m1_pre_topc('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1699, c_1502])).
% 10.32/3.83  tff(c_1739, plain, (k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1700, c_1732])).
% 10.32/3.83  tff(c_1994, plain, (![B_484, D_485, E_487, A_488, C_486]: (r2_hidden('#skF_2'(B_484, D_485, C_486, E_487, A_488), u1_struct_0(C_486)) | r2_funct_2(u1_struct_0(C_486), u1_struct_0(A_488), k2_tmap_1(B_484, A_488, D_485, C_486), E_487) | ~m1_subset_1(E_487, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_486), u1_struct_0(A_488)))) | ~v1_funct_2(E_487, u1_struct_0(C_486), u1_struct_0(A_488)) | ~v1_funct_1(E_487) | ~m1_subset_1(D_485, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_484), u1_struct_0(A_488)))) | ~v1_funct_2(D_485, u1_struct_0(B_484), u1_struct_0(A_488)) | ~v1_funct_1(D_485) | ~m1_pre_topc(C_486, B_484) | v2_struct_0(C_486) | ~l1_pre_topc(B_484) | ~v2_pre_topc(B_484) | v2_struct_0(B_484) | ~l1_pre_topc(A_488) | ~v2_pre_topc(A_488) | v2_struct_0(A_488))), inference(cnfTransformation, [status(thm)], [f_250])).
% 10.32/3.83  tff(c_2554, plain, (![B_547, D_548, B_549, A_550]: (r2_hidden('#skF_2'(B_547, D_548, B_549, k4_tmap_1(A_550, B_549), A_550), u1_struct_0(B_549)) | r2_funct_2(u1_struct_0(B_549), u1_struct_0(A_550), k2_tmap_1(B_547, A_550, D_548, B_549), k4_tmap_1(A_550, B_549)) | ~v1_funct_2(k4_tmap_1(A_550, B_549), u1_struct_0(B_549), u1_struct_0(A_550)) | ~v1_funct_1(k4_tmap_1(A_550, B_549)) | ~m1_subset_1(D_548, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_547), u1_struct_0(A_550)))) | ~v1_funct_2(D_548, u1_struct_0(B_547), u1_struct_0(A_550)) | ~v1_funct_1(D_548) | ~m1_pre_topc(B_549, B_547) | v2_struct_0(B_549) | ~l1_pre_topc(B_547) | ~v2_pre_topc(B_547) | v2_struct_0(B_547) | ~m1_pre_topc(B_549, A_550) | ~l1_pre_topc(A_550) | ~v2_pre_topc(A_550) | v2_struct_0(A_550))), inference(resolution, [status(thm)], [c_30, c_1994])).
% 10.32/3.83  tff(c_2559, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1739, c_2554])).
% 10.32/3.83  tff(c_2562, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_102, c_86, c_1700, c_58, c_56, c_54, c_2559])).
% 10.32/3.83  tff(c_2563, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_2562])).
% 10.32/3.83  tff(c_2564, plain, (~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_2563])).
% 10.32/3.83  tff(c_2567, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_2564])).
% 10.32/3.83  tff(c_2570, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_2567])).
% 10.32/3.83  tff(c_2572, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_2570])).
% 10.32/3.83  tff(c_2574, plain, (v1_funct_1(k4_tmap_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_2563])).
% 10.32/3.83  tff(c_2573, plain, (~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_2563])).
% 10.32/3.83  tff(c_2593, plain, (~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_2573])).
% 10.32/3.83  tff(c_2596, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_2593])).
% 10.32/3.83  tff(c_2599, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_2596])).
% 10.32/3.83  tff(c_2601, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_2599])).
% 10.32/3.83  tff(c_2603, plain, (v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_2573])).
% 10.32/3.83  tff(c_2602, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_2573])).
% 10.32/3.83  tff(c_2604, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_2602])).
% 10.32/3.83  tff(c_2606, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5' | ~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_2604, c_12])).
% 10.32/3.83  tff(c_2609, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5' | ~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2574, c_2603, c_2606])).
% 10.32/3.83  tff(c_2631, plain, (~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(splitLeft, [status(thm)], [c_2609])).
% 10.32/3.83  tff(c_2634, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_30, c_2631])).
% 10.32/3.83  tff(c_2637, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_2634])).
% 10.32/3.83  tff(c_2639, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_2637])).
% 10.32/3.83  tff(c_2640, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_2609])).
% 10.32/3.83  tff(c_2645, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2640, c_50])).
% 10.32/3.83  tff(c_2651, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1446, c_2645])).
% 10.32/3.83  tff(c_2653, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_2602])).
% 10.32/3.83  tff(c_1600, plain, (k3_tmap_1('#skF_4', '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_36, c_1596])).
% 10.32/3.83  tff(c_1606, plain, (k3_tmap_1('#skF_4', '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_102, c_1600])).
% 10.32/3.83  tff(c_1607, plain, (k3_tmap_1('#skF_4', '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_62, c_1606])).
% 10.32/3.83  tff(c_1796, plain, (![D_471, C_472, B_470, A_474, E_473]: (m1_subset_1('#skF_2'(B_470, D_471, C_472, E_473, A_474), u1_struct_0(B_470)) | r2_funct_2(u1_struct_0(C_472), u1_struct_0(A_474), k2_tmap_1(B_470, A_474, D_471, C_472), E_473) | ~m1_subset_1(E_473, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_472), u1_struct_0(A_474)))) | ~v1_funct_2(E_473, u1_struct_0(C_472), u1_struct_0(A_474)) | ~v1_funct_1(E_473) | ~m1_subset_1(D_471, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_470), u1_struct_0(A_474)))) | ~v1_funct_2(D_471, u1_struct_0(B_470), u1_struct_0(A_474)) | ~v1_funct_1(D_471) | ~m1_pre_topc(C_472, B_470) | v2_struct_0(C_472) | ~l1_pre_topc(B_470) | ~v2_pre_topc(B_470) | v2_struct_0(B_470) | ~l1_pre_topc(A_474) | ~v2_pre_topc(A_474) | v2_struct_0(A_474))), inference(cnfTransformation, [status(thm)], [f_250])).
% 10.32/3.83  tff(c_2685, plain, (![B_560, D_561, B_562, A_563]: (m1_subset_1('#skF_2'(B_560, D_561, B_562, k4_tmap_1(A_563, B_562), A_563), u1_struct_0(B_560)) | r2_funct_2(u1_struct_0(B_562), u1_struct_0(A_563), k2_tmap_1(B_560, A_563, D_561, B_562), k4_tmap_1(A_563, B_562)) | ~v1_funct_2(k4_tmap_1(A_563, B_562), u1_struct_0(B_562), u1_struct_0(A_563)) | ~v1_funct_1(k4_tmap_1(A_563, B_562)) | ~m1_subset_1(D_561, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_560), u1_struct_0(A_563)))) | ~v1_funct_2(D_561, u1_struct_0(B_560), u1_struct_0(A_563)) | ~v1_funct_1(D_561) | ~m1_pre_topc(B_562, B_560) | v2_struct_0(B_562) | ~l1_pre_topc(B_560) | ~v2_pre_topc(B_560) | v2_struct_0(B_560) | ~m1_pre_topc(B_562, A_563) | ~l1_pre_topc(A_563) | ~v2_pre_topc(A_563) | v2_struct_0(A_563))), inference(resolution, [status(thm)], [c_30, c_1796])).
% 10.32/3.83  tff(c_2700, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1739, c_2685])).
% 10.32/3.83  tff(c_2706, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_102, c_86, c_1700, c_58, c_56, c_54, c_2574, c_2603, c_2700])).
% 10.32/3.83  tff(c_2707, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_2653, c_2706])).
% 10.32/3.83  tff(c_18, plain, (![C_27, A_21, B_25]: (m1_subset_1(C_27, u1_struct_0(A_21)) | ~m1_subset_1(C_27, u1_struct_0(B_25)) | ~m1_pre_topc(B_25, A_21) | v2_struct_0(B_25) | ~l1_pre_topc(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_98])).
% 10.32/3.83  tff(c_2716, plain, (![A_21]: (m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'), u1_struct_0(A_21)) | ~m1_pre_topc('#skF_4', A_21) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_21) | v2_struct_0(A_21))), inference(resolution, [status(thm)], [c_2707, c_18])).
% 10.32/3.83  tff(c_2731, plain, (![A_564]: (m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'), u1_struct_0(A_564)) | ~m1_pre_topc('#skF_4', A_564) | ~l1_pre_topc(A_564) | v2_struct_0(A_564))), inference(negUnitSimplification, [status(thm)], [c_62, c_2716])).
% 10.32/3.83  tff(c_2652, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_2602])).
% 10.32/3.83  tff(c_52, plain, (![D_184]: (k1_funct_1('#skF_5', D_184)=D_184 | ~r2_hidden(D_184, u1_struct_0('#skF_4')) | ~m1_subset_1(D_184, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_342])).
% 10.32/3.83  tff(c_2681, plain, (k1_funct_1('#skF_5', '#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'))='#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3') | ~m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_2652, c_52])).
% 10.32/3.83  tff(c_2683, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_2681])).
% 10.32/3.83  tff(c_2737, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_2731, c_2683])).
% 10.32/3.83  tff(c_2751, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_2737])).
% 10.32/3.83  tff(c_2753, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_2751])).
% 10.32/3.83  tff(c_2754, plain, (k1_funct_1('#skF_5', '#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'))='#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_2681])).
% 10.32/3.83  tff(c_1686, plain, (![A_81]: (k3_tmap_1(A_81, '#skF_3', '#skF_4', A_81, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(A_81)) | ~m1_pre_topc(A_81, '#skF_4') | ~m1_pre_topc('#skF_4', A_81) | ~v2_pre_topc(A_81) | v2_struct_0(A_81) | ~l1_pre_topc(A_81))), inference(resolution, [status(thm)], [c_36, c_1681])).
% 10.32/3.83  tff(c_1749, plain, (![A_469]: (k3_tmap_1(A_469, '#skF_3', '#skF_4', A_469, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(A_469)) | ~m1_pre_topc(A_469, '#skF_4') | ~m1_pre_topc('#skF_4', A_469) | ~v2_pre_topc(A_469) | v2_struct_0(A_469) | ~l1_pre_topc(A_469))), inference(resolution, [status(thm)], [c_36, c_1681])).
% 10.32/3.83  tff(c_1764, plain, (![A_469]: (m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(A_469)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_469), u1_struct_0('#skF_3')))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(A_469, A_469) | ~m1_pre_topc('#skF_4', A_469) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_469) | ~v2_pre_topc(A_469) | v2_struct_0(A_469) | ~m1_pre_topc(A_469, '#skF_4') | ~m1_pre_topc('#skF_4', A_469) | ~v2_pre_topc(A_469) | v2_struct_0(A_469) | ~l1_pre_topc(A_469))), inference(superposition, [status(thm), theory('equality')], [c_1749, c_24])).
% 10.32/3.83  tff(c_1789, plain, (![A_469]: (m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(A_469)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_469), u1_struct_0('#skF_3')))) | ~m1_pre_topc(A_469, A_469) | v2_struct_0('#skF_3') | ~m1_pre_topc(A_469, '#skF_4') | ~m1_pre_topc('#skF_4', A_469) | ~v2_pre_topc(A_469) | v2_struct_0(A_469) | ~l1_pre_topc(A_469))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_56, c_54, c_1764])).
% 10.32/3.83  tff(c_1823, plain, (![A_476]: (m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(A_476)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_476), u1_struct_0('#skF_3')))) | ~m1_pre_topc(A_476, A_476) | ~m1_pre_topc(A_476, '#skF_4') | ~m1_pre_topc('#skF_4', A_476) | ~v2_pre_topc(A_476) | v2_struct_0(A_476) | ~l1_pre_topc(A_476))), inference(negUnitSimplification, [status(thm)], [c_68, c_1789])).
% 10.32/3.83  tff(c_1842, plain, (![A_81]: (m1_subset_1(k3_tmap_1(A_81, '#skF_3', '#skF_4', A_81, '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_81), u1_struct_0('#skF_3')))) | ~m1_pre_topc(A_81, A_81) | ~m1_pre_topc(A_81, '#skF_4') | ~m1_pre_topc('#skF_4', A_81) | ~v2_pre_topc(A_81) | v2_struct_0(A_81) | ~l1_pre_topc(A_81) | ~m1_pre_topc(A_81, '#skF_4') | ~m1_pre_topc('#skF_4', A_81) | ~v2_pre_topc(A_81) | v2_struct_0(A_81) | ~l1_pre_topc(A_81))), inference(superposition, [status(thm), theory('equality')], [c_1686, c_1823])).
% 10.32/3.83  tff(c_2814, plain, (![B_568, D_569, B_570, A_571]: (m1_subset_1('#skF_2'(B_568, D_569, B_570, k4_tmap_1(A_571, B_570), A_571), u1_struct_0(B_568)) | r2_funct_2(u1_struct_0(B_570), u1_struct_0(A_571), k2_tmap_1(B_568, A_571, D_569, B_570), k4_tmap_1(A_571, B_570)) | ~v1_funct_2(k4_tmap_1(A_571, B_570), u1_struct_0(B_570), u1_struct_0(A_571)) | ~v1_funct_1(k4_tmap_1(A_571, B_570)) | ~m1_subset_1(D_569, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_568), u1_struct_0(A_571)))) | ~v1_funct_2(D_569, u1_struct_0(B_568), u1_struct_0(A_571)) | ~v1_funct_1(D_569) | ~m1_pre_topc(B_570, B_568) | v2_struct_0(B_570) | ~l1_pre_topc(B_568) | ~v2_pre_topc(B_568) | v2_struct_0(B_568) | ~m1_pre_topc(B_570, A_571) | ~l1_pre_topc(A_571) | ~v2_pre_topc(A_571) | v2_struct_0(A_571))), inference(resolution, [status(thm)], [c_30, c_1796])).
% 10.32/3.83  tff(c_2827, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1739, c_2814])).
% 10.32/3.83  tff(c_2833, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_102, c_86, c_1700, c_58, c_56, c_54, c_2574, c_2603, c_2827])).
% 10.32/3.83  tff(c_2834, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_2653, c_2833])).
% 10.32/3.83  tff(c_8, plain, (![A_7, B_8, C_9, D_10]: (k3_funct_2(A_7, B_8, C_9, D_10)=k1_funct_1(C_9, D_10) | ~m1_subset_1(D_10, A_7) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))) | ~v1_funct_2(C_9, A_7, B_8) | ~v1_funct_1(C_9) | v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.32/3.83  tff(c_2838, plain, (![B_8, C_9]: (k3_funct_2(u1_struct_0('#skF_4'), B_8, C_9, '#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'))=k1_funct_1(C_9, '#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3')) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), B_8))) | ~v1_funct_2(C_9, u1_struct_0('#skF_4'), B_8) | ~v1_funct_1(C_9) | v1_xboole_0(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_2834, c_8])).
% 10.32/3.83  tff(c_2887, plain, (![B_575, C_576]: (k3_funct_2(u1_struct_0('#skF_4'), B_575, C_576, '#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'))=k1_funct_1(C_576, '#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3')) | ~m1_subset_1(C_576, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), B_575))) | ~v1_funct_2(C_576, u1_struct_0('#skF_4'), B_575) | ~v1_funct_1(C_576))), inference(negUnitSimplification, [status(thm)], [c_1422, c_2838])).
% 10.32/3.83  tff(c_2891, plain, (k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_4', '#skF_3', '#skF_4', '#skF_4', '#skF_5'), '#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'))=k1_funct_1(k3_tmap_1('#skF_4', '#skF_3', '#skF_4', '#skF_4', '#skF_5'), '#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3')) | ~v1_funct_2(k3_tmap_1('#skF_4', '#skF_3', '#skF_4', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k3_tmap_1('#skF_4', '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', '#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_1842, c_2887])).
% 10.32/3.83  tff(c_2913, plain, (k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', '#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'))='#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_102, c_1700, c_58, c_1607, c_56, c_1607, c_2754, c_1607, c_1607, c_2891])).
% 10.32/3.83  tff(c_2914, plain, (k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', '#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'))='#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_62, c_2913])).
% 10.32/3.83  tff(c_38, plain, (![D_138, A_82, B_114, C_130, E_142]: (k3_funct_2(u1_struct_0(B_114), u1_struct_0(A_82), D_138, '#skF_2'(B_114, D_138, C_130, E_142, A_82))!=k1_funct_1(E_142, '#skF_2'(B_114, D_138, C_130, E_142, A_82)) | r2_funct_2(u1_struct_0(C_130), u1_struct_0(A_82), k2_tmap_1(B_114, A_82, D_138, C_130), E_142) | ~m1_subset_1(E_142, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_130), u1_struct_0(A_82)))) | ~v1_funct_2(E_142, u1_struct_0(C_130), u1_struct_0(A_82)) | ~v1_funct_1(E_142) | ~m1_subset_1(D_138, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_114), u1_struct_0(A_82)))) | ~v1_funct_2(D_138, u1_struct_0(B_114), u1_struct_0(A_82)) | ~v1_funct_1(D_138) | ~m1_pre_topc(C_130, B_114) | v2_struct_0(C_130) | ~l1_pre_topc(B_114) | ~v2_pre_topc(B_114) | v2_struct_0(B_114) | ~l1_pre_topc(A_82) | ~v2_pre_topc(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_250])).
% 10.32/3.83  tff(c_2930, plain, (k1_funct_1(k4_tmap_1('#skF_3', '#skF_4'), '#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'))!='#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3') | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4'), k4_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2914, c_38])).
% 10.32/3.83  tff(c_2934, plain, (k1_funct_1(k4_tmap_1('#skF_3', '#skF_4'), '#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'))!='#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3') | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_102, c_86, c_1700, c_58, c_56, c_54, c_2574, c_2603, c_1739, c_2930])).
% 10.32/3.83  tff(c_2935, plain, (k1_funct_1(k4_tmap_1('#skF_3', '#skF_4'), '#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'))!='#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3') | ~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_2653, c_2934])).
% 10.32/3.83  tff(c_2973, plain, (~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(splitLeft, [status(thm)], [c_2935])).
% 10.32/3.83  tff(c_2976, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_30, c_2973])).
% 10.32/3.83  tff(c_2979, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_2976])).
% 10.32/3.83  tff(c_2981, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_2979])).
% 10.32/3.83  tff(c_2982, plain, (k1_funct_1(k4_tmap_1('#skF_3', '#skF_4'), '#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'))!='#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_2935])).
% 10.32/3.83  tff(c_2755, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_2681])).
% 10.32/3.83  tff(c_1453, plain, (![A_396, B_397, C_398]: (k1_funct_1(k4_tmap_1(A_396, B_397), C_398)=C_398 | ~r2_hidden(C_398, u1_struct_0(B_397)) | ~m1_subset_1(C_398, u1_struct_0(A_396)) | ~m1_pre_topc(B_397, A_396) | v2_struct_0(B_397) | ~l1_pre_topc(A_396) | ~v2_pre_topc(A_396) | v2_struct_0(A_396))), inference(cnfTransformation, [status(thm)], [f_312])).
% 10.32/3.83  tff(c_1460, plain, (![A_396, B_397, A_5]: (k1_funct_1(k4_tmap_1(A_396, B_397), A_5)=A_5 | ~m1_subset_1(A_5, u1_struct_0(A_396)) | ~m1_pre_topc(B_397, A_396) | v2_struct_0(B_397) | ~l1_pre_topc(A_396) | ~v2_pre_topc(A_396) | v2_struct_0(A_396) | v1_xboole_0(u1_struct_0(B_397)) | ~m1_subset_1(A_5, u1_struct_0(B_397)))), inference(resolution, [status(thm)], [c_6, c_1453])).
% 10.32/3.83  tff(c_2757, plain, (![B_397]: (k1_funct_1(k4_tmap_1('#skF_3', B_397), '#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'))='#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3') | ~m1_pre_topc(B_397, '#skF_3') | v2_struct_0(B_397) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | v1_xboole_0(u1_struct_0(B_397)) | ~m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'), u1_struct_0(B_397)))), inference(resolution, [status(thm)], [c_2755, c_1460])).
% 10.32/3.83  tff(c_2767, plain, (![B_397]: (k1_funct_1(k4_tmap_1('#skF_3', B_397), '#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'))='#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3') | ~m1_pre_topc(B_397, '#skF_3') | v2_struct_0(B_397) | v2_struct_0('#skF_3') | v1_xboole_0(u1_struct_0(B_397)) | ~m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'), u1_struct_0(B_397)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_2757])).
% 10.32/3.83  tff(c_9972, plain, (![B_880]: (k1_funct_1(k4_tmap_1('#skF_3', B_880), '#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'))='#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3') | ~m1_pre_topc(B_880, '#skF_3') | v2_struct_0(B_880) | v1_xboole_0(u1_struct_0(B_880)) | ~m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'), u1_struct_0(B_880)))), inference(negUnitSimplification, [status(thm)], [c_68, c_2767])).
% 10.32/3.83  tff(c_9982, plain, (k1_funct_1(k4_tmap_1('#skF_3', '#skF_4'), '#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'))='#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_2834, c_9972])).
% 10.32/3.83  tff(c_9998, plain, (k1_funct_1(k4_tmap_1('#skF_3', '#skF_4'), '#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3'))='#skF_2'('#skF_4', '#skF_5', '#skF_4', k4_tmap_1('#skF_3', '#skF_4'), '#skF_3') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_9982])).
% 10.32/3.83  tff(c_10000, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1422, c_62, c_2982, c_9998])).
% 10.32/3.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.32/3.83  
% 10.32/3.83  Inference rules
% 10.32/3.83  ----------------------
% 10.32/3.83  #Ref     : 0
% 10.32/3.83  #Sup     : 1851
% 10.32/3.83  #Fact    : 0
% 10.32/3.83  #Define  : 0
% 10.32/3.83  #Split   : 22
% 10.32/3.83  #Chain   : 0
% 10.32/3.83  #Close   : 0
% 10.32/3.83  
% 10.32/3.83  Ordering : KBO
% 10.32/3.83  
% 10.32/3.83  Simplification rules
% 10.32/3.83  ----------------------
% 10.32/3.83  #Subsume      : 376
% 10.32/3.83  #Demod        : 6039
% 10.32/3.83  #Tautology    : 614
% 10.32/3.83  #SimpNegUnit  : 971
% 10.32/3.83  #BackRed      : 109
% 10.32/3.83  
% 10.32/3.83  #Partial instantiations: 0
% 10.32/3.83  #Strategies tried      : 1
% 10.32/3.83  
% 10.32/3.83  Timing (in seconds)
% 10.32/3.83  ----------------------
% 10.32/3.83  Preprocessing        : 0.42
% 10.32/3.83  Parsing              : 0.22
% 10.32/3.83  CNF conversion       : 0.04
% 10.32/3.83  Main loop            : 2.58
% 10.32/3.83  Inferencing          : 0.84
% 10.32/3.83  Reduction            : 0.92
% 10.32/3.83  Demodulation         : 0.71
% 10.32/3.83  BG Simplification    : 0.09
% 10.32/3.84  Subsumption          : 0.62
% 10.32/3.84  Abstraction          : 0.13
% 10.32/3.84  MUC search           : 0.00
% 10.32/3.84  Cooper               : 0.00
% 10.32/3.84  Total                : 3.09
% 10.32/3.84  Index Insertion      : 0.00
% 10.32/3.84  Index Deletion       : 0.00
% 10.32/3.84  Index Matching       : 0.00
% 10.32/3.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
