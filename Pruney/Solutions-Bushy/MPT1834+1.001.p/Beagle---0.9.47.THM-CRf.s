%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1834+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:30 EST 2020

% Result     : Theorem 7.62s
% Output     : CNFRefutation 8.02s
% Verified   : 
% Statistics : Number of formulae       :  258 (8224 expanded)
%              Number of leaves         :   42 (2983 expanded)
%              Depth                    :   23
%              Number of atoms          : 1431 (79478 expanded)
%              Number of equality atoms :   19 (1121 expanded)
%              Maximal formula depth    :   28 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v5_pre_topc > v1_funct_2 > r4_tsep_1 > r3_tsep_1 > r1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k10_tmap_1,type,(
    k10_tmap_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r4_tsep_1,type,(
    r4_tsep_1: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r3_tsep_1,type,(
    r3_tsep_1: ( $i * $i * $i ) > $o )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_366,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ( r3_tsep_1(A,B,C)
                <=> ( r1_tsep_1(B,C)
                    & ! [D] :
                        ( ( ~ v2_struct_0(D)
                          & v2_pre_topc(D)
                          & l1_pre_topc(D) )
                       => ! [E] :
                            ( ( v1_funct_1(E)
                              & v1_funct_2(E,u1_struct_0(B),u1_struct_0(D))
                              & v5_pre_topc(E,B,D)
                              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(D)))) )
                           => ! [F] :
                                ( ( v1_funct_1(F)
                                  & v1_funct_2(F,u1_struct_0(C),u1_struct_0(D))
                                  & v5_pre_topc(F,C,D)
                                  & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(D)))) )
                               => ( v1_funct_1(k10_tmap_1(A,D,B,C,E,F))
                                  & v1_funct_2(k10_tmap_1(A,D,B,C,E,F),u1_struct_0(k1_tsep_1(A,B,C)),u1_struct_0(D))
                                  & v5_pre_topc(k10_tmap_1(A,D,B,C,E,F),k1_tsep_1(A,B,C),D)
                                  & m1_subset_1(k10_tmap_1(A,D,B,C,E,F),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,B,C)),u1_struct_0(D)))) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_tmap_1)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_118,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => k1_tsep_1(A,B,C) = k1_tsep_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k1_tsep_1)).

tff(f_190,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( r3_tsep_1(A,B,C)
              <=> ( r1_tsep_1(B,C)
                  & ! [D] :
                      ( ( ~ v2_struct_0(D)
                        & v2_pre_topc(D)
                        & l1_pre_topc(D) )
                     => ! [E] :
                          ( ( v1_funct_1(E)
                            & v1_funct_2(E,u1_struct_0(k1_tsep_1(A,B,C)),u1_struct_0(D))
                            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,B,C)),u1_struct_0(D)))) )
                         => ( ( v1_funct_1(k3_tmap_1(A,D,k1_tsep_1(A,B,C),B,E))
                              & v1_funct_2(k3_tmap_1(A,D,k1_tsep_1(A,B,C),B,E),u1_struct_0(B),u1_struct_0(D))
                              & v5_pre_topc(k3_tmap_1(A,D,k1_tsep_1(A,B,C),B,E),B,D)
                              & m1_subset_1(k3_tmap_1(A,D,k1_tsep_1(A,B,C),B,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(D))))
                              & v1_funct_1(k3_tmap_1(A,D,k1_tsep_1(A,B,C),C,E))
                              & v1_funct_2(k3_tmap_1(A,D,k1_tsep_1(A,B,C),C,E),u1_struct_0(C),u1_struct_0(D))
                              & v5_pre_topc(k3_tmap_1(A,D,k1_tsep_1(A,B,C),C,E),C,D)
                              & m1_subset_1(k3_tmap_1(A,D,k1_tsep_1(A,B,C),C,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(D)))) )
                           => ( v1_funct_1(E)
                              & v1_funct_2(E,u1_struct_0(k1_tsep_1(A,B,C)),u1_struct_0(D))
                              & v5_pre_topc(E,k1_tsep_1(A,B,C),D)
                              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,B,C)),u1_struct_0(D)))) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_tmap_1)).

tff(f_128,axiom,(
    ! [A,B,C] :
      ( ( l1_pre_topc(A)
        & m1_pre_topc(B,A)
        & m1_pre_topc(C,A) )
     => ( r3_tsep_1(A,B,C)
       => r3_tsep_1(A,C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r3_tsep_1)).

tff(f_110,axiom,(
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

tff(f_83,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A)
        & ~ v2_struct_0(D)
        & m1_pre_topc(D,A)
        & v1_funct_1(E)
        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B))))
        & v1_funct_1(F)
        & v1_funct_2(F,u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
     => ( v1_funct_1(k10_tmap_1(A,B,C,D,E,F))
        & v1_funct_2(k10_tmap_1(A,B,C,D,E,F),u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
        & m1_subset_1(k10_tmap_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_tmap_1)).

tff(f_226,axiom,(
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
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) )
                     => r2_funct_2(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B),E,k10_tmap_1(A,B,C,D,k3_tmap_1(A,B,k1_tsep_1(A,C,D),C,E),k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,E))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_tmap_1)).

tff(f_308,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( ( r1_tsep_1(B,C)
                  & r4_tsep_1(A,B,C) )
              <=> r3_tsep_1(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_tsep_1)).

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
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ( r1_tsep_1(C,D)
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                          & v5_pre_topc(E,C,B)
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                       => ! [F] :
                            ( ( v1_funct_1(F)
                              & v1_funct_2(F,u1_struct_0(D),u1_struct_0(B))
                              & v5_pre_topc(F,D,B)
                              & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                           => ( r4_tsep_1(A,C,D)
                             => ( v1_funct_1(k10_tmap_1(A,B,C,D,E,F))
                                & v1_funct_2(k10_tmap_1(A,B,C,D,E,F),u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
                                & v5_pre_topc(k10_tmap_1(A,B,C,D,E,F),k1_tsep_1(A,C,D),B)
                                & m1_subset_1(k10_tmap_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_tmap_1)).

tff(c_90,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_366])).

tff(c_84,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_366])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_366])).

tff(c_88,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_366])).

tff(c_86,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_366])).

tff(c_82,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_366])).

tff(c_78,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_366])).

tff(c_116,plain,
    ( ~ v2_struct_0('#skF_6')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_366])).

tff(c_249,plain,(
    ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_250,plain,(
    ! [B_291,A_292] :
      ( l1_pre_topc(B_291)
      | ~ m1_pre_topc(B_291,A_292)
      | ~ l1_pre_topc(A_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_253,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_250])).

tff(c_259,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_253])).

tff(c_10,plain,(
    ! [A_10] :
      ( l1_struct_0(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_256,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_250])).

tff(c_262,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_256])).

tff(c_222,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | r1_tsep_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_366])).

tff(c_248,plain,(
    r1_tsep_1('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_222])).

tff(c_273,plain,(
    ! [B_293,A_294] :
      ( r1_tsep_1(B_293,A_294)
      | ~ r1_tsep_1(A_294,B_293)
      | ~ l1_struct_0(B_293)
      | ~ l1_struct_0(A_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_276,plain,
    ( r1_tsep_1('#skF_5','#skF_4')
    | ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_248,c_273])).

tff(c_277,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_276])).

tff(c_280,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_277])).

tff(c_284,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_280])).

tff(c_285,plain,
    ( ~ l1_struct_0('#skF_5')
    | r1_tsep_1('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_276])).

tff(c_287,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_285])).

tff(c_292,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_287])).

tff(c_296,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_292])).

tff(c_297,plain,(
    r1_tsep_1('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_285])).

tff(c_316,plain,(
    ! [A_301,C_302,B_303] :
      ( k1_tsep_1(A_301,C_302,B_303) = k1_tsep_1(A_301,B_303,C_302)
      | ~ m1_pre_topc(C_302,A_301)
      | v2_struct_0(C_302)
      | ~ m1_pre_topc(B_303,A_301)
      | v2_struct_0(B_303)
      | ~ l1_pre_topc(A_301)
      | v2_struct_0(A_301) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_318,plain,(
    ! [B_303] :
      ( k1_tsep_1('#skF_3',B_303,'#skF_5') = k1_tsep_1('#skF_3','#skF_5',B_303)
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(B_303,'#skF_3')
      | v2_struct_0(B_303)
      | ~ l1_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_78,c_316])).

tff(c_323,plain,(
    ! [B_303] :
      ( k1_tsep_1('#skF_3',B_303,'#skF_5') = k1_tsep_1('#skF_3','#skF_5',B_303)
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(B_303,'#skF_3')
      | v2_struct_0(B_303)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_318])).

tff(c_329,plain,(
    ! [B_304] :
      ( k1_tsep_1('#skF_3',B_304,'#skF_5') = k1_tsep_1('#skF_3','#skF_5',B_304)
      | ~ m1_pre_topc(B_304,'#skF_3')
      | v2_struct_0(B_304) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_80,c_323])).

tff(c_335,plain,
    ( k1_tsep_1('#skF_3','#skF_5','#skF_4') = k1_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_329])).

tff(c_342,plain,(
    k1_tsep_1('#skF_3','#skF_5','#skF_4') = k1_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_335])).

tff(c_377,plain,(
    ! [A_334,B_335,C_336] :
      ( v1_funct_2('#skF_2'(A_334,B_335,C_336),u1_struct_0(k1_tsep_1(A_334,B_335,C_336)),u1_struct_0('#skF_1'(A_334,B_335,C_336)))
      | r3_tsep_1(A_334,B_335,C_336)
      | ~ r1_tsep_1(B_335,C_336)
      | ~ m1_pre_topc(C_336,A_334)
      | v2_struct_0(C_336)
      | ~ m1_pre_topc(B_335,A_334)
      | v2_struct_0(B_335)
      | ~ l1_pre_topc(A_334)
      | ~ v2_pre_topc(A_334)
      | v2_struct_0(A_334) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_380,plain,
    ( v1_funct_2('#skF_2'('#skF_3','#skF_5','#skF_4'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))
    | r3_tsep_1('#skF_3','#skF_5','#skF_4')
    | ~ r1_tsep_1('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_377])).

tff(c_382,plain,
    ( v1_funct_2('#skF_2'('#skF_3','#skF_5','#skF_4'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))
    | r3_tsep_1('#skF_3','#skF_5','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_78,c_82,c_297,c_380])).

tff(c_383,plain,
    ( v1_funct_2('#skF_2'('#skF_3','#skF_5','#skF_4'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))
    | r3_tsep_1('#skF_3','#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_80,c_84,c_382])).

tff(c_384,plain,(
    r3_tsep_1('#skF_3','#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_383])).

tff(c_20,plain,(
    ! [A_20,C_22,B_21] :
      ( r3_tsep_1(A_20,C_22,B_21)
      | ~ r3_tsep_1(A_20,B_21,C_22)
      | ~ m1_pre_topc(C_22,A_20)
      | ~ m1_pre_topc(B_21,A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_389,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_384,c_20])).

tff(c_396,plain,(
    r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_78,c_82,c_389])).

tff(c_398,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_396])).

tff(c_400,plain,(
    ~ r3_tsep_1('#skF_3','#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_383])).

tff(c_44,plain,(
    ! [A_23,B_51,C_65] :
      ( v1_funct_1('#skF_2'(A_23,B_51,C_65))
      | r3_tsep_1(A_23,B_51,C_65)
      | ~ r1_tsep_1(B_51,C_65)
      | ~ m1_pre_topc(C_65,A_23)
      | v2_struct_0(C_65)
      | ~ m1_pre_topc(B_51,A_23)
      | v2_struct_0(B_51)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_399,plain,(
    v1_funct_2('#skF_2'('#skF_3','#skF_5','#skF_4'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_383])).

tff(c_417,plain,(
    ! [A_343,B_344,C_345] :
      ( m1_subset_1('#skF_2'(A_343,B_344,C_345),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_343,B_344,C_345)),u1_struct_0('#skF_1'(A_343,B_344,C_345)))))
      | r3_tsep_1(A_343,B_344,C_345)
      | ~ r1_tsep_1(B_344,C_345)
      | ~ m1_pre_topc(C_345,A_343)
      | v2_struct_0(C_345)
      | ~ m1_pre_topc(B_344,A_343)
      | v2_struct_0(B_344)
      | ~ l1_pre_topc(A_343)
      | ~ v2_pre_topc(A_343)
      | v2_struct_0(A_343) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_422,plain,
    ( m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))))
    | r3_tsep_1('#skF_3','#skF_5','#skF_4')
    | ~ r1_tsep_1('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_417])).

tff(c_425,plain,
    ( m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))))
    | r3_tsep_1('#skF_3','#skF_5','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_78,c_82,c_297,c_422])).

tff(c_426,plain,(
    m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_80,c_84,c_400,c_425])).

tff(c_14,plain,(
    ! [A_14,B_15,D_17] :
      ( r2_funct_2(A_14,B_15,D_17,D_17)
      | ~ m1_subset_1(D_17,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15)))
      | ~ v1_funct_2(D_17,A_14,B_15)
      | ~ v1_funct_1(D_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_428,plain,
    ( r2_funct_2(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')),'#skF_2'('#skF_3','#skF_5','#skF_4'),'#skF_2'('#skF_3','#skF_5','#skF_4'))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_5','#skF_4'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_426,c_14])).

tff(c_431,plain,
    ( r2_funct_2(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')),'#skF_2'('#skF_3','#skF_5','#skF_4'),'#skF_2'('#skF_3','#skF_5','#skF_4'))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_399,c_428])).

tff(c_432,plain,(
    ~ v1_funct_1('#skF_2'('#skF_3','#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_431])).

tff(c_435,plain,
    ( r3_tsep_1('#skF_3','#skF_5','#skF_4')
    | ~ r1_tsep_1('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_432])).

tff(c_438,plain,
    ( r3_tsep_1('#skF_3','#skF_5','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_78,c_82,c_297,c_435])).

tff(c_440,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_80,c_84,c_400,c_438])).

tff(c_442,plain,(
    v1_funct_1('#skF_2'('#skF_3','#skF_5','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_431])).

tff(c_749,plain,(
    ! [A_401,B_402,C_403] :
      ( ~ m1_subset_1('#skF_2'(A_401,B_402,C_403),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_401,B_402,C_403)),u1_struct_0('#skF_1'(A_401,B_402,C_403)))))
      | ~ v5_pre_topc('#skF_2'(A_401,B_402,C_403),k1_tsep_1(A_401,B_402,C_403),'#skF_1'(A_401,B_402,C_403))
      | ~ v1_funct_2('#skF_2'(A_401,B_402,C_403),u1_struct_0(k1_tsep_1(A_401,B_402,C_403)),u1_struct_0('#skF_1'(A_401,B_402,C_403)))
      | ~ v1_funct_1('#skF_2'(A_401,B_402,C_403))
      | r3_tsep_1(A_401,B_402,C_403)
      | ~ r1_tsep_1(B_402,C_403)
      | ~ m1_pre_topc(C_403,A_401)
      | v2_struct_0(C_403)
      | ~ m1_pre_topc(B_402,A_401)
      | v2_struct_0(B_402)
      | ~ l1_pre_topc(A_401)
      | ~ v2_pre_topc(A_401)
      | v2_struct_0(A_401) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_755,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))))
    | ~ v5_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_5','#skF_4'),'#skF_1'('#skF_3','#skF_5','#skF_4'))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_5','#skF_4'),u1_struct_0(k1_tsep_1('#skF_3','#skF_5','#skF_4')),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_5','#skF_4'))
    | r3_tsep_1('#skF_3','#skF_5','#skF_4')
    | ~ r1_tsep_1('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_749])).

tff(c_758,plain,
    ( ~ v5_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_1'('#skF_3','#skF_5','#skF_4'))
    | r3_tsep_1('#skF_3','#skF_5','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_78,c_82,c_297,c_442,c_399,c_342,c_342,c_426,c_755])).

tff(c_759,plain,(
    ~ v5_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_1'('#skF_3','#skF_5','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_80,c_84,c_400,c_758])).

tff(c_401,plain,(
    ! [A_337,B_338,C_339] :
      ( v1_funct_1(k3_tmap_1(A_337,'#skF_1'(A_337,B_338,C_339),k1_tsep_1(A_337,B_338,C_339),C_339,'#skF_2'(A_337,B_338,C_339)))
      | r3_tsep_1(A_337,B_338,C_339)
      | ~ r1_tsep_1(B_338,C_339)
      | ~ m1_pre_topc(C_339,A_337)
      | v2_struct_0(C_339)
      | ~ m1_pre_topc(B_338,A_337)
      | v2_struct_0(B_338)
      | ~ l1_pre_topc(A_337)
      | ~ v2_pre_topc(A_337)
      | v2_struct_0(A_337) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_404,plain,
    ( v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_5','#skF_4')))
    | r3_tsep_1('#skF_3','#skF_5','#skF_4')
    | ~ r1_tsep_1('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_401])).

tff(c_406,plain,
    ( v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_5','#skF_4')))
    | r3_tsep_1('#skF_3','#skF_5','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_78,c_82,c_297,c_404])).

tff(c_407,plain,(
    v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_5','#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_80,c_84,c_400,c_406])).

tff(c_472,plain,(
    ! [A_355,B_356,C_357] :
      ( v1_funct_2(k3_tmap_1(A_355,'#skF_1'(A_355,B_356,C_357),k1_tsep_1(A_355,B_356,C_357),C_357,'#skF_2'(A_355,B_356,C_357)),u1_struct_0(C_357),u1_struct_0('#skF_1'(A_355,B_356,C_357)))
      | r3_tsep_1(A_355,B_356,C_357)
      | ~ r1_tsep_1(B_356,C_357)
      | ~ m1_pre_topc(C_357,A_355)
      | v2_struct_0(C_357)
      | ~ m1_pre_topc(B_356,A_355)
      | v2_struct_0(B_356)
      | ~ l1_pre_topc(A_355)
      | ~ v2_pre_topc(A_355)
      | v2_struct_0(A_355) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_475,plain,
    ( v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_5','#skF_4')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))
    | r3_tsep_1('#skF_3','#skF_5','#skF_4')
    | ~ r1_tsep_1('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_472])).

tff(c_477,plain,
    ( v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_5','#skF_4')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))
    | r3_tsep_1('#skF_3','#skF_5','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_78,c_82,c_297,c_475])).

tff(c_478,plain,(
    v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_5','#skF_4')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_80,c_84,c_400,c_477])).

tff(c_456,plain,(
    ! [A_349,B_350,C_351] :
      ( v5_pre_topc(k3_tmap_1(A_349,'#skF_1'(A_349,B_350,C_351),k1_tsep_1(A_349,B_350,C_351),C_351,'#skF_2'(A_349,B_350,C_351)),C_351,'#skF_1'(A_349,B_350,C_351))
      | r3_tsep_1(A_349,B_350,C_351)
      | ~ r1_tsep_1(B_350,C_351)
      | ~ m1_pre_topc(C_351,A_349)
      | v2_struct_0(C_351)
      | ~ m1_pre_topc(B_350,A_349)
      | v2_struct_0(B_350)
      | ~ l1_pre_topc(A_349)
      | ~ v2_pre_topc(A_349)
      | v2_struct_0(A_349) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_459,plain,
    ( v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_5','#skF_4')),'#skF_4','#skF_1'('#skF_3','#skF_5','#skF_4'))
    | r3_tsep_1('#skF_3','#skF_5','#skF_4')
    | ~ r1_tsep_1('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_456])).

tff(c_461,plain,
    ( v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_5','#skF_4')),'#skF_4','#skF_1'('#skF_3','#skF_5','#skF_4'))
    | r3_tsep_1('#skF_3','#skF_5','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_78,c_82,c_297,c_459])).

tff(c_462,plain,(
    v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_5','#skF_4')),'#skF_4','#skF_1'('#skF_3','#skF_5','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_80,c_84,c_400,c_461])).

tff(c_479,plain,(
    ! [A_358,B_359,C_360] :
      ( m1_subset_1(k3_tmap_1(A_358,'#skF_1'(A_358,B_359,C_360),k1_tsep_1(A_358,B_359,C_360),C_360,'#skF_2'(A_358,B_359,C_360)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_360),u1_struct_0('#skF_1'(A_358,B_359,C_360)))))
      | r3_tsep_1(A_358,B_359,C_360)
      | ~ r1_tsep_1(B_359,C_360)
      | ~ m1_pre_topc(C_360,A_358)
      | v2_struct_0(C_360)
      | ~ m1_pre_topc(B_359,A_358)
      | v2_struct_0(B_359)
      | ~ l1_pre_topc(A_358)
      | ~ v2_pre_topc(A_358)
      | v2_struct_0(A_358) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_487,plain,
    ( m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))))
    | r3_tsep_1('#skF_3','#skF_5','#skF_4')
    | ~ r1_tsep_1('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_479])).

tff(c_493,plain,
    ( m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))))
    | r3_tsep_1('#skF_3','#skF_5','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_78,c_82,c_297,c_487])).

tff(c_494,plain,(
    m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_80,c_84,c_400,c_493])).

tff(c_46,plain,(
    ! [A_23,B_51,C_65] :
      ( l1_pre_topc('#skF_1'(A_23,B_51,C_65))
      | r3_tsep_1(A_23,B_51,C_65)
      | ~ r1_tsep_1(B_51,C_65)
      | ~ m1_pre_topc(C_65,A_23)
      | v2_struct_0(C_65)
      | ~ m1_pre_topc(B_51,A_23)
      | v2_struct_0(B_51)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_48,plain,(
    ! [A_23,B_51,C_65] :
      ( v2_pre_topc('#skF_1'(A_23,B_51,C_65))
      | r3_tsep_1(A_23,B_51,C_65)
      | ~ r1_tsep_1(B_51,C_65)
      | ~ m1_pre_topc(C_65,A_23)
      | v2_struct_0(C_65)
      | ~ m1_pre_topc(B_51,A_23)
      | v2_struct_0(B_51)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_408,plain,(
    ! [A_340,B_341,C_342] :
      ( v1_funct_1(k3_tmap_1(A_340,'#skF_1'(A_340,B_341,C_342),k1_tsep_1(A_340,B_341,C_342),B_341,'#skF_2'(A_340,B_341,C_342)))
      | r3_tsep_1(A_340,B_341,C_342)
      | ~ r1_tsep_1(B_341,C_342)
      | ~ m1_pre_topc(C_342,A_340)
      | v2_struct_0(C_342)
      | ~ m1_pre_topc(B_341,A_340)
      | v2_struct_0(B_341)
      | ~ l1_pre_topc(A_340)
      | ~ v2_pre_topc(A_340)
      | v2_struct_0(A_340) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_411,plain,
    ( v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4')))
    | r3_tsep_1('#skF_3','#skF_5','#skF_4')
    | ~ r1_tsep_1('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_408])).

tff(c_413,plain,
    ( v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4')))
    | r3_tsep_1('#skF_3','#skF_5','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_78,c_82,c_297,c_411])).

tff(c_414,plain,(
    v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_80,c_84,c_400,c_413])).

tff(c_465,plain,(
    ! [A_352,B_353,C_354] :
      ( v1_funct_2(k3_tmap_1(A_352,'#skF_1'(A_352,B_353,C_354),k1_tsep_1(A_352,B_353,C_354),B_353,'#skF_2'(A_352,B_353,C_354)),u1_struct_0(B_353),u1_struct_0('#skF_1'(A_352,B_353,C_354)))
      | r3_tsep_1(A_352,B_353,C_354)
      | ~ r1_tsep_1(B_353,C_354)
      | ~ m1_pre_topc(C_354,A_352)
      | v2_struct_0(C_354)
      | ~ m1_pre_topc(B_353,A_352)
      | v2_struct_0(B_353)
      | ~ l1_pre_topc(A_352)
      | ~ v2_pre_topc(A_352)
      | v2_struct_0(A_352) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_468,plain,
    ( v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))
    | r3_tsep_1('#skF_3','#skF_5','#skF_4')
    | ~ r1_tsep_1('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_465])).

tff(c_470,plain,
    ( v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))
    | r3_tsep_1('#skF_3','#skF_5','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_78,c_82,c_297,c_468])).

tff(c_471,plain,(
    v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_80,c_84,c_400,c_470])).

tff(c_443,plain,(
    ! [A_346,B_347,C_348] :
      ( v5_pre_topc(k3_tmap_1(A_346,'#skF_1'(A_346,B_347,C_348),k1_tsep_1(A_346,B_347,C_348),B_347,'#skF_2'(A_346,B_347,C_348)),B_347,'#skF_1'(A_346,B_347,C_348))
      | r3_tsep_1(A_346,B_347,C_348)
      | ~ r1_tsep_1(B_347,C_348)
      | ~ m1_pre_topc(C_348,A_346)
      | v2_struct_0(C_348)
      | ~ m1_pre_topc(B_347,A_346)
      | v2_struct_0(B_347)
      | ~ l1_pre_topc(A_346)
      | ~ v2_pre_topc(A_346)
      | v2_struct_0(A_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_446,plain,
    ( v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4')),'#skF_5','#skF_1'('#skF_3','#skF_5','#skF_4'))
    | r3_tsep_1('#skF_3','#skF_5','#skF_4')
    | ~ r1_tsep_1('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_443])).

tff(c_448,plain,
    ( v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4')),'#skF_5','#skF_1'('#skF_3','#skF_5','#skF_4'))
    | r3_tsep_1('#skF_3','#skF_5','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_78,c_82,c_297,c_446])).

tff(c_449,plain,(
    v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4')),'#skF_5','#skF_1'('#skF_3','#skF_5','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_80,c_84,c_400,c_448])).

tff(c_506,plain,(
    ! [A_361,B_362,C_363] :
      ( m1_subset_1(k3_tmap_1(A_361,'#skF_1'(A_361,B_362,C_363),k1_tsep_1(A_361,B_362,C_363),B_362,'#skF_2'(A_361,B_362,C_363)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_362),u1_struct_0('#skF_1'(A_361,B_362,C_363)))))
      | r3_tsep_1(A_361,B_362,C_363)
      | ~ r1_tsep_1(B_362,C_363)
      | ~ m1_pre_topc(C_363,A_361)
      | v2_struct_0(C_363)
      | ~ m1_pre_topc(B_362,A_361)
      | v2_struct_0(B_362)
      | ~ l1_pre_topc(A_361)
      | ~ v2_pre_topc(A_361)
      | v2_struct_0(A_361) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_514,plain,
    ( m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))))
    | r3_tsep_1('#skF_3','#skF_5','#skF_4')
    | ~ r1_tsep_1('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_506])).

tff(c_520,plain,
    ( m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))))
    | r3_tsep_1('#skF_3','#skF_5','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_78,c_82,c_297,c_514])).

tff(c_521,plain,(
    m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_80,c_84,c_400,c_520])).

tff(c_196,plain,(
    ! [D_283,E_287,F_289] :
      ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
      | v1_funct_1(k10_tmap_1('#skF_3',D_283,'#skF_4','#skF_5',E_287,F_289))
      | ~ m1_subset_1(F_289,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(D_283))))
      | ~ v5_pre_topc(F_289,'#skF_5',D_283)
      | ~ v1_funct_2(F_289,u1_struct_0('#skF_5'),u1_struct_0(D_283))
      | ~ v1_funct_1(F_289)
      | ~ m1_subset_1(E_287,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(D_283))))
      | ~ v5_pre_topc(E_287,'#skF_4',D_283)
      | ~ v1_funct_2(E_287,u1_struct_0('#skF_4'),u1_struct_0(D_283))
      | ~ v1_funct_1(E_287)
      | ~ l1_pre_topc(D_283)
      | ~ v2_pre_topc(D_283)
      | v2_struct_0(D_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_366])).

tff(c_347,plain,(
    ! [D_283,E_287,F_289] :
      ( v1_funct_1(k10_tmap_1('#skF_3',D_283,'#skF_4','#skF_5',E_287,F_289))
      | ~ m1_subset_1(F_289,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(D_283))))
      | ~ v5_pre_topc(F_289,'#skF_5',D_283)
      | ~ v1_funct_2(F_289,u1_struct_0('#skF_5'),u1_struct_0(D_283))
      | ~ v1_funct_1(F_289)
      | ~ m1_subset_1(E_287,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(D_283))))
      | ~ v5_pre_topc(E_287,'#skF_4',D_283)
      | ~ v1_funct_2(E_287,u1_struct_0('#skF_4'),u1_struct_0(D_283))
      | ~ v1_funct_1(E_287)
      | ~ l1_pre_topc(D_283)
      | ~ v2_pre_topc(D_283)
      | v2_struct_0(D_283) ) ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_196])).

tff(c_525,plain,(
    ! [E_287] :
      ( v1_funct_1(k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_5',E_287,k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4'))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4')),'#skF_5','#skF_1'('#skF_3','#skF_5','#skF_4'))
      | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))
      | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4')))
      | ~ m1_subset_1(E_287,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))))
      | ~ v5_pre_topc(E_287,'#skF_4','#skF_1'('#skF_3','#skF_5','#skF_4'))
      | ~ v1_funct_2(E_287,u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))
      | ~ v1_funct_1(E_287)
      | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_5','#skF_4'))
      | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_5','#skF_4'))
      | v2_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_521,c_347])).

tff(c_530,plain,(
    ! [E_287] :
      ( v1_funct_1(k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_5',E_287,k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4'))))
      | ~ m1_subset_1(E_287,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))))
      | ~ v5_pre_topc(E_287,'#skF_4','#skF_1'('#skF_3','#skF_5','#skF_4'))
      | ~ v1_funct_2(E_287,u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))
      | ~ v1_funct_1(E_287)
      | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_5','#skF_4'))
      | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_5','#skF_4'))
      | v2_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_414,c_471,c_449,c_525])).

tff(c_673,plain,(
    ~ v2_pre_topc('#skF_1'('#skF_3','#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_530])).

tff(c_678,plain,
    ( r3_tsep_1('#skF_3','#skF_5','#skF_4')
    | ~ r1_tsep_1('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_673])).

tff(c_681,plain,
    ( r3_tsep_1('#skF_3','#skF_5','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_78,c_82,c_297,c_678])).

tff(c_683,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_80,c_84,c_400,c_681])).

tff(c_684,plain,(
    ! [E_287] :
      ( ~ l1_pre_topc('#skF_1'('#skF_3','#skF_5','#skF_4'))
      | v2_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4'))
      | v1_funct_1(k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_5',E_287,k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4'))))
      | ~ m1_subset_1(E_287,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))))
      | ~ v5_pre_topc(E_287,'#skF_4','#skF_1'('#skF_3','#skF_5','#skF_4'))
      | ~ v1_funct_2(E_287,u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))
      | ~ v1_funct_1(E_287) ) ),
    inference(splitRight,[status(thm)],[c_530])).

tff(c_686,plain,(
    ~ l1_pre_topc('#skF_1'('#skF_3','#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_684])).

tff(c_689,plain,
    ( r3_tsep_1('#skF_3','#skF_5','#skF_4')
    | ~ r1_tsep_1('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_686])).

tff(c_692,plain,
    ( r3_tsep_1('#skF_3','#skF_5','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_78,c_82,c_297,c_689])).

tff(c_694,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_80,c_84,c_400,c_692])).

tff(c_695,plain,(
    ! [E_287] :
      ( v2_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4'))
      | v1_funct_1(k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_5',E_287,k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4'))))
      | ~ m1_subset_1(E_287,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))))
      | ~ v5_pre_topc(E_287,'#skF_4','#skF_1'('#skF_3','#skF_5','#skF_4'))
      | ~ v1_funct_2(E_287,u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))
      | ~ v1_funct_1(E_287) ) ),
    inference(splitRight,[status(thm)],[c_684])).

tff(c_699,plain,(
    v2_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_695])).

tff(c_50,plain,(
    ! [A_23,B_51,C_65] :
      ( ~ v2_struct_0('#skF_1'(A_23,B_51,C_65))
      | r3_tsep_1(A_23,B_51,C_65)
      | ~ r1_tsep_1(B_51,C_65)
      | ~ m1_pre_topc(C_65,A_23)
      | v2_struct_0(C_65)
      | ~ m1_pre_topc(B_51,A_23)
      | v2_struct_0(B_51)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_702,plain,
    ( r3_tsep_1('#skF_3','#skF_5','#skF_4')
    | ~ r1_tsep_1('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_699,c_50])).

tff(c_705,plain,
    ( r3_tsep_1('#skF_3','#skF_5','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_78,c_82,c_297,c_702])).

tff(c_707,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_80,c_84,c_400,c_705])).

tff(c_709,plain,(
    ~ v2_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_695])).

tff(c_685,plain,(
    v2_pre_topc('#skF_1'('#skF_3','#skF_5','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_530])).

tff(c_696,plain,(
    l1_pre_topc('#skF_1'('#skF_3','#skF_5','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_684])).

tff(c_548,plain,(
    ! [E_368,A_369,F_365,C_366,D_367,B_364] :
      ( v1_funct_1(k10_tmap_1(A_369,B_364,C_366,D_367,E_368,F_365))
      | ~ m1_subset_1(F_365,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_367),u1_struct_0(B_364))))
      | ~ v1_funct_2(F_365,u1_struct_0(D_367),u1_struct_0(B_364))
      | ~ v1_funct_1(F_365)
      | ~ m1_subset_1(E_368,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_366),u1_struct_0(B_364))))
      | ~ v1_funct_2(E_368,u1_struct_0(C_366),u1_struct_0(B_364))
      | ~ v1_funct_1(E_368)
      | ~ m1_pre_topc(D_367,A_369)
      | v2_struct_0(D_367)
      | ~ m1_pre_topc(C_366,A_369)
      | v2_struct_0(C_366)
      | ~ l1_pre_topc(B_364)
      | ~ v2_pre_topc(B_364)
      | v2_struct_0(B_364)
      | ~ l1_pre_topc(A_369)
      | ~ v2_pre_topc(A_369)
      | v2_struct_0(A_369) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_550,plain,(
    ! [A_369,C_366,E_368] :
      ( v1_funct_1(k10_tmap_1(A_369,'#skF_1'('#skF_3','#skF_5','#skF_4'),C_366,'#skF_5',E_368,k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4'))))
      | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))
      | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4')))
      | ~ m1_subset_1(E_368,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_366),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))))
      | ~ v1_funct_2(E_368,u1_struct_0(C_366),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))
      | ~ v1_funct_1(E_368)
      | ~ m1_pre_topc('#skF_5',A_369)
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(C_366,A_369)
      | v2_struct_0(C_366)
      | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_5','#skF_4'))
      | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_5','#skF_4'))
      | v2_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4'))
      | ~ l1_pre_topc(A_369)
      | ~ v2_pre_topc(A_369)
      | v2_struct_0(A_369) ) ),
    inference(resolution,[status(thm)],[c_521,c_548])).

tff(c_563,plain,(
    ! [A_369,C_366,E_368] :
      ( v1_funct_1(k10_tmap_1(A_369,'#skF_1'('#skF_3','#skF_5','#skF_4'),C_366,'#skF_5',E_368,k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4'))))
      | ~ m1_subset_1(E_368,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_366),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))))
      | ~ v1_funct_2(E_368,u1_struct_0(C_366),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))
      | ~ v1_funct_1(E_368)
      | ~ m1_pre_topc('#skF_5',A_369)
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(C_366,A_369)
      | v2_struct_0(C_366)
      | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_5','#skF_4'))
      | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_5','#skF_4'))
      | v2_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4'))
      | ~ l1_pre_topc(A_369)
      | ~ v2_pre_topc(A_369)
      | v2_struct_0(A_369) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_414,c_471,c_550])).

tff(c_564,plain,(
    ! [A_369,C_366,E_368] :
      ( v1_funct_1(k10_tmap_1(A_369,'#skF_1'('#skF_3','#skF_5','#skF_4'),C_366,'#skF_5',E_368,k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4'))))
      | ~ m1_subset_1(E_368,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_366),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))))
      | ~ v1_funct_2(E_368,u1_struct_0(C_366),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))
      | ~ v1_funct_1(E_368)
      | ~ m1_pre_topc('#skF_5',A_369)
      | ~ m1_pre_topc(C_366,A_369)
      | v2_struct_0(C_366)
      | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_5','#skF_4'))
      | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_5','#skF_4'))
      | v2_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4'))
      | ~ l1_pre_topc(A_369)
      | ~ v2_pre_topc(A_369)
      | v2_struct_0(A_369) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_563])).

tff(c_858,plain,(
    ! [A_369,C_366,E_368] :
      ( v1_funct_1(k10_tmap_1(A_369,'#skF_1'('#skF_3','#skF_5','#skF_4'),C_366,'#skF_5',E_368,k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4'))))
      | ~ m1_subset_1(E_368,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_366),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))))
      | ~ v1_funct_2(E_368,u1_struct_0(C_366),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))
      | ~ v1_funct_1(E_368)
      | ~ m1_pre_topc('#skF_5',A_369)
      | ~ m1_pre_topc(C_366,A_369)
      | v2_struct_0(C_366)
      | v2_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4'))
      | ~ l1_pre_topc(A_369)
      | ~ v2_pre_topc(A_369)
      | v2_struct_0(A_369) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_685,c_696,c_564])).

tff(c_859,plain,(
    ! [A_369,C_366,E_368] :
      ( v1_funct_1(k10_tmap_1(A_369,'#skF_1'('#skF_3','#skF_5','#skF_4'),C_366,'#skF_5',E_368,k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4'))))
      | ~ m1_subset_1(E_368,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_366),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))))
      | ~ v1_funct_2(E_368,u1_struct_0(C_366),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))
      | ~ v1_funct_1(E_368)
      | ~ m1_pre_topc('#skF_5',A_369)
      | ~ m1_pre_topc(C_366,A_369)
      | v2_struct_0(C_366)
      | ~ l1_pre_topc(A_369)
      | ~ v2_pre_topc(A_369)
      | v2_struct_0(A_369) ) ),
    inference(negUnitSimplification,[status(thm)],[c_709,c_858])).

tff(c_6,plain,(
    ! [B_5,D_7,A_4,E_8,C_6,F_9] :
      ( v1_funct_2(k10_tmap_1(A_4,B_5,C_6,D_7,E_8,F_9),u1_struct_0(k1_tsep_1(A_4,C_6,D_7)),u1_struct_0(B_5))
      | ~ m1_subset_1(F_9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_7),u1_struct_0(B_5))))
      | ~ v1_funct_2(F_9,u1_struct_0(D_7),u1_struct_0(B_5))
      | ~ v1_funct_1(F_9)
      | ~ m1_subset_1(E_8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_6),u1_struct_0(B_5))))
      | ~ v1_funct_2(E_8,u1_struct_0(C_6),u1_struct_0(B_5))
      | ~ v1_funct_1(E_8)
      | ~ m1_pre_topc(D_7,A_4)
      | v2_struct_0(D_7)
      | ~ m1_pre_topc(C_6,A_4)
      | v2_struct_0(C_6)
      | ~ l1_pre_topc(B_5)
      | ~ v2_pre_topc(B_5)
      | v2_struct_0(B_5)
      | ~ l1_pre_topc(A_4)
      | ~ v2_pre_topc(A_4)
      | v2_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_118,plain,(
    ! [D_283,E_287,F_289] :
      ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
      | m1_subset_1(k10_tmap_1('#skF_3',D_283,'#skF_4','#skF_5',E_287,F_289),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0(D_283))))
      | ~ m1_subset_1(F_289,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(D_283))))
      | ~ v5_pre_topc(F_289,'#skF_5',D_283)
      | ~ v1_funct_2(F_289,u1_struct_0('#skF_5'),u1_struct_0(D_283))
      | ~ v1_funct_1(F_289)
      | ~ m1_subset_1(E_287,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(D_283))))
      | ~ v5_pre_topc(E_287,'#skF_4',D_283)
      | ~ v1_funct_2(E_287,u1_struct_0('#skF_4'),u1_struct_0(D_283))
      | ~ v1_funct_1(E_287)
      | ~ l1_pre_topc(D_283)
      | ~ v2_pre_topc(D_283)
      | v2_struct_0(D_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_366])).

tff(c_639,plain,(
    ! [D_283,E_287,F_289] :
      ( m1_subset_1(k10_tmap_1('#skF_3',D_283,'#skF_4','#skF_5',E_287,F_289),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0(D_283))))
      | ~ m1_subset_1(F_289,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(D_283))))
      | ~ v5_pre_topc(F_289,'#skF_5',D_283)
      | ~ v1_funct_2(F_289,u1_struct_0('#skF_5'),u1_struct_0(D_283))
      | ~ v1_funct_1(F_289)
      | ~ m1_subset_1(E_287,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(D_283))))
      | ~ v5_pre_topc(E_287,'#skF_4',D_283)
      | ~ v1_funct_2(E_287,u1_struct_0('#skF_4'),u1_struct_0(D_283))
      | ~ v1_funct_1(E_287)
      | ~ l1_pre_topc(D_283)
      | ~ v2_pre_topc(D_283)
      | v2_struct_0(D_283) ) ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_118])).

tff(c_782,plain,(
    ! [C_410,D_413,B_411,A_414,E_412] :
      ( r2_funct_2(u1_struct_0(k1_tsep_1(A_414,C_410,D_413)),u1_struct_0(B_411),E_412,k10_tmap_1(A_414,B_411,C_410,D_413,k3_tmap_1(A_414,B_411,k1_tsep_1(A_414,C_410,D_413),C_410,E_412),k3_tmap_1(A_414,B_411,k1_tsep_1(A_414,C_410,D_413),D_413,E_412)))
      | ~ m1_subset_1(E_412,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_414,C_410,D_413)),u1_struct_0(B_411))))
      | ~ v1_funct_2(E_412,u1_struct_0(k1_tsep_1(A_414,C_410,D_413)),u1_struct_0(B_411))
      | ~ v1_funct_1(E_412)
      | ~ m1_pre_topc(D_413,A_414)
      | v2_struct_0(D_413)
      | ~ m1_pre_topc(C_410,A_414)
      | v2_struct_0(C_410)
      | ~ l1_pre_topc(B_411)
      | ~ v2_pre_topc(B_411)
      | v2_struct_0(B_411)
      | ~ l1_pre_topc(A_414)
      | ~ v2_pre_topc(A_414)
      | v2_struct_0(A_414) ) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_16,plain,(
    ! [D_17,C_16,A_14,B_15] :
      ( D_17 = C_16
      | ~ r2_funct_2(A_14,B_15,C_16,D_17)
      | ~ m1_subset_1(D_17,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15)))
      | ~ v1_funct_2(D_17,A_14,B_15)
      | ~ v1_funct_1(D_17)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15)))
      | ~ v1_funct_2(C_16,A_14,B_15)
      | ~ v1_funct_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1207,plain,(
    ! [C_558,B_557,E_560,A_559,D_556] :
      ( k10_tmap_1(A_559,B_557,C_558,D_556,k3_tmap_1(A_559,B_557,k1_tsep_1(A_559,C_558,D_556),C_558,E_560),k3_tmap_1(A_559,B_557,k1_tsep_1(A_559,C_558,D_556),D_556,E_560)) = E_560
      | ~ m1_subset_1(k10_tmap_1(A_559,B_557,C_558,D_556,k3_tmap_1(A_559,B_557,k1_tsep_1(A_559,C_558,D_556),C_558,E_560),k3_tmap_1(A_559,B_557,k1_tsep_1(A_559,C_558,D_556),D_556,E_560)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_559,C_558,D_556)),u1_struct_0(B_557))))
      | ~ v1_funct_2(k10_tmap_1(A_559,B_557,C_558,D_556,k3_tmap_1(A_559,B_557,k1_tsep_1(A_559,C_558,D_556),C_558,E_560),k3_tmap_1(A_559,B_557,k1_tsep_1(A_559,C_558,D_556),D_556,E_560)),u1_struct_0(k1_tsep_1(A_559,C_558,D_556)),u1_struct_0(B_557))
      | ~ v1_funct_1(k10_tmap_1(A_559,B_557,C_558,D_556,k3_tmap_1(A_559,B_557,k1_tsep_1(A_559,C_558,D_556),C_558,E_560),k3_tmap_1(A_559,B_557,k1_tsep_1(A_559,C_558,D_556),D_556,E_560)))
      | ~ m1_subset_1(E_560,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_559,C_558,D_556)),u1_struct_0(B_557))))
      | ~ v1_funct_2(E_560,u1_struct_0(k1_tsep_1(A_559,C_558,D_556)),u1_struct_0(B_557))
      | ~ v1_funct_1(E_560)
      | ~ m1_pre_topc(D_556,A_559)
      | v2_struct_0(D_556)
      | ~ m1_pre_topc(C_558,A_559)
      | v2_struct_0(C_558)
      | ~ l1_pre_topc(B_557)
      | ~ v2_pre_topc(B_557)
      | v2_struct_0(B_557)
      | ~ l1_pre_topc(A_559)
      | ~ v2_pre_topc(A_559)
      | v2_struct_0(A_559) ) ),
    inference(resolution,[status(thm)],[c_782,c_16])).

tff(c_1215,plain,(
    ! [D_283,E_560] :
      ( k10_tmap_1('#skF_3',D_283,'#skF_4','#skF_5',k3_tmap_1('#skF_3',D_283,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_560),k3_tmap_1('#skF_3',D_283,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_560)) = E_560
      | ~ v1_funct_2(k10_tmap_1('#skF_3',D_283,'#skF_4','#skF_5',k3_tmap_1('#skF_3',D_283,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_560),k3_tmap_1('#skF_3',D_283,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_560)),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0(D_283))
      | ~ v1_funct_1(k10_tmap_1('#skF_3',D_283,'#skF_4','#skF_5',k3_tmap_1('#skF_3',D_283,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_560),k3_tmap_1('#skF_3',D_283,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_560)))
      | ~ m1_subset_1(E_560,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0(D_283))))
      | ~ v1_funct_2(E_560,u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0(D_283))
      | ~ v1_funct_1(E_560)
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(k3_tmap_1('#skF_3',D_283,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_560),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(D_283))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_3',D_283,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_560),'#skF_5',D_283)
      | ~ v1_funct_2(k3_tmap_1('#skF_3',D_283,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_560),u1_struct_0('#skF_5'),u1_struct_0(D_283))
      | ~ v1_funct_1(k3_tmap_1('#skF_3',D_283,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_560))
      | ~ m1_subset_1(k3_tmap_1('#skF_3',D_283,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_560),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(D_283))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_3',D_283,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_560),'#skF_4',D_283)
      | ~ v1_funct_2(k3_tmap_1('#skF_3',D_283,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_560),u1_struct_0('#skF_4'),u1_struct_0(D_283))
      | ~ v1_funct_1(k3_tmap_1('#skF_3',D_283,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_560))
      | ~ l1_pre_topc(D_283)
      | ~ v2_pre_topc(D_283)
      | v2_struct_0(D_283) ) ),
    inference(resolution,[status(thm)],[c_639,c_1207])).

tff(c_1228,plain,(
    ! [D_283,E_560] :
      ( k10_tmap_1('#skF_3',D_283,'#skF_4','#skF_5',k3_tmap_1('#skF_3',D_283,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_560),k3_tmap_1('#skF_3',D_283,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_560)) = E_560
      | ~ v1_funct_2(k10_tmap_1('#skF_3',D_283,'#skF_4','#skF_5',k3_tmap_1('#skF_3',D_283,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_560),k3_tmap_1('#skF_3',D_283,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_560)),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0(D_283))
      | ~ v1_funct_1(k10_tmap_1('#skF_3',D_283,'#skF_4','#skF_5',k3_tmap_1('#skF_3',D_283,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_560),k3_tmap_1('#skF_3',D_283,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_560)))
      | ~ m1_subset_1(E_560,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0(D_283))))
      | ~ v1_funct_2(E_560,u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0(D_283))
      | ~ v1_funct_1(E_560)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(k3_tmap_1('#skF_3',D_283,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_560),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(D_283))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_3',D_283,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_560),'#skF_5',D_283)
      | ~ v1_funct_2(k3_tmap_1('#skF_3',D_283,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_560),u1_struct_0('#skF_5'),u1_struct_0(D_283))
      | ~ v1_funct_1(k3_tmap_1('#skF_3',D_283,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_560))
      | ~ m1_subset_1(k3_tmap_1('#skF_3',D_283,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_560),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(D_283))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_3',D_283,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_560),'#skF_4',D_283)
      | ~ v1_funct_2(k3_tmap_1('#skF_3',D_283,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_560),u1_struct_0('#skF_4'),u1_struct_0(D_283))
      | ~ v1_funct_1(k3_tmap_1('#skF_3',D_283,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_560))
      | ~ l1_pre_topc(D_283)
      | ~ v2_pre_topc(D_283)
      | v2_struct_0(D_283) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_78,c_1215])).

tff(c_1273,plain,(
    ! [D_582,E_583] :
      ( k10_tmap_1('#skF_3',D_582,'#skF_4','#skF_5',k3_tmap_1('#skF_3',D_582,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_583),k3_tmap_1('#skF_3',D_582,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_583)) = E_583
      | ~ v1_funct_2(k10_tmap_1('#skF_3',D_582,'#skF_4','#skF_5',k3_tmap_1('#skF_3',D_582,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_583),k3_tmap_1('#skF_3',D_582,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_583)),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0(D_582))
      | ~ v1_funct_1(k10_tmap_1('#skF_3',D_582,'#skF_4','#skF_5',k3_tmap_1('#skF_3',D_582,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_583),k3_tmap_1('#skF_3',D_582,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_583)))
      | ~ m1_subset_1(E_583,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0(D_582))))
      | ~ v1_funct_2(E_583,u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0(D_582))
      | ~ v1_funct_1(E_583)
      | ~ m1_subset_1(k3_tmap_1('#skF_3',D_582,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_583),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(D_582))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_3',D_582,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_583),'#skF_5',D_582)
      | ~ v1_funct_2(k3_tmap_1('#skF_3',D_582,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_583),u1_struct_0('#skF_5'),u1_struct_0(D_582))
      | ~ v1_funct_1(k3_tmap_1('#skF_3',D_582,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_583))
      | ~ m1_subset_1(k3_tmap_1('#skF_3',D_582,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_583),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(D_582))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_3',D_582,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_583),'#skF_4',D_582)
      | ~ v1_funct_2(k3_tmap_1('#skF_3',D_582,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_583),u1_struct_0('#skF_4'),u1_struct_0(D_582))
      | ~ v1_funct_1(k3_tmap_1('#skF_3',D_582,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_583))
      | ~ l1_pre_topc(D_582)
      | ~ v2_pre_topc(D_582)
      | v2_struct_0(D_582) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_80,c_1228])).

tff(c_1277,plain,(
    ! [B_5,E_583] :
      ( k10_tmap_1('#skF_3',B_5,'#skF_4','#skF_5',k3_tmap_1('#skF_3',B_5,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_583),k3_tmap_1('#skF_3',B_5,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_583)) = E_583
      | ~ v1_funct_1(k10_tmap_1('#skF_3',B_5,'#skF_4','#skF_5',k3_tmap_1('#skF_3',B_5,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_583),k3_tmap_1('#skF_3',B_5,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_583)))
      | ~ m1_subset_1(E_583,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0(B_5))))
      | ~ v1_funct_2(E_583,u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0(B_5))
      | ~ v1_funct_1(E_583)
      | ~ v5_pre_topc(k3_tmap_1('#skF_3',B_5,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_583),'#skF_5',B_5)
      | ~ v5_pre_topc(k3_tmap_1('#skF_3',B_5,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_583),'#skF_4',B_5)
      | ~ m1_subset_1(k3_tmap_1('#skF_3',B_5,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_583),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_5))))
      | ~ v1_funct_2(k3_tmap_1('#skF_3',B_5,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_583),u1_struct_0('#skF_5'),u1_struct_0(B_5))
      | ~ v1_funct_1(k3_tmap_1('#skF_3',B_5,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_583))
      | ~ m1_subset_1(k3_tmap_1('#skF_3',B_5,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_583),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_5))))
      | ~ v1_funct_2(k3_tmap_1('#skF_3',B_5,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_583),u1_struct_0('#skF_4'),u1_struct_0(B_5))
      | ~ v1_funct_1(k3_tmap_1('#skF_3',B_5,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_583))
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_5)
      | ~ v2_pre_topc(B_5)
      | v2_struct_0(B_5)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_6,c_1273])).

tff(c_1284,plain,(
    ! [B_5,E_583] :
      ( k10_tmap_1('#skF_3',B_5,'#skF_4','#skF_5',k3_tmap_1('#skF_3',B_5,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_583),k3_tmap_1('#skF_3',B_5,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_583)) = E_583
      | ~ v1_funct_1(k10_tmap_1('#skF_3',B_5,'#skF_4','#skF_5',k3_tmap_1('#skF_3',B_5,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_583),k3_tmap_1('#skF_3',B_5,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_583)))
      | ~ m1_subset_1(E_583,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0(B_5))))
      | ~ v1_funct_2(E_583,u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0(B_5))
      | ~ v1_funct_1(E_583)
      | ~ v5_pre_topc(k3_tmap_1('#skF_3',B_5,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_583),'#skF_5',B_5)
      | ~ v5_pre_topc(k3_tmap_1('#skF_3',B_5,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_583),'#skF_4',B_5)
      | ~ m1_subset_1(k3_tmap_1('#skF_3',B_5,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_583),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_5))))
      | ~ v1_funct_2(k3_tmap_1('#skF_3',B_5,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_583),u1_struct_0('#skF_5'),u1_struct_0(B_5))
      | ~ v1_funct_1(k3_tmap_1('#skF_3',B_5,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_583))
      | ~ m1_subset_1(k3_tmap_1('#skF_3',B_5,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_583),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_5))))
      | ~ v1_funct_2(k3_tmap_1('#skF_3',B_5,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_583),u1_struct_0('#skF_4'),u1_struct_0(B_5))
      | ~ v1_funct_1(k3_tmap_1('#skF_3',B_5,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_583))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(B_5)
      | ~ v2_pre_topc(B_5)
      | v2_struct_0(B_5)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_78,c_1277])).

tff(c_1287,plain,(
    ! [B_584,E_585] :
      ( k10_tmap_1('#skF_3',B_584,'#skF_4','#skF_5',k3_tmap_1('#skF_3',B_584,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_585),k3_tmap_1('#skF_3',B_584,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_585)) = E_585
      | ~ v1_funct_1(k10_tmap_1('#skF_3',B_584,'#skF_4','#skF_5',k3_tmap_1('#skF_3',B_584,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_585),k3_tmap_1('#skF_3',B_584,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_585)))
      | ~ m1_subset_1(E_585,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0(B_584))))
      | ~ v1_funct_2(E_585,u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0(B_584))
      | ~ v1_funct_1(E_585)
      | ~ v5_pre_topc(k3_tmap_1('#skF_3',B_584,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_585),'#skF_5',B_584)
      | ~ v5_pre_topc(k3_tmap_1('#skF_3',B_584,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_585),'#skF_4',B_584)
      | ~ m1_subset_1(k3_tmap_1('#skF_3',B_584,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_585),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(B_584))))
      | ~ v1_funct_2(k3_tmap_1('#skF_3',B_584,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_585),u1_struct_0('#skF_5'),u1_struct_0(B_584))
      | ~ v1_funct_1(k3_tmap_1('#skF_3',B_584,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_585))
      | ~ m1_subset_1(k3_tmap_1('#skF_3',B_584,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_585),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_584))))
      | ~ v1_funct_2(k3_tmap_1('#skF_3',B_584,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_585),u1_struct_0('#skF_4'),u1_struct_0(B_584))
      | ~ v1_funct_1(k3_tmap_1('#skF_3',B_584,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_585))
      | ~ l1_pre_topc(B_584)
      | ~ v2_pre_topc(B_584)
      | v2_struct_0(B_584) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_80,c_1284])).

tff(c_1296,plain,
    ( k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_5',k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_5','#skF_4')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4'))) = '#skF_2'('#skF_3','#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_5','#skF_4'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_5','#skF_4'))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4')),'#skF_5','#skF_1'('#skF_3','#skF_5','#skF_4'))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_5','#skF_4')),'#skF_4','#skF_1'('#skF_3','#skF_5','#skF_4'))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4')))
    | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_5','#skF_4'))
    | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_5','#skF_4'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4'))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_5','#skF_4')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_5','#skF_4')))
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_859,c_1287])).

tff(c_1310,plain,
    ( k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_5',k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_5','#skF_4')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4'))) = '#skF_2'('#skF_3','#skF_5','#skF_4')
    | v2_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_78,c_407,c_478,c_494,c_685,c_696,c_414,c_471,c_521,c_462,c_449,c_442,c_399,c_426,c_1296])).

tff(c_1311,plain,(
    k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_5',k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_5','#skF_4')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4'))) = '#skF_2'('#skF_3','#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_709,c_1310])).

tff(c_144,plain,(
    ! [D_283,E_287,F_289] :
      ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
      | v5_pre_topc(k10_tmap_1('#skF_3',D_283,'#skF_4','#skF_5',E_287,F_289),k1_tsep_1('#skF_3','#skF_4','#skF_5'),D_283)
      | ~ m1_subset_1(F_289,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(D_283))))
      | ~ v5_pre_topc(F_289,'#skF_5',D_283)
      | ~ v1_funct_2(F_289,u1_struct_0('#skF_5'),u1_struct_0(D_283))
      | ~ v1_funct_1(F_289)
      | ~ m1_subset_1(E_287,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(D_283))))
      | ~ v5_pre_topc(E_287,'#skF_4',D_283)
      | ~ v1_funct_2(E_287,u1_struct_0('#skF_4'),u1_struct_0(D_283))
      | ~ v1_funct_1(E_287)
      | ~ l1_pre_topc(D_283)
      | ~ v2_pre_topc(D_283)
      | v2_struct_0(D_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_366])).

tff(c_591,plain,(
    ! [D_373,E_374,F_375] :
      ( v5_pre_topc(k10_tmap_1('#skF_3',D_373,'#skF_4','#skF_5',E_374,F_375),k1_tsep_1('#skF_3','#skF_4','#skF_5'),D_373)
      | ~ m1_subset_1(F_375,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(D_373))))
      | ~ v5_pre_topc(F_375,'#skF_5',D_373)
      | ~ v1_funct_2(F_375,u1_struct_0('#skF_5'),u1_struct_0(D_373))
      | ~ v1_funct_1(F_375)
      | ~ m1_subset_1(E_374,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(D_373))))
      | ~ v5_pre_topc(E_374,'#skF_4',D_373)
      | ~ v1_funct_2(E_374,u1_struct_0('#skF_4'),u1_struct_0(D_373))
      | ~ v1_funct_1(E_374)
      | ~ l1_pre_topc(D_373)
      | ~ v2_pre_topc(D_373)
      | v2_struct_0(D_373) ) ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_144])).

tff(c_593,plain,(
    ! [E_374] :
      ( v5_pre_topc(k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_5',E_374,k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4'))),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_1'('#skF_3','#skF_5','#skF_4'))
      | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4')),'#skF_5','#skF_1'('#skF_3','#skF_5','#skF_4'))
      | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))
      | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4')))
      | ~ m1_subset_1(E_374,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))))
      | ~ v5_pre_topc(E_374,'#skF_4','#skF_1'('#skF_3','#skF_5','#skF_4'))
      | ~ v1_funct_2(E_374,u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))
      | ~ v1_funct_1(E_374)
      | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_5','#skF_4'))
      | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_5','#skF_4'))
      | v2_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_521,c_591])).

tff(c_602,plain,(
    ! [E_374] :
      ( v5_pre_topc(k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_5',E_374,k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4'))),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_1'('#skF_3','#skF_5','#skF_4'))
      | ~ m1_subset_1(E_374,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))))
      | ~ v5_pre_topc(E_374,'#skF_4','#skF_1'('#skF_3','#skF_5','#skF_4'))
      | ~ v1_funct_2(E_374,u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))
      | ~ v1_funct_1(E_374)
      | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_5','#skF_4'))
      | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_5','#skF_4'))
      | v2_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_414,c_471,c_449,c_593])).

tff(c_862,plain,(
    ! [E_374] :
      ( v5_pre_topc(k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_5',E_374,k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4'))),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_1'('#skF_3','#skF_5','#skF_4'))
      | ~ m1_subset_1(E_374,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))))
      | ~ v5_pre_topc(E_374,'#skF_4','#skF_1'('#skF_3','#skF_5','#skF_4'))
      | ~ v1_funct_2(E_374,u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))
      | ~ v1_funct_1(E_374)
      | v2_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_685,c_696,c_602])).

tff(c_863,plain,(
    ! [E_374] :
      ( v5_pre_topc(k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),'#skF_4','#skF_5',E_374,k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_5','#skF_4'))),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_1'('#skF_3','#skF_5','#skF_4'))
      | ~ m1_subset_1(E_374,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))))
      | ~ v5_pre_topc(E_374,'#skF_4','#skF_1'('#skF_3','#skF_5','#skF_4'))
      | ~ v1_funct_2(E_374,u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))
      | ~ v1_funct_1(E_374) ) ),
    inference(negUnitSimplification,[status(thm)],[c_709,c_862])).

tff(c_1348,plain,
    ( v5_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_1'('#skF_3','#skF_5','#skF_4'))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_5','#skF_4')),'#skF_4','#skF_1'('#skF_3','#skF_5','#skF_4'))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_5','#skF_4')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_5','#skF_4')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_5','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1311,c_863])).

tff(c_1403,plain,(
    v5_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_1'('#skF_3','#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_478,c_462,c_494,c_1348])).

tff(c_1405,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_759,c_1403])).

tff(c_1407,plain,(
    r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_74,plain,(
    ! [A_170,B_174,C_176] :
      ( r4_tsep_1(A_170,B_174,C_176)
      | ~ r3_tsep_1(A_170,B_174,C_176)
      | ~ m1_pre_topc(C_176,A_170)
      | v2_struct_0(C_176)
      | ~ m1_pre_topc(B_174,A_170)
      | v2_struct_0(B_174)
      | ~ l1_pre_topc(A_170)
      | ~ v2_pre_topc(A_170)
      | v2_struct_0(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_308])).

tff(c_110,plain,
    ( v1_funct_1('#skF_7')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_366])).

tff(c_1424,plain,(
    v1_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1407,c_248,c_110])).

tff(c_108,plain,
    ( v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_6'))
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_366])).

tff(c_1465,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1407,c_248,c_108])).

tff(c_106,plain,
    ( v5_pre_topc('#skF_7','#skF_4','#skF_6')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_366])).

tff(c_1446,plain,(
    v5_pre_topc('#skF_7','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1407,c_248,c_106])).

tff(c_104,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_6'))))
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_366])).

tff(c_1471,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_6')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1407,c_248,c_104])).

tff(c_1406,plain,
    ( ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ v2_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_1409,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_1406])).

tff(c_114,plain,
    ( v2_pre_topc('#skF_6')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_366])).

tff(c_1430,plain,(
    v2_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1407,c_248,c_114])).

tff(c_112,plain,
    ( l1_pre_topc('#skF_6')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_366])).

tff(c_1426,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1407,c_248,c_112])).

tff(c_102,plain,
    ( v1_funct_1('#skF_8')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_366])).

tff(c_1428,plain,(
    v1_funct_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1407,c_248,c_102])).

tff(c_100,plain,
    ( v1_funct_2('#skF_8',u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_366])).

tff(c_1467,plain,(
    v1_funct_2('#skF_8',u1_struct_0('#skF_5'),u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1407,c_248,c_100])).

tff(c_98,plain,
    ( v5_pre_topc('#skF_8','#skF_5','#skF_6')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_366])).

tff(c_1458,plain,(
    v5_pre_topc('#skF_8','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1407,c_248,c_98])).

tff(c_96,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))))
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_366])).

tff(c_1469,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1407,c_248,c_96])).

tff(c_2353,plain,(
    ! [F_788,D_785,A_789,B_787,C_784,E_786] :
      ( v5_pre_topc(k10_tmap_1(A_789,B_787,C_784,D_785,E_786,F_788),k1_tsep_1(A_789,C_784,D_785),B_787)
      | ~ r4_tsep_1(A_789,C_784,D_785)
      | ~ m1_subset_1(F_788,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_785),u1_struct_0(B_787))))
      | ~ v5_pre_topc(F_788,D_785,B_787)
      | ~ v1_funct_2(F_788,u1_struct_0(D_785),u1_struct_0(B_787))
      | ~ v1_funct_1(F_788)
      | ~ m1_subset_1(E_786,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_784),u1_struct_0(B_787))))
      | ~ v5_pre_topc(E_786,C_784,B_787)
      | ~ v1_funct_2(E_786,u1_struct_0(C_784),u1_struct_0(B_787))
      | ~ v1_funct_1(E_786)
      | ~ r1_tsep_1(C_784,D_785)
      | ~ m1_pre_topc(D_785,A_789)
      | v2_struct_0(D_785)
      | ~ m1_pre_topc(C_784,A_789)
      | v2_struct_0(C_784)
      | ~ l1_pre_topc(B_787)
      | ~ v2_pre_topc(B_787)
      | v2_struct_0(B_787)
      | ~ l1_pre_topc(A_789)
      | ~ v2_pre_topc(A_789)
      | v2_struct_0(A_789) ) ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_2369,plain,(
    ! [A_789,C_784,E_786] :
      ( v5_pre_topc(k10_tmap_1(A_789,'#skF_6',C_784,'#skF_5',E_786,'#skF_8'),k1_tsep_1(A_789,C_784,'#skF_5'),'#skF_6')
      | ~ r4_tsep_1(A_789,C_784,'#skF_5')
      | ~ v5_pre_topc('#skF_8','#skF_5','#skF_6')
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_786,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_784),u1_struct_0('#skF_6'))))
      | ~ v5_pre_topc(E_786,C_784,'#skF_6')
      | ~ v1_funct_2(E_786,u1_struct_0(C_784),u1_struct_0('#skF_6'))
      | ~ v1_funct_1(E_786)
      | ~ r1_tsep_1(C_784,'#skF_5')
      | ~ m1_pre_topc('#skF_5',A_789)
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(C_784,A_789)
      | v2_struct_0(C_784)
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc(A_789)
      | ~ v2_pre_topc(A_789)
      | v2_struct_0(A_789) ) ),
    inference(resolution,[status(thm)],[c_1469,c_2353])).

tff(c_2386,plain,(
    ! [A_789,C_784,E_786] :
      ( v5_pre_topc(k10_tmap_1(A_789,'#skF_6',C_784,'#skF_5',E_786,'#skF_8'),k1_tsep_1(A_789,C_784,'#skF_5'),'#skF_6')
      | ~ r4_tsep_1(A_789,C_784,'#skF_5')
      | ~ m1_subset_1(E_786,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_784),u1_struct_0('#skF_6'))))
      | ~ v5_pre_topc(E_786,C_784,'#skF_6')
      | ~ v1_funct_2(E_786,u1_struct_0(C_784),u1_struct_0('#skF_6'))
      | ~ v1_funct_1(E_786)
      | ~ r1_tsep_1(C_784,'#skF_5')
      | ~ m1_pre_topc('#skF_5',A_789)
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(C_784,A_789)
      | v2_struct_0(C_784)
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc(A_789)
      | ~ v2_pre_topc(A_789)
      | v2_struct_0(A_789) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1430,c_1426,c_1428,c_1467,c_1458,c_2369])).

tff(c_2450,plain,(
    ! [A_794,C_795,E_796] :
      ( v5_pre_topc(k10_tmap_1(A_794,'#skF_6',C_795,'#skF_5',E_796,'#skF_8'),k1_tsep_1(A_794,C_795,'#skF_5'),'#skF_6')
      | ~ r4_tsep_1(A_794,C_795,'#skF_5')
      | ~ m1_subset_1(E_796,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_795),u1_struct_0('#skF_6'))))
      | ~ v5_pre_topc(E_796,C_795,'#skF_6')
      | ~ v1_funct_2(E_796,u1_struct_0(C_795),u1_struct_0('#skF_6'))
      | ~ v1_funct_1(E_796)
      | ~ r1_tsep_1(C_795,'#skF_5')
      | ~ m1_pre_topc('#skF_5',A_794)
      | ~ m1_pre_topc(C_795,A_794)
      | v2_struct_0(C_795)
      | ~ l1_pre_topc(A_794)
      | ~ v2_pre_topc(A_794)
      | v2_struct_0(A_794) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1409,c_80,c_2386])).

tff(c_2460,plain,(
    ! [A_794] :
      ( v5_pre_topc(k10_tmap_1(A_794,'#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),k1_tsep_1(A_794,'#skF_4','#skF_5'),'#skF_6')
      | ~ r4_tsep_1(A_794,'#skF_4','#skF_5')
      | ~ v5_pre_topc('#skF_7','#skF_4','#skF_6')
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_6'))
      | ~ v1_funct_1('#skF_7')
      | ~ r1_tsep_1('#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5',A_794)
      | ~ m1_pre_topc('#skF_4',A_794)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_794)
      | ~ v2_pre_topc(A_794)
      | v2_struct_0(A_794) ) ),
    inference(resolution,[status(thm)],[c_1471,c_2450])).

tff(c_2476,plain,(
    ! [A_794] :
      ( v5_pre_topc(k10_tmap_1(A_794,'#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),k1_tsep_1(A_794,'#skF_4','#skF_5'),'#skF_6')
      | ~ r4_tsep_1(A_794,'#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5',A_794)
      | ~ m1_pre_topc('#skF_4',A_794)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_794)
      | ~ v2_pre_topc(A_794)
      | v2_struct_0(A_794) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_1424,c_1465,c_1446,c_2460])).

tff(c_2484,plain,(
    ! [A_797] :
      ( v5_pre_topc(k10_tmap_1(A_797,'#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),k1_tsep_1(A_797,'#skF_4','#skF_5'),'#skF_6')
      | ~ r4_tsep_1(A_797,'#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5',A_797)
      | ~ m1_pre_topc('#skF_4',A_797)
      | ~ l1_pre_topc(A_797)
      | ~ v2_pre_topc(A_797)
      | v2_struct_0(A_797) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2476])).

tff(c_2055,plain,(
    ! [A_730,B_725,C_727,E_729,D_728,F_726] :
      ( v1_funct_2(k10_tmap_1(A_730,B_725,C_727,D_728,E_729,F_726),u1_struct_0(k1_tsep_1(A_730,C_727,D_728)),u1_struct_0(B_725))
      | ~ m1_subset_1(F_726,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_728),u1_struct_0(B_725))))
      | ~ v1_funct_2(F_726,u1_struct_0(D_728),u1_struct_0(B_725))
      | ~ v1_funct_1(F_726)
      | ~ m1_subset_1(E_729,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_727),u1_struct_0(B_725))))
      | ~ v1_funct_2(E_729,u1_struct_0(C_727),u1_struct_0(B_725))
      | ~ v1_funct_1(E_729)
      | ~ m1_pre_topc(D_728,A_730)
      | v2_struct_0(D_728)
      | ~ m1_pre_topc(C_727,A_730)
      | v2_struct_0(C_727)
      | ~ l1_pre_topc(B_725)
      | ~ v2_pre_topc(B_725)
      | v2_struct_0(B_725)
      | ~ l1_pre_topc(A_730)
      | ~ v2_pre_topc(A_730)
      | v2_struct_0(A_730) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1880,plain,(
    ! [C_702,A_705,B_700,D_703,E_704,F_701] :
      ( m1_subset_1(k10_tmap_1(A_705,B_700,C_702,D_703,E_704,F_701),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_705,C_702,D_703)),u1_struct_0(B_700))))
      | ~ m1_subset_1(F_701,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_703),u1_struct_0(B_700))))
      | ~ v1_funct_2(F_701,u1_struct_0(D_703),u1_struct_0(B_700))
      | ~ v1_funct_1(F_701)
      | ~ m1_subset_1(E_704,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_702),u1_struct_0(B_700))))
      | ~ v1_funct_2(E_704,u1_struct_0(C_702),u1_struct_0(B_700))
      | ~ v1_funct_1(E_704)
      | ~ m1_pre_topc(D_703,A_705)
      | v2_struct_0(D_703)
      | ~ m1_pre_topc(C_702,A_705)
      | v2_struct_0(C_702)
      | ~ l1_pre_topc(B_700)
      | ~ v2_pre_topc(B_700)
      | v2_struct_0(B_700)
      | ~ l1_pre_topc(A_705)
      | ~ v2_pre_topc(A_705)
      | v2_struct_0(A_705) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1674,plain,(
    ! [B_656,C_658,D_659,A_661,F_657,E_660] :
      ( v1_funct_1(k10_tmap_1(A_661,B_656,C_658,D_659,E_660,F_657))
      | ~ m1_subset_1(F_657,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_659),u1_struct_0(B_656))))
      | ~ v1_funct_2(F_657,u1_struct_0(D_659),u1_struct_0(B_656))
      | ~ v1_funct_1(F_657)
      | ~ m1_subset_1(E_660,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_658),u1_struct_0(B_656))))
      | ~ v1_funct_2(E_660,u1_struct_0(C_658),u1_struct_0(B_656))
      | ~ v1_funct_1(E_660)
      | ~ m1_pre_topc(D_659,A_661)
      | v2_struct_0(D_659)
      | ~ m1_pre_topc(C_658,A_661)
      | v2_struct_0(C_658)
      | ~ l1_pre_topc(B_656)
      | ~ v2_pre_topc(B_656)
      | v2_struct_0(B_656)
      | ~ l1_pre_topc(A_661)
      | ~ v2_pre_topc(A_661)
      | v2_struct_0(A_661) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1684,plain,(
    ! [A_661,C_658,E_660] :
      ( v1_funct_1(k10_tmap_1(A_661,'#skF_6',C_658,'#skF_5',E_660,'#skF_8'))
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_660,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_658),u1_struct_0('#skF_6'))))
      | ~ v1_funct_2(E_660,u1_struct_0(C_658),u1_struct_0('#skF_6'))
      | ~ v1_funct_1(E_660)
      | ~ m1_pre_topc('#skF_5',A_661)
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(C_658,A_661)
      | v2_struct_0(C_658)
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc(A_661)
      | ~ v2_pre_topc(A_661)
      | v2_struct_0(A_661) ) ),
    inference(resolution,[status(thm)],[c_1469,c_1674])).

tff(c_1694,plain,(
    ! [A_661,C_658,E_660] :
      ( v1_funct_1(k10_tmap_1(A_661,'#skF_6',C_658,'#skF_5',E_660,'#skF_8'))
      | ~ m1_subset_1(E_660,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_658),u1_struct_0('#skF_6'))))
      | ~ v1_funct_2(E_660,u1_struct_0(C_658),u1_struct_0('#skF_6'))
      | ~ v1_funct_1(E_660)
      | ~ m1_pre_topc('#skF_5',A_661)
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(C_658,A_661)
      | v2_struct_0(C_658)
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc(A_661)
      | ~ v2_pre_topc(A_661)
      | v2_struct_0(A_661) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1430,c_1426,c_1428,c_1467,c_1684])).

tff(c_1713,plain,(
    ! [A_667,C_668,E_669] :
      ( v1_funct_1(k10_tmap_1(A_667,'#skF_6',C_668,'#skF_5',E_669,'#skF_8'))
      | ~ m1_subset_1(E_669,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_668),u1_struct_0('#skF_6'))))
      | ~ v1_funct_2(E_669,u1_struct_0(C_668),u1_struct_0('#skF_6'))
      | ~ v1_funct_1(E_669)
      | ~ m1_pre_topc('#skF_5',A_667)
      | ~ m1_pre_topc(C_668,A_667)
      | v2_struct_0(C_668)
      | ~ l1_pre_topc(A_667)
      | ~ v2_pre_topc(A_667)
      | v2_struct_0(A_667) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1409,c_80,c_1694])).

tff(c_1715,plain,(
    ! [A_667] :
      ( v1_funct_1(k10_tmap_1(A_667,'#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'))
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_6'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_pre_topc('#skF_5',A_667)
      | ~ m1_pre_topc('#skF_4',A_667)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_667)
      | ~ v2_pre_topc(A_667)
      | v2_struct_0(A_667) ) ),
    inference(resolution,[status(thm)],[c_1471,c_1713])).

tff(c_1720,plain,(
    ! [A_667] :
      ( v1_funct_1(k10_tmap_1(A_667,'#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'))
      | ~ m1_pre_topc('#skF_5',A_667)
      | ~ m1_pre_topc('#skF_4',A_667)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_667)
      | ~ v2_pre_topc(A_667)
      | v2_struct_0(A_667) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1424,c_1465,c_1715])).

tff(c_1728,plain,(
    ! [A_671] :
      ( v1_funct_1(k10_tmap_1(A_671,'#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'))
      | ~ m1_pre_topc('#skF_5',A_671)
      | ~ m1_pre_topc('#skF_4',A_671)
      | ~ l1_pre_topc(A_671)
      | ~ v2_pre_topc(A_671)
      | v2_struct_0(A_671) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_1720])).

tff(c_94,plain,
    ( ~ m1_subset_1(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_6'))))
    | ~ v5_pre_topc(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_6')
    | ~ v1_funct_2(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_6'))
    | ~ v1_funct_1(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'))
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_366])).

tff(c_1668,plain,
    ( ~ m1_subset_1(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_6'))))
    | ~ v5_pre_topc(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_6')
    | ~ v1_funct_2(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_6'))
    | ~ v1_funct_1(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1407,c_248,c_94])).

tff(c_1669,plain,(
    ~ v1_funct_1(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_1668])).

tff(c_1731,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1728,c_1669])).

tff(c_1734,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_78,c_1731])).

tff(c_1736,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_1734])).

tff(c_1737,plain,
    ( ~ v1_funct_2(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_6'))
    | ~ v5_pre_topc(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_6')
    | ~ m1_subset_1(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_6')))) ),
    inference(splitRight,[status(thm)],[c_1668])).

tff(c_1739,plain,(
    ~ m1_subset_1(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_6')))) ),
    inference(splitLeft,[status(thm)],[c_1737])).

tff(c_1891,plain,
    ( ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))))
    | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))
    | ~ v1_funct_1('#skF_8')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_6'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_6'))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1880,c_1739])).

tff(c_1908,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_1430,c_1426,c_82,c_78,c_1424,c_1465,c_1471,c_1428,c_1467,c_1469,c_1891])).

tff(c_1910,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_1409,c_84,c_80,c_1908])).

tff(c_1911,plain,
    ( ~ v5_pre_topc(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_6')
    | ~ v1_funct_2(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1737])).

tff(c_1918,plain,(
    ~ v1_funct_2(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1911])).

tff(c_2058,plain,
    ( ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))))
    | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))
    | ~ v1_funct_1('#skF_8')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_6'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_6'))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2055,c_1918])).

tff(c_2064,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_1430,c_1426,c_82,c_78,c_1424,c_1465,c_1471,c_1428,c_1467,c_1469,c_2058])).

tff(c_2066,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_1409,c_84,c_80,c_2064])).

tff(c_2067,plain,(
    ~ v5_pre_topc(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1911])).

tff(c_2487,plain,
    ( ~ r4_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2484,c_2067])).

tff(c_2490,plain,
    ( ~ r4_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_78,c_2487])).

tff(c_2491,plain,(
    ~ r4_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_2490])).

tff(c_2494,plain,
    ( ~ r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_2491])).

tff(c_2497,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_78,c_1407,c_2494])).

tff(c_2499,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_80,c_2497])).

tff(c_2501,plain,(
    ~ r1_tsep_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_2500,plain,(
    r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_2594,plain,(
    ! [B_813,C_814,A_815] :
      ( r1_tsep_1(B_813,C_814)
      | ~ r3_tsep_1(A_815,B_813,C_814)
      | ~ m1_pre_topc(C_814,A_815)
      | v2_struct_0(C_814)
      | ~ m1_pre_topc(B_813,A_815)
      | v2_struct_0(B_813)
      | ~ l1_pre_topc(A_815)
      | ~ v2_pre_topc(A_815)
      | v2_struct_0(A_815) ) ),
    inference(cnfTransformation,[status(thm)],[f_308])).

tff(c_2600,plain,
    ( r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2500,c_2594])).

tff(c_2607,plain,
    ( r1_tsep_1('#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_78,c_2600])).

tff(c_2609,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_80,c_2501,c_2607])).

%------------------------------------------------------------------------------
