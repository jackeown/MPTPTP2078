%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:11 EST 2020

% Result     : Theorem 11.56s
% Output     : CNFRefutation 11.89s
% Verified   : 
% Statistics : Number of formulae       :  247 (32397 expanded)
%              Number of leaves         :   37 (11334 expanded)
%              Depth                    :   33
%              Number of atoms          : 1571 (422334 expanded)
%              Number of equality atoms :   12 (3431 expanded)
%              Maximal formula depth    :   39 (   8 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v5_pre_topc > v1_funct_2 > r4_tsep_1 > r3_tsep_1 > r1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k2_tsep_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_8 > #skF_4

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

tff(k2_tsep_1,type,(
    k2_tsep_1: ( $i * $i * $i ) > $i )).

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

tff(f_343,negated_conjecture,(
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

tff(f_203,axiom,(
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

tff(f_41,axiom,(
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

tff(f_99,axiom,(
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
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,u1_struct_0(D),u1_struct_0(B))
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                         => ( ( r1_tsep_1(C,D)
                              | r2_funct_2(u1_struct_0(k2_tsep_1(A,C,D)),u1_struct_0(B),k3_tmap_1(A,B,C,k2_tsep_1(A,C,D),E),k3_tmap_1(A,B,D,k2_tsep_1(A,C,D),F)) )
                           => ! [G] :
                                ( ( v1_funct_1(G)
                                  & v1_funct_2(G,u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
                                  & m1_subset_1(G,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) )
                               => ( G = k10_tmap_1(A,B,C,D,E,F)
                                <=> ( r2_funct_2(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,k1_tsep_1(A,C,D),C,G),E)
                                    & r2_funct_2(u1_struct_0(D),u1_struct_0(B),k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,G),F) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_tmap_1)).

tff(f_141,axiom,(
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

tff(f_285,axiom,(
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

tff(f_260,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_343])).

tff(c_84,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_343])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_343])).

tff(c_88,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_343])).

tff(c_86,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_343])).

tff(c_82,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_343])).

tff(c_78,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_343])).

tff(c_222,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | r1_tsep_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_343])).

tff(c_247,plain,(
    r1_tsep_1('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_222])).

tff(c_112,plain,
    ( l1_pre_topc('#skF_6')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_343])).

tff(c_249,plain,
    ( l1_pre_topc('#skF_6')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_112])).

tff(c_250,plain,(
    ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_249])).

tff(c_46,plain,(
    ! [A_138,B_166,C_180] :
      ( v1_funct_1('#skF_2'(A_138,B_166,C_180))
      | r3_tsep_1(A_138,B_166,C_180)
      | ~ r1_tsep_1(B_166,C_180)
      | ~ m1_pre_topc(C_180,A_138)
      | v2_struct_0(C_180)
      | ~ m1_pre_topc(B_166,A_138)
      | v2_struct_0(B_166)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_48,plain,(
    ! [A_138,B_166,C_180] :
      ( l1_pre_topc('#skF_1'(A_138,B_166,C_180))
      | r3_tsep_1(A_138,B_166,C_180)
      | ~ r1_tsep_1(B_166,C_180)
      | ~ m1_pre_topc(C_180,A_138)
      | v2_struct_0(C_180)
      | ~ m1_pre_topc(B_166,A_138)
      | v2_struct_0(B_166)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_50,plain,(
    ! [A_138,B_166,C_180] :
      ( v2_pre_topc('#skF_1'(A_138,B_166,C_180))
      | r3_tsep_1(A_138,B_166,C_180)
      | ~ r1_tsep_1(B_166,C_180)
      | ~ m1_pre_topc(C_180,A_138)
      | v2_struct_0(C_180)
      | ~ m1_pre_topc(B_166,A_138)
      | v2_struct_0(B_166)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_40,plain,(
    ! [A_138,B_166,C_180] :
      ( v1_funct_1(k3_tmap_1(A_138,'#skF_1'(A_138,B_166,C_180),k1_tsep_1(A_138,B_166,C_180),B_166,'#skF_2'(A_138,B_166,C_180)))
      | r3_tsep_1(A_138,B_166,C_180)
      | ~ r1_tsep_1(B_166,C_180)
      | ~ m1_pre_topc(C_180,A_138)
      | v2_struct_0(C_180)
      | ~ m1_pre_topc(B_166,A_138)
      | v2_struct_0(B_166)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_34,plain,(
    ! [A_138,B_166,C_180] :
      ( m1_subset_1(k3_tmap_1(A_138,'#skF_1'(A_138,B_166,C_180),k1_tsep_1(A_138,B_166,C_180),B_166,'#skF_2'(A_138,B_166,C_180)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_166),u1_struct_0('#skF_1'(A_138,B_166,C_180)))))
      | r3_tsep_1(A_138,B_166,C_180)
      | ~ r1_tsep_1(B_166,C_180)
      | ~ m1_pre_topc(C_180,A_138)
      | v2_struct_0(C_180)
      | ~ m1_pre_topc(B_166,A_138)
      | v2_struct_0(B_166)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_26,plain,(
    ! [A_138,B_166,C_180] :
      ( m1_subset_1(k3_tmap_1(A_138,'#skF_1'(A_138,B_166,C_180),k1_tsep_1(A_138,B_166,C_180),C_180,'#skF_2'(A_138,B_166,C_180)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_180),u1_struct_0('#skF_1'(A_138,B_166,C_180)))))
      | r3_tsep_1(A_138,B_166,C_180)
      | ~ r1_tsep_1(B_166,C_180)
      | ~ m1_pre_topc(C_180,A_138)
      | v2_struct_0(C_180)
      | ~ m1_pre_topc(B_166,A_138)
      | v2_struct_0(B_166)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_299,plain,(
    ! [A_429,B_430,C_431] :
      ( m1_subset_1(k3_tmap_1(A_429,'#skF_1'(A_429,B_430,C_431),k1_tsep_1(A_429,B_430,C_431),B_430,'#skF_2'(A_429,B_430,C_431)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_430),u1_struct_0('#skF_1'(A_429,B_430,C_431)))))
      | r3_tsep_1(A_429,B_430,C_431)
      | ~ r1_tsep_1(B_430,C_431)
      | ~ m1_pre_topc(C_431,A_429)
      | v2_struct_0(C_431)
      | ~ m1_pre_topc(B_430,A_429)
      | v2_struct_0(B_430)
      | ~ l1_pre_topc(A_429)
      | ~ v2_pre_topc(A_429)
      | v2_struct_0(A_429) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_2,plain,(
    ! [A_1,B_2,D_4] :
      ( r2_funct_2(A_1,B_2,D_4,D_4)
      | ~ m1_subset_1(D_4,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(D_4,A_1,B_2)
      | ~ v1_funct_1(D_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_308,plain,(
    ! [B_430,A_429,C_431] :
      ( r2_funct_2(u1_struct_0(B_430),u1_struct_0('#skF_1'(A_429,B_430,C_431)),k3_tmap_1(A_429,'#skF_1'(A_429,B_430,C_431),k1_tsep_1(A_429,B_430,C_431),B_430,'#skF_2'(A_429,B_430,C_431)),k3_tmap_1(A_429,'#skF_1'(A_429,B_430,C_431),k1_tsep_1(A_429,B_430,C_431),B_430,'#skF_2'(A_429,B_430,C_431)))
      | ~ v1_funct_2(k3_tmap_1(A_429,'#skF_1'(A_429,B_430,C_431),k1_tsep_1(A_429,B_430,C_431),B_430,'#skF_2'(A_429,B_430,C_431)),u1_struct_0(B_430),u1_struct_0('#skF_1'(A_429,B_430,C_431)))
      | ~ v1_funct_1(k3_tmap_1(A_429,'#skF_1'(A_429,B_430,C_431),k1_tsep_1(A_429,B_430,C_431),B_430,'#skF_2'(A_429,B_430,C_431)))
      | r3_tsep_1(A_429,B_430,C_431)
      | ~ r1_tsep_1(B_430,C_431)
      | ~ m1_pre_topc(C_431,A_429)
      | v2_struct_0(C_431)
      | ~ m1_pre_topc(B_430,A_429)
      | v2_struct_0(B_430)
      | ~ l1_pre_topc(A_429)
      | ~ v2_pre_topc(A_429)
      | v2_struct_0(A_429) ) ),
    inference(resolution,[status(thm)],[c_299,c_2])).

tff(c_309,plain,(
    ! [A_432,B_433,C_434] :
      ( m1_subset_1(k3_tmap_1(A_432,'#skF_1'(A_432,B_433,C_434),k1_tsep_1(A_432,B_433,C_434),C_434,'#skF_2'(A_432,B_433,C_434)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_434),u1_struct_0('#skF_1'(A_432,B_433,C_434)))))
      | r3_tsep_1(A_432,B_433,C_434)
      | ~ r1_tsep_1(B_433,C_434)
      | ~ m1_pre_topc(C_434,A_432)
      | v2_struct_0(C_434)
      | ~ m1_pre_topc(B_433,A_432)
      | v2_struct_0(B_433)
      | ~ l1_pre_topc(A_432)
      | ~ v2_pre_topc(A_432)
      | v2_struct_0(A_432) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_318,plain,(
    ! [C_434,A_432,B_433] :
      ( r2_funct_2(u1_struct_0(C_434),u1_struct_0('#skF_1'(A_432,B_433,C_434)),k3_tmap_1(A_432,'#skF_1'(A_432,B_433,C_434),k1_tsep_1(A_432,B_433,C_434),C_434,'#skF_2'(A_432,B_433,C_434)),k3_tmap_1(A_432,'#skF_1'(A_432,B_433,C_434),k1_tsep_1(A_432,B_433,C_434),C_434,'#skF_2'(A_432,B_433,C_434)))
      | ~ v1_funct_2(k3_tmap_1(A_432,'#skF_1'(A_432,B_433,C_434),k1_tsep_1(A_432,B_433,C_434),C_434,'#skF_2'(A_432,B_433,C_434)),u1_struct_0(C_434),u1_struct_0('#skF_1'(A_432,B_433,C_434)))
      | ~ v1_funct_1(k3_tmap_1(A_432,'#skF_1'(A_432,B_433,C_434),k1_tsep_1(A_432,B_433,C_434),C_434,'#skF_2'(A_432,B_433,C_434)))
      | r3_tsep_1(A_432,B_433,C_434)
      | ~ r1_tsep_1(B_433,C_434)
      | ~ m1_pre_topc(C_434,A_432)
      | v2_struct_0(C_434)
      | ~ m1_pre_topc(B_433,A_432)
      | v2_struct_0(B_433)
      | ~ l1_pre_topc(A_432)
      | ~ v2_pre_topc(A_432)
      | v2_struct_0(A_432) ) ),
    inference(resolution,[status(thm)],[c_309,c_2])).

tff(c_505,plain,(
    ! [D_500,C_498,G_495,F_501,B_496,A_499,E_497] :
      ( ~ r1_tsep_1(C_498,D_500)
      | k10_tmap_1(A_499,B_496,C_498,D_500,E_497,F_501) = G_495
      | ~ r2_funct_2(u1_struct_0(D_500),u1_struct_0(B_496),k3_tmap_1(A_499,B_496,k1_tsep_1(A_499,C_498,D_500),D_500,G_495),F_501)
      | ~ r2_funct_2(u1_struct_0(C_498),u1_struct_0(B_496),k3_tmap_1(A_499,B_496,k1_tsep_1(A_499,C_498,D_500),C_498,G_495),E_497)
      | ~ m1_subset_1(G_495,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_499,C_498,D_500)),u1_struct_0(B_496))))
      | ~ v1_funct_2(G_495,u1_struct_0(k1_tsep_1(A_499,C_498,D_500)),u1_struct_0(B_496))
      | ~ v1_funct_1(G_495)
      | ~ m1_subset_1(F_501,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_500),u1_struct_0(B_496))))
      | ~ v1_funct_2(F_501,u1_struct_0(D_500),u1_struct_0(B_496))
      | ~ v1_funct_1(F_501)
      | ~ m1_subset_1(E_497,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_498),u1_struct_0(B_496))))
      | ~ v1_funct_2(E_497,u1_struct_0(C_498),u1_struct_0(B_496))
      | ~ v1_funct_1(E_497)
      | ~ m1_pre_topc(D_500,A_499)
      | v2_struct_0(D_500)
      | ~ m1_pre_topc(C_498,A_499)
      | v2_struct_0(C_498)
      | ~ l1_pre_topc(B_496)
      | ~ v2_pre_topc(B_496)
      | v2_struct_0(B_496)
      | ~ l1_pre_topc(A_499)
      | ~ v2_pre_topc(A_499)
      | v2_struct_0(A_499) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1093,plain,(
    ! [A_836,B_837,C_838,E_839] :
      ( k10_tmap_1(A_836,'#skF_1'(A_836,B_837,C_838),B_837,C_838,E_839,k3_tmap_1(A_836,'#skF_1'(A_836,B_837,C_838),k1_tsep_1(A_836,B_837,C_838),C_838,'#skF_2'(A_836,B_837,C_838))) = '#skF_2'(A_836,B_837,C_838)
      | ~ r2_funct_2(u1_struct_0(B_837),u1_struct_0('#skF_1'(A_836,B_837,C_838)),k3_tmap_1(A_836,'#skF_1'(A_836,B_837,C_838),k1_tsep_1(A_836,B_837,C_838),B_837,'#skF_2'(A_836,B_837,C_838)),E_839)
      | ~ m1_subset_1('#skF_2'(A_836,B_837,C_838),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_836,B_837,C_838)),u1_struct_0('#skF_1'(A_836,B_837,C_838)))))
      | ~ v1_funct_2('#skF_2'(A_836,B_837,C_838),u1_struct_0(k1_tsep_1(A_836,B_837,C_838)),u1_struct_0('#skF_1'(A_836,B_837,C_838)))
      | ~ v1_funct_1('#skF_2'(A_836,B_837,C_838))
      | ~ m1_subset_1(k3_tmap_1(A_836,'#skF_1'(A_836,B_837,C_838),k1_tsep_1(A_836,B_837,C_838),C_838,'#skF_2'(A_836,B_837,C_838)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_838),u1_struct_0('#skF_1'(A_836,B_837,C_838)))))
      | ~ m1_subset_1(E_839,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_837),u1_struct_0('#skF_1'(A_836,B_837,C_838)))))
      | ~ v1_funct_2(E_839,u1_struct_0(B_837),u1_struct_0('#skF_1'(A_836,B_837,C_838)))
      | ~ v1_funct_1(E_839)
      | ~ l1_pre_topc('#skF_1'(A_836,B_837,C_838))
      | ~ v2_pre_topc('#skF_1'(A_836,B_837,C_838))
      | v2_struct_0('#skF_1'(A_836,B_837,C_838))
      | ~ v1_funct_2(k3_tmap_1(A_836,'#skF_1'(A_836,B_837,C_838),k1_tsep_1(A_836,B_837,C_838),C_838,'#skF_2'(A_836,B_837,C_838)),u1_struct_0(C_838),u1_struct_0('#skF_1'(A_836,B_837,C_838)))
      | ~ v1_funct_1(k3_tmap_1(A_836,'#skF_1'(A_836,B_837,C_838),k1_tsep_1(A_836,B_837,C_838),C_838,'#skF_2'(A_836,B_837,C_838)))
      | r3_tsep_1(A_836,B_837,C_838)
      | ~ r1_tsep_1(B_837,C_838)
      | ~ m1_pre_topc(C_838,A_836)
      | v2_struct_0(C_838)
      | ~ m1_pre_topc(B_837,A_836)
      | v2_struct_0(B_837)
      | ~ l1_pre_topc(A_836)
      | ~ v2_pre_topc(A_836)
      | v2_struct_0(A_836) ) ),
    inference(resolution,[status(thm)],[c_318,c_505])).

tff(c_1513,plain,(
    ! [A_970,B_971,C_972] :
      ( k10_tmap_1(A_970,'#skF_1'(A_970,B_971,C_972),B_971,C_972,k3_tmap_1(A_970,'#skF_1'(A_970,B_971,C_972),k1_tsep_1(A_970,B_971,C_972),B_971,'#skF_2'(A_970,B_971,C_972)),k3_tmap_1(A_970,'#skF_1'(A_970,B_971,C_972),k1_tsep_1(A_970,B_971,C_972),C_972,'#skF_2'(A_970,B_971,C_972))) = '#skF_2'(A_970,B_971,C_972)
      | ~ m1_subset_1('#skF_2'(A_970,B_971,C_972),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_970,B_971,C_972)),u1_struct_0('#skF_1'(A_970,B_971,C_972)))))
      | ~ v1_funct_2('#skF_2'(A_970,B_971,C_972),u1_struct_0(k1_tsep_1(A_970,B_971,C_972)),u1_struct_0('#skF_1'(A_970,B_971,C_972)))
      | ~ v1_funct_1('#skF_2'(A_970,B_971,C_972))
      | ~ m1_subset_1(k3_tmap_1(A_970,'#skF_1'(A_970,B_971,C_972),k1_tsep_1(A_970,B_971,C_972),C_972,'#skF_2'(A_970,B_971,C_972)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_972),u1_struct_0('#skF_1'(A_970,B_971,C_972)))))
      | ~ m1_subset_1(k3_tmap_1(A_970,'#skF_1'(A_970,B_971,C_972),k1_tsep_1(A_970,B_971,C_972),B_971,'#skF_2'(A_970,B_971,C_972)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_971),u1_struct_0('#skF_1'(A_970,B_971,C_972)))))
      | ~ l1_pre_topc('#skF_1'(A_970,B_971,C_972))
      | ~ v2_pre_topc('#skF_1'(A_970,B_971,C_972))
      | v2_struct_0('#skF_1'(A_970,B_971,C_972))
      | ~ v1_funct_2(k3_tmap_1(A_970,'#skF_1'(A_970,B_971,C_972),k1_tsep_1(A_970,B_971,C_972),C_972,'#skF_2'(A_970,B_971,C_972)),u1_struct_0(C_972),u1_struct_0('#skF_1'(A_970,B_971,C_972)))
      | ~ v1_funct_1(k3_tmap_1(A_970,'#skF_1'(A_970,B_971,C_972),k1_tsep_1(A_970,B_971,C_972),C_972,'#skF_2'(A_970,B_971,C_972)))
      | ~ v1_funct_2(k3_tmap_1(A_970,'#skF_1'(A_970,B_971,C_972),k1_tsep_1(A_970,B_971,C_972),B_971,'#skF_2'(A_970,B_971,C_972)),u1_struct_0(B_971),u1_struct_0('#skF_1'(A_970,B_971,C_972)))
      | ~ v1_funct_1(k3_tmap_1(A_970,'#skF_1'(A_970,B_971,C_972),k1_tsep_1(A_970,B_971,C_972),B_971,'#skF_2'(A_970,B_971,C_972)))
      | r3_tsep_1(A_970,B_971,C_972)
      | ~ r1_tsep_1(B_971,C_972)
      | ~ m1_pre_topc(C_972,A_970)
      | v2_struct_0(C_972)
      | ~ m1_pre_topc(B_971,A_970)
      | v2_struct_0(B_971)
      | ~ l1_pre_topc(A_970)
      | ~ v2_pre_topc(A_970)
      | v2_struct_0(A_970) ) ),
    inference(resolution,[status(thm)],[c_308,c_1093])).

tff(c_1521,plain,(
    ! [A_973,B_974,C_975] :
      ( k10_tmap_1(A_973,'#skF_1'(A_973,B_974,C_975),B_974,C_975,k3_tmap_1(A_973,'#skF_1'(A_973,B_974,C_975),k1_tsep_1(A_973,B_974,C_975),B_974,'#skF_2'(A_973,B_974,C_975)),k3_tmap_1(A_973,'#skF_1'(A_973,B_974,C_975),k1_tsep_1(A_973,B_974,C_975),C_975,'#skF_2'(A_973,B_974,C_975))) = '#skF_2'(A_973,B_974,C_975)
      | ~ m1_subset_1('#skF_2'(A_973,B_974,C_975),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_973,B_974,C_975)),u1_struct_0('#skF_1'(A_973,B_974,C_975)))))
      | ~ v1_funct_2('#skF_2'(A_973,B_974,C_975),u1_struct_0(k1_tsep_1(A_973,B_974,C_975)),u1_struct_0('#skF_1'(A_973,B_974,C_975)))
      | ~ v1_funct_1('#skF_2'(A_973,B_974,C_975))
      | ~ m1_subset_1(k3_tmap_1(A_973,'#skF_1'(A_973,B_974,C_975),k1_tsep_1(A_973,B_974,C_975),B_974,'#skF_2'(A_973,B_974,C_975)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_974),u1_struct_0('#skF_1'(A_973,B_974,C_975)))))
      | ~ l1_pre_topc('#skF_1'(A_973,B_974,C_975))
      | ~ v2_pre_topc('#skF_1'(A_973,B_974,C_975))
      | v2_struct_0('#skF_1'(A_973,B_974,C_975))
      | ~ v1_funct_2(k3_tmap_1(A_973,'#skF_1'(A_973,B_974,C_975),k1_tsep_1(A_973,B_974,C_975),C_975,'#skF_2'(A_973,B_974,C_975)),u1_struct_0(C_975),u1_struct_0('#skF_1'(A_973,B_974,C_975)))
      | ~ v1_funct_1(k3_tmap_1(A_973,'#skF_1'(A_973,B_974,C_975),k1_tsep_1(A_973,B_974,C_975),C_975,'#skF_2'(A_973,B_974,C_975)))
      | ~ v1_funct_2(k3_tmap_1(A_973,'#skF_1'(A_973,B_974,C_975),k1_tsep_1(A_973,B_974,C_975),B_974,'#skF_2'(A_973,B_974,C_975)),u1_struct_0(B_974),u1_struct_0('#skF_1'(A_973,B_974,C_975)))
      | ~ v1_funct_1(k3_tmap_1(A_973,'#skF_1'(A_973,B_974,C_975),k1_tsep_1(A_973,B_974,C_975),B_974,'#skF_2'(A_973,B_974,C_975)))
      | r3_tsep_1(A_973,B_974,C_975)
      | ~ r1_tsep_1(B_974,C_975)
      | ~ m1_pre_topc(C_975,A_973)
      | v2_struct_0(C_975)
      | ~ m1_pre_topc(B_974,A_973)
      | v2_struct_0(B_974)
      | ~ l1_pre_topc(A_973)
      | ~ v2_pre_topc(A_973)
      | v2_struct_0(A_973) ) ),
    inference(resolution,[status(thm)],[c_26,c_1513])).

tff(c_1529,plain,(
    ! [A_976,B_977,C_978] :
      ( k10_tmap_1(A_976,'#skF_1'(A_976,B_977,C_978),B_977,C_978,k3_tmap_1(A_976,'#skF_1'(A_976,B_977,C_978),k1_tsep_1(A_976,B_977,C_978),B_977,'#skF_2'(A_976,B_977,C_978)),k3_tmap_1(A_976,'#skF_1'(A_976,B_977,C_978),k1_tsep_1(A_976,B_977,C_978),C_978,'#skF_2'(A_976,B_977,C_978))) = '#skF_2'(A_976,B_977,C_978)
      | ~ m1_subset_1('#skF_2'(A_976,B_977,C_978),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_976,B_977,C_978)),u1_struct_0('#skF_1'(A_976,B_977,C_978)))))
      | ~ v1_funct_2('#skF_2'(A_976,B_977,C_978),u1_struct_0(k1_tsep_1(A_976,B_977,C_978)),u1_struct_0('#skF_1'(A_976,B_977,C_978)))
      | ~ v1_funct_1('#skF_2'(A_976,B_977,C_978))
      | ~ l1_pre_topc('#skF_1'(A_976,B_977,C_978))
      | ~ v2_pre_topc('#skF_1'(A_976,B_977,C_978))
      | v2_struct_0('#skF_1'(A_976,B_977,C_978))
      | ~ v1_funct_2(k3_tmap_1(A_976,'#skF_1'(A_976,B_977,C_978),k1_tsep_1(A_976,B_977,C_978),C_978,'#skF_2'(A_976,B_977,C_978)),u1_struct_0(C_978),u1_struct_0('#skF_1'(A_976,B_977,C_978)))
      | ~ v1_funct_1(k3_tmap_1(A_976,'#skF_1'(A_976,B_977,C_978),k1_tsep_1(A_976,B_977,C_978),C_978,'#skF_2'(A_976,B_977,C_978)))
      | ~ v1_funct_2(k3_tmap_1(A_976,'#skF_1'(A_976,B_977,C_978),k1_tsep_1(A_976,B_977,C_978),B_977,'#skF_2'(A_976,B_977,C_978)),u1_struct_0(B_977),u1_struct_0('#skF_1'(A_976,B_977,C_978)))
      | ~ v1_funct_1(k3_tmap_1(A_976,'#skF_1'(A_976,B_977,C_978),k1_tsep_1(A_976,B_977,C_978),B_977,'#skF_2'(A_976,B_977,C_978)))
      | r3_tsep_1(A_976,B_977,C_978)
      | ~ r1_tsep_1(B_977,C_978)
      | ~ m1_pre_topc(C_978,A_976)
      | v2_struct_0(C_978)
      | ~ m1_pre_topc(B_977,A_976)
      | v2_struct_0(B_977)
      | ~ l1_pre_topc(A_976)
      | ~ v2_pre_topc(A_976)
      | v2_struct_0(A_976) ) ),
    inference(resolution,[status(thm)],[c_34,c_1521])).

tff(c_144,plain,(
    ! [D_367,E_371,F_373] :
      ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
      | v5_pre_topc(k10_tmap_1('#skF_3',D_367,'#skF_4','#skF_5',E_371,F_373),k1_tsep_1('#skF_3','#skF_4','#skF_5'),D_367)
      | ~ m1_subset_1(F_373,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(D_367))))
      | ~ v5_pre_topc(F_373,'#skF_5',D_367)
      | ~ v1_funct_2(F_373,u1_struct_0('#skF_5'),u1_struct_0(D_367))
      | ~ v1_funct_1(F_373)
      | ~ m1_subset_1(E_371,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(D_367))))
      | ~ v5_pre_topc(E_371,'#skF_4',D_367)
      | ~ v1_funct_2(E_371,u1_struct_0('#skF_4'),u1_struct_0(D_367))
      | ~ v1_funct_1(E_371)
      | ~ l1_pre_topc(D_367)
      | ~ v2_pre_topc(D_367)
      | v2_struct_0(D_367) ) ),
    inference(cnfTransformation,[status(thm)],[f_343])).

tff(c_353,plain,(
    ! [D_444,E_445,F_446] :
      ( v5_pre_topc(k10_tmap_1('#skF_3',D_444,'#skF_4','#skF_5',E_445,F_446),k1_tsep_1('#skF_3','#skF_4','#skF_5'),D_444)
      | ~ m1_subset_1(F_446,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(D_444))))
      | ~ v5_pre_topc(F_446,'#skF_5',D_444)
      | ~ v1_funct_2(F_446,u1_struct_0('#skF_5'),u1_struct_0(D_444))
      | ~ v1_funct_1(F_446)
      | ~ m1_subset_1(E_445,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(D_444))))
      | ~ v5_pre_topc(E_445,'#skF_4',D_444)
      | ~ v1_funct_2(E_445,u1_struct_0('#skF_4'),u1_struct_0(D_444))
      | ~ v1_funct_1(E_445)
      | ~ l1_pre_topc(D_444)
      | ~ v2_pre_topc(D_444)
      | v2_struct_0(D_444) ) ),
    inference(negUnitSimplification,[status(thm)],[c_250,c_144])).

tff(c_356,plain,(
    ! [A_138,B_166,E_445] :
      ( v5_pre_topc(k10_tmap_1('#skF_3','#skF_1'(A_138,B_166,'#skF_5'),'#skF_4','#skF_5',E_445,k3_tmap_1(A_138,'#skF_1'(A_138,B_166,'#skF_5'),k1_tsep_1(A_138,B_166,'#skF_5'),'#skF_5','#skF_2'(A_138,B_166,'#skF_5'))),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_1'(A_138,B_166,'#skF_5'))
      | ~ v5_pre_topc(k3_tmap_1(A_138,'#skF_1'(A_138,B_166,'#skF_5'),k1_tsep_1(A_138,B_166,'#skF_5'),'#skF_5','#skF_2'(A_138,B_166,'#skF_5')),'#skF_5','#skF_1'(A_138,B_166,'#skF_5'))
      | ~ v1_funct_2(k3_tmap_1(A_138,'#skF_1'(A_138,B_166,'#skF_5'),k1_tsep_1(A_138,B_166,'#skF_5'),'#skF_5','#skF_2'(A_138,B_166,'#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'(A_138,B_166,'#skF_5')))
      | ~ v1_funct_1(k3_tmap_1(A_138,'#skF_1'(A_138,B_166,'#skF_5'),k1_tsep_1(A_138,B_166,'#skF_5'),'#skF_5','#skF_2'(A_138,B_166,'#skF_5')))
      | ~ m1_subset_1(E_445,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'(A_138,B_166,'#skF_5')))))
      | ~ v5_pre_topc(E_445,'#skF_4','#skF_1'(A_138,B_166,'#skF_5'))
      | ~ v1_funct_2(E_445,u1_struct_0('#skF_4'),u1_struct_0('#skF_1'(A_138,B_166,'#skF_5')))
      | ~ v1_funct_1(E_445)
      | ~ l1_pre_topc('#skF_1'(A_138,B_166,'#skF_5'))
      | ~ v2_pre_topc('#skF_1'(A_138,B_166,'#skF_5'))
      | v2_struct_0('#skF_1'(A_138,B_166,'#skF_5'))
      | r3_tsep_1(A_138,B_166,'#skF_5')
      | ~ r1_tsep_1(B_166,'#skF_5')
      | ~ m1_pre_topc('#skF_5',A_138)
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(B_166,A_138)
      | v2_struct_0(B_166)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(resolution,[status(thm)],[c_26,c_353])).

tff(c_362,plain,(
    ! [A_138,B_166,E_445] :
      ( v5_pre_topc(k10_tmap_1('#skF_3','#skF_1'(A_138,B_166,'#skF_5'),'#skF_4','#skF_5',E_445,k3_tmap_1(A_138,'#skF_1'(A_138,B_166,'#skF_5'),k1_tsep_1(A_138,B_166,'#skF_5'),'#skF_5','#skF_2'(A_138,B_166,'#skF_5'))),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_1'(A_138,B_166,'#skF_5'))
      | ~ v5_pre_topc(k3_tmap_1(A_138,'#skF_1'(A_138,B_166,'#skF_5'),k1_tsep_1(A_138,B_166,'#skF_5'),'#skF_5','#skF_2'(A_138,B_166,'#skF_5')),'#skF_5','#skF_1'(A_138,B_166,'#skF_5'))
      | ~ v1_funct_2(k3_tmap_1(A_138,'#skF_1'(A_138,B_166,'#skF_5'),k1_tsep_1(A_138,B_166,'#skF_5'),'#skF_5','#skF_2'(A_138,B_166,'#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'(A_138,B_166,'#skF_5')))
      | ~ v1_funct_1(k3_tmap_1(A_138,'#skF_1'(A_138,B_166,'#skF_5'),k1_tsep_1(A_138,B_166,'#skF_5'),'#skF_5','#skF_2'(A_138,B_166,'#skF_5')))
      | ~ m1_subset_1(E_445,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'(A_138,B_166,'#skF_5')))))
      | ~ v5_pre_topc(E_445,'#skF_4','#skF_1'(A_138,B_166,'#skF_5'))
      | ~ v1_funct_2(E_445,u1_struct_0('#skF_4'),u1_struct_0('#skF_1'(A_138,B_166,'#skF_5')))
      | ~ v1_funct_1(E_445)
      | ~ l1_pre_topc('#skF_1'(A_138,B_166,'#skF_5'))
      | ~ v2_pre_topc('#skF_1'(A_138,B_166,'#skF_5'))
      | v2_struct_0('#skF_1'(A_138,B_166,'#skF_5'))
      | r3_tsep_1(A_138,B_166,'#skF_5')
      | ~ r1_tsep_1(B_166,'#skF_5')
      | ~ m1_pre_topc('#skF_5',A_138)
      | ~ m1_pre_topc(B_166,A_138)
      | v2_struct_0(B_166)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_356])).

tff(c_1583,plain,
    ( v5_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1529,c_362])).

tff(c_1669,plain,
    ( v5_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_78,c_247,c_88,c_86,c_82,c_78,c_247,c_1583])).

tff(c_1670,plain,
    ( v5_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_80,c_250,c_1669])).

tff(c_1700,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_1670])).

tff(c_1704,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_1700])).

tff(c_1707,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_78,c_247,c_1704])).

tff(c_1709,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_80,c_250,c_1707])).

tff(c_1711,plain,(
    v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_1670])).

tff(c_38,plain,(
    ! [A_138,B_166,C_180] :
      ( v1_funct_2(k3_tmap_1(A_138,'#skF_1'(A_138,B_166,C_180),k1_tsep_1(A_138,B_166,C_180),B_166,'#skF_2'(A_138,B_166,C_180)),u1_struct_0(B_166),u1_struct_0('#skF_1'(A_138,B_166,C_180)))
      | r3_tsep_1(A_138,B_166,C_180)
      | ~ r1_tsep_1(B_166,C_180)
      | ~ m1_pre_topc(C_180,A_138)
      | v2_struct_0(C_180)
      | ~ m1_pre_topc(B_166,A_138)
      | v2_struct_0(B_166)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_28,plain,(
    ! [A_138,B_166,C_180] :
      ( v5_pre_topc(k3_tmap_1(A_138,'#skF_1'(A_138,B_166,C_180),k1_tsep_1(A_138,B_166,C_180),C_180,'#skF_2'(A_138,B_166,C_180)),C_180,'#skF_1'(A_138,B_166,C_180))
      | r3_tsep_1(A_138,B_166,C_180)
      | ~ r1_tsep_1(B_166,C_180)
      | ~ m1_pre_topc(C_180,A_138)
      | v2_struct_0(C_180)
      | ~ m1_pre_topc(B_166,A_138)
      | v2_struct_0(B_166)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_1710,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v5_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1670])).

tff(c_1712,plain,(
    ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1710])).

tff(c_1715,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_1712])).

tff(c_1718,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_78,c_247,c_1715])).

tff(c_1720,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_80,c_250,c_1718])).

tff(c_1721,plain,
    ( ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | v5_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1710])).

tff(c_1734,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_1721])).

tff(c_1737,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_1734])).

tff(c_1740,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_78,c_247,c_1737])).

tff(c_1742,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_80,c_250,c_1740])).

tff(c_1744,plain,(
    v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_1721])).

tff(c_32,plain,(
    ! [A_138,B_166,C_180] :
      ( v1_funct_1(k3_tmap_1(A_138,'#skF_1'(A_138,B_166,C_180),k1_tsep_1(A_138,B_166,C_180),C_180,'#skF_2'(A_138,B_166,C_180)))
      | r3_tsep_1(A_138,B_166,C_180)
      | ~ r1_tsep_1(B_166,C_180)
      | ~ m1_pre_topc(C_180,A_138)
      | v2_struct_0(C_180)
      | ~ m1_pre_topc(B_166,A_138)
      | v2_struct_0(B_166)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_1722,plain,(
    v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1710])).

tff(c_118,plain,(
    ! [D_367,E_371,F_373] :
      ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
      | m1_subset_1(k10_tmap_1('#skF_3',D_367,'#skF_4','#skF_5',E_371,F_373),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0(D_367))))
      | ~ m1_subset_1(F_373,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(D_367))))
      | ~ v5_pre_topc(F_373,'#skF_5',D_367)
      | ~ v1_funct_2(F_373,u1_struct_0('#skF_5'),u1_struct_0(D_367))
      | ~ v1_funct_1(F_373)
      | ~ m1_subset_1(E_371,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(D_367))))
      | ~ v5_pre_topc(E_371,'#skF_4',D_367)
      | ~ v1_funct_2(E_371,u1_struct_0('#skF_4'),u1_struct_0(D_367))
      | ~ v1_funct_1(E_371)
      | ~ l1_pre_topc(D_367)
      | ~ v2_pre_topc(D_367)
      | v2_struct_0(D_367) ) ),
    inference(cnfTransformation,[status(thm)],[f_343])).

tff(c_397,plain,(
    ! [D_450,E_451,F_452] :
      ( m1_subset_1(k10_tmap_1('#skF_3',D_450,'#skF_4','#skF_5',E_451,F_452),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0(D_450))))
      | ~ m1_subset_1(F_452,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(D_450))))
      | ~ v5_pre_topc(F_452,'#skF_5',D_450)
      | ~ v1_funct_2(F_452,u1_struct_0('#skF_5'),u1_struct_0(D_450))
      | ~ v1_funct_1(F_452)
      | ~ m1_subset_1(E_451,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(D_450))))
      | ~ v5_pre_topc(E_451,'#skF_4',D_450)
      | ~ v1_funct_2(E_451,u1_struct_0('#skF_4'),u1_struct_0(D_450))
      | ~ v1_funct_1(E_451)
      | ~ l1_pre_topc(D_450)
      | ~ v2_pre_topc(D_450)
      | v2_struct_0(D_450) ) ),
    inference(negUnitSimplification,[status(thm)],[c_250,c_118])).

tff(c_403,plain,(
    ! [D_450,E_451,F_452] :
      ( r2_funct_2(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0(D_450),k10_tmap_1('#skF_3',D_450,'#skF_4','#skF_5',E_451,F_452),k10_tmap_1('#skF_3',D_450,'#skF_4','#skF_5',E_451,F_452))
      | ~ v1_funct_2(k10_tmap_1('#skF_3',D_450,'#skF_4','#skF_5',E_451,F_452),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0(D_450))
      | ~ v1_funct_1(k10_tmap_1('#skF_3',D_450,'#skF_4','#skF_5',E_451,F_452))
      | ~ m1_subset_1(F_452,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(D_450))))
      | ~ v5_pre_topc(F_452,'#skF_5',D_450)
      | ~ v1_funct_2(F_452,u1_struct_0('#skF_5'),u1_struct_0(D_450))
      | ~ v1_funct_1(F_452)
      | ~ m1_subset_1(E_451,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(D_450))))
      | ~ v5_pre_topc(E_451,'#skF_4',D_450)
      | ~ v1_funct_2(E_451,u1_struct_0('#skF_4'),u1_struct_0(D_450))
      | ~ v1_funct_1(E_451)
      | ~ l1_pre_topc(D_450)
      | ~ v2_pre_topc(D_450)
      | v2_struct_0(D_450) ) ),
    inference(resolution,[status(thm)],[c_397,c_2])).

tff(c_1642,plain,
    ( r2_funct_2(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')),k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_5',k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))),'#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2(k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_5',k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_5',k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1529,c_403])).

tff(c_1690,plain,
    ( r2_funct_2(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')),k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_5',k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))),'#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2(k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_5',k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_5',k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_78,c_247,c_1642])).

tff(c_1691,plain,
    ( r2_funct_2(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')),k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_5',k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))),'#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2(k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_5',k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_5',k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_80,c_250,c_1690])).

tff(c_1746,plain,
    ( r2_funct_2(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')),k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_5',k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))),'#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2(k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_5',k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_5',k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1711,c_1744,c_1722,c_1691])).

tff(c_1747,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_1746])).

tff(c_1750,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_1747])).

tff(c_1753,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_78,c_247,c_1750])).

tff(c_1755,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_80,c_250,c_1753])).

tff(c_1757,plain,(
    v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_1746])).

tff(c_1743,plain,
    ( ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v5_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1721])).

tff(c_1759,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v5_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1757,c_1743])).

tff(c_1760,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))))) ),
    inference(splitLeft,[status(thm)],[c_1759])).

tff(c_1763,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_1760])).

tff(c_1766,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_78,c_247,c_1763])).

tff(c_1768,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_80,c_250,c_1766])).

tff(c_1770,plain,(
    m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))))) ),
    inference(splitRight,[status(thm)],[c_1759])).

tff(c_22,plain,(
    ! [B_133,A_132,C_134,E_136,F_137,D_135] :
      ( v1_funct_1(k10_tmap_1(A_132,B_133,C_134,D_135,E_136,F_137))
      | ~ m1_subset_1(F_137,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_135),u1_struct_0(B_133))))
      | ~ v1_funct_2(F_137,u1_struct_0(D_135),u1_struct_0(B_133))
      | ~ v1_funct_1(F_137)
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_134),u1_struct_0(B_133))))
      | ~ v1_funct_2(E_136,u1_struct_0(C_134),u1_struct_0(B_133))
      | ~ v1_funct_1(E_136)
      | ~ m1_pre_topc(D_135,A_132)
      | v2_struct_0(D_135)
      | ~ m1_pre_topc(C_134,A_132)
      | v2_struct_0(C_134)
      | ~ l1_pre_topc(B_133)
      | ~ v2_pre_topc(B_133)
      | v2_struct_0(B_133)
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132)
      | v2_struct_0(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1786,plain,(
    ! [A_132,C_134,E_136] :
      ( v1_funct_1(k10_tmap_1(A_132,'#skF_1'('#skF_3','#skF_4','#skF_5'),C_134,'#skF_4',E_136,k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5'))))
      | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
      | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_134),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
      | ~ v1_funct_2(E_136,u1_struct_0(C_134),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
      | ~ v1_funct_1(E_136)
      | ~ m1_pre_topc('#skF_4',A_132)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_134,A_132)
      | v2_struct_0(C_134)
      | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132)
      | v2_struct_0(A_132) ) ),
    inference(resolution,[status(thm)],[c_1770,c_22])).

tff(c_1822,plain,(
    ! [A_132,C_134,E_136] :
      ( v1_funct_1(k10_tmap_1(A_132,'#skF_1'('#skF_3','#skF_4','#skF_5'),C_134,'#skF_4',E_136,k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5'))))
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_134),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
      | ~ v1_funct_2(E_136,u1_struct_0(C_134),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
      | ~ v1_funct_1(E_136)
      | ~ m1_pre_topc('#skF_4',A_132)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_134,A_132)
      | v2_struct_0(C_134)
      | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132)
      | v2_struct_0(A_132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1711,c_1744,c_1786])).

tff(c_1823,plain,(
    ! [A_132,C_134,E_136] :
      ( v1_funct_1(k10_tmap_1(A_132,'#skF_1'('#skF_3','#skF_4','#skF_5'),C_134,'#skF_4',E_136,k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5'))))
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_134),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
      | ~ v1_funct_2(E_136,u1_struct_0(C_134),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
      | ~ v1_funct_1(E_136)
      | ~ m1_pre_topc('#skF_4',A_132)
      | ~ m1_pre_topc(C_134,A_132)
      | v2_struct_0(C_134)
      | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132)
      | v2_struct_0(A_132) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_1822])).

tff(c_1850,plain,(
    ~ v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1823])).

tff(c_1853,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_1850])).

tff(c_1856,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_78,c_247,c_1853])).

tff(c_1858,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_80,c_250,c_1856])).

tff(c_1859,plain,(
    ! [A_132,C_134,E_136] :
      ( ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | v1_funct_1(k10_tmap_1(A_132,'#skF_1'('#skF_3','#skF_4','#skF_5'),C_134,'#skF_4',E_136,k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5'))))
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_134),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
      | ~ v1_funct_2(E_136,u1_struct_0(C_134),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
      | ~ v1_funct_1(E_136)
      | ~ m1_pre_topc('#skF_4',A_132)
      | ~ m1_pre_topc(C_134,A_132)
      | v2_struct_0(C_134)
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132)
      | v2_struct_0(A_132) ) ),
    inference(splitRight,[status(thm)],[c_1823])).

tff(c_1873,plain,(
    ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1859])).

tff(c_1876,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_1873])).

tff(c_1879,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_78,c_247,c_1876])).

tff(c_1881,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_80,c_250,c_1879])).

tff(c_1882,plain,(
    ! [A_132,C_134,E_136] :
      ( v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | v1_funct_1(k10_tmap_1(A_132,'#skF_1'('#skF_3','#skF_4','#skF_5'),C_134,'#skF_4',E_136,k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5'))))
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_134),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
      | ~ v1_funct_2(E_136,u1_struct_0(C_134),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
      | ~ v1_funct_1(E_136)
      | ~ m1_pre_topc('#skF_4',A_132)
      | ~ m1_pre_topc(C_134,A_132)
      | v2_struct_0(C_134)
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132)
      | v2_struct_0(A_132) ) ),
    inference(splitRight,[status(thm)],[c_1859])).

tff(c_1884,plain,(
    v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1882])).

tff(c_52,plain,(
    ! [A_138,B_166,C_180] :
      ( ~ v2_struct_0('#skF_1'(A_138,B_166,C_180))
      | r3_tsep_1(A_138,B_166,C_180)
      | ~ r1_tsep_1(B_166,C_180)
      | ~ m1_pre_topc(C_180,A_138)
      | v2_struct_0(C_180)
      | ~ m1_pre_topc(B_166,A_138)
      | v2_struct_0(B_166)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_1887,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1884,c_52])).

tff(c_1890,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_78,c_247,c_1887])).

tff(c_1892,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_80,c_250,c_1890])).

tff(c_1894,plain,(
    ~ v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1882])).

tff(c_30,plain,(
    ! [A_138,B_166,C_180] :
      ( v1_funct_2(k3_tmap_1(A_138,'#skF_1'(A_138,B_166,C_180),k1_tsep_1(A_138,B_166,C_180),C_180,'#skF_2'(A_138,B_166,C_180)),u1_struct_0(C_180),u1_struct_0('#skF_1'(A_138,B_166,C_180)))
      | r3_tsep_1(A_138,B_166,C_180)
      | ~ r1_tsep_1(B_166,C_180)
      | ~ m1_pre_topc(C_180,A_138)
      | v2_struct_0(C_180)
      | ~ m1_pre_topc(B_166,A_138)
      | v2_struct_0(B_166)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_1860,plain,(
    v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1823])).

tff(c_1883,plain,(
    l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1859])).

tff(c_1788,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_1770,c_2])).

tff(c_1826,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1711,c_1744,c_1788])).

tff(c_512,plain,(
    ! [A_432,B_433,C_434,E_497] :
      ( k10_tmap_1(A_432,'#skF_1'(A_432,B_433,C_434),B_433,C_434,E_497,k3_tmap_1(A_432,'#skF_1'(A_432,B_433,C_434),k1_tsep_1(A_432,B_433,C_434),C_434,'#skF_2'(A_432,B_433,C_434))) = '#skF_2'(A_432,B_433,C_434)
      | ~ r2_funct_2(u1_struct_0(B_433),u1_struct_0('#skF_1'(A_432,B_433,C_434)),k3_tmap_1(A_432,'#skF_1'(A_432,B_433,C_434),k1_tsep_1(A_432,B_433,C_434),B_433,'#skF_2'(A_432,B_433,C_434)),E_497)
      | ~ m1_subset_1('#skF_2'(A_432,B_433,C_434),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_432,B_433,C_434)),u1_struct_0('#skF_1'(A_432,B_433,C_434)))))
      | ~ v1_funct_2('#skF_2'(A_432,B_433,C_434),u1_struct_0(k1_tsep_1(A_432,B_433,C_434)),u1_struct_0('#skF_1'(A_432,B_433,C_434)))
      | ~ v1_funct_1('#skF_2'(A_432,B_433,C_434))
      | ~ m1_subset_1(k3_tmap_1(A_432,'#skF_1'(A_432,B_433,C_434),k1_tsep_1(A_432,B_433,C_434),C_434,'#skF_2'(A_432,B_433,C_434)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_434),u1_struct_0('#skF_1'(A_432,B_433,C_434)))))
      | ~ m1_subset_1(E_497,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_433),u1_struct_0('#skF_1'(A_432,B_433,C_434)))))
      | ~ v1_funct_2(E_497,u1_struct_0(B_433),u1_struct_0('#skF_1'(A_432,B_433,C_434)))
      | ~ v1_funct_1(E_497)
      | ~ l1_pre_topc('#skF_1'(A_432,B_433,C_434))
      | ~ v2_pre_topc('#skF_1'(A_432,B_433,C_434))
      | v2_struct_0('#skF_1'(A_432,B_433,C_434))
      | ~ v1_funct_2(k3_tmap_1(A_432,'#skF_1'(A_432,B_433,C_434),k1_tsep_1(A_432,B_433,C_434),C_434,'#skF_2'(A_432,B_433,C_434)),u1_struct_0(C_434),u1_struct_0('#skF_1'(A_432,B_433,C_434)))
      | ~ v1_funct_1(k3_tmap_1(A_432,'#skF_1'(A_432,B_433,C_434),k1_tsep_1(A_432,B_433,C_434),C_434,'#skF_2'(A_432,B_433,C_434)))
      | r3_tsep_1(A_432,B_433,C_434)
      | ~ r1_tsep_1(B_433,C_434)
      | ~ m1_pre_topc(C_434,A_432)
      | v2_struct_0(C_434)
      | ~ m1_pre_topc(B_433,A_432)
      | v2_struct_0(B_433)
      | ~ l1_pre_topc(A_432)
      | ~ v2_pre_topc(A_432)
      | v2_struct_0(A_432) ) ),
    inference(resolution,[status(thm)],[c_318,c_505])).

tff(c_1839,plain,
    ( k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_5',k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))) = '#skF_2'('#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1826,c_512])).

tff(c_1844,plain,
    ( k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_5',k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))) = '#skF_2'('#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_78,c_247,c_1757,c_1711,c_1744,c_1770,c_1839])).

tff(c_1845,plain,
    ( k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_5',k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))) = '#skF_2'('#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_80,c_250,c_1844])).

tff(c_1896,plain,
    ( k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_5',k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))) = '#skF_2'('#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1860,c_1883,c_1845])).

tff(c_1897,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_1896])).

tff(c_1900,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_1897])).

tff(c_1903,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_78,c_247,c_1900])).

tff(c_1905,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_80,c_250,c_1903])).

tff(c_1907,plain,(
    v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_1896])).

tff(c_1769,plain,
    ( ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | v5_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1759])).

tff(c_1942,plain,
    ( ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v5_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1907,c_1860,c_1883,c_1769])).

tff(c_1943,plain,
    ( ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | v5_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_1894,c_1942])).

tff(c_1944,plain,(
    ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1943])).

tff(c_1947,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_1944])).

tff(c_1950,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_78,c_247,c_1947])).

tff(c_1952,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_80,c_250,c_1950])).

tff(c_1954,plain,(
    v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1943])).

tff(c_42,plain,(
    ! [A_138,B_166,C_180] :
      ( m1_subset_1('#skF_2'(A_138,B_166,C_180),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_138,B_166,C_180)),u1_struct_0('#skF_1'(A_138,B_166,C_180)))))
      | r3_tsep_1(A_138,B_166,C_180)
      | ~ r1_tsep_1(B_166,C_180)
      | ~ m1_pre_topc(C_180,A_138)
      | v2_struct_0(C_180)
      | ~ m1_pre_topc(B_166,A_138)
      | v2_struct_0(B_166)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_44,plain,(
    ! [A_138,B_166,C_180] :
      ( v1_funct_2('#skF_2'(A_138,B_166,C_180),u1_struct_0(k1_tsep_1(A_138,B_166,C_180)),u1_struct_0('#skF_1'(A_138,B_166,C_180)))
      | r3_tsep_1(A_138,B_166,C_180)
      | ~ r1_tsep_1(B_166,C_180)
      | ~ m1_pre_topc(C_180,A_138)
      | v2_struct_0(C_180)
      | ~ m1_pre_topc(B_166,A_138)
      | v2_struct_0(B_166)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_36,plain,(
    ! [A_138,B_166,C_180] :
      ( v5_pre_topc(k3_tmap_1(A_138,'#skF_1'(A_138,B_166,C_180),k1_tsep_1(A_138,B_166,C_180),B_166,'#skF_2'(A_138,B_166,C_180)),B_166,'#skF_1'(A_138,B_166,C_180))
      | r3_tsep_1(A_138,B_166,C_180)
      | ~ r1_tsep_1(B_166,C_180)
      | ~ m1_pre_topc(C_180,A_138)
      | v2_struct_0(C_180)
      | ~ m1_pre_topc(B_166,A_138)
      | v2_struct_0(B_166)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_1953,plain,
    ( ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v5_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1943])).

tff(c_1955,plain,(
    ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1953])).

tff(c_1958,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_1955])).

tff(c_1961,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_78,c_247,c_1958])).

tff(c_1963,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_80,c_250,c_1961])).

tff(c_1964,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | v5_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1953])).

tff(c_1966,plain,(
    ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_1964])).

tff(c_1969,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_1966])).

tff(c_1972,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_78,c_247,c_1969])).

tff(c_1974,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_80,c_250,c_1972])).

tff(c_1975,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | v5_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1964])).

tff(c_1988,plain,(
    ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))))) ),
    inference(splitLeft,[status(thm)],[c_1975])).

tff(c_1991,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_1988])).

tff(c_1994,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_78,c_247,c_1991])).

tff(c_1996,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_80,c_250,c_1994])).

tff(c_1997,plain,(
    v5_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1975])).

tff(c_450,plain,(
    ! [A_465,B_466,C_467] :
      ( ~ m1_subset_1('#skF_2'(A_465,B_466,C_467),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_465,B_466,C_467)),u1_struct_0('#skF_1'(A_465,B_466,C_467)))))
      | ~ v5_pre_topc('#skF_2'(A_465,B_466,C_467),k1_tsep_1(A_465,B_466,C_467),'#skF_1'(A_465,B_466,C_467))
      | ~ v1_funct_2('#skF_2'(A_465,B_466,C_467),u1_struct_0(k1_tsep_1(A_465,B_466,C_467)),u1_struct_0('#skF_1'(A_465,B_466,C_467)))
      | ~ v1_funct_1('#skF_2'(A_465,B_466,C_467))
      | r3_tsep_1(A_465,B_466,C_467)
      | ~ r1_tsep_1(B_466,C_467)
      | ~ m1_pre_topc(C_467,A_465)
      | v2_struct_0(C_467)
      | ~ m1_pre_topc(B_466,A_465)
      | v2_struct_0(B_466)
      | ~ l1_pre_topc(A_465)
      | ~ v2_pre_topc(A_465)
      | v2_struct_0(A_465) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_455,plain,(
    ! [A_468,B_469,C_470] :
      ( ~ v5_pre_topc('#skF_2'(A_468,B_469,C_470),k1_tsep_1(A_468,B_469,C_470),'#skF_1'(A_468,B_469,C_470))
      | ~ v1_funct_2('#skF_2'(A_468,B_469,C_470),u1_struct_0(k1_tsep_1(A_468,B_469,C_470)),u1_struct_0('#skF_1'(A_468,B_469,C_470)))
      | ~ v1_funct_1('#skF_2'(A_468,B_469,C_470))
      | r3_tsep_1(A_468,B_469,C_470)
      | ~ r1_tsep_1(B_469,C_470)
      | ~ m1_pre_topc(C_470,A_468)
      | v2_struct_0(C_470)
      | ~ m1_pre_topc(B_469,A_468)
      | v2_struct_0(B_469)
      | ~ l1_pre_topc(A_468)
      | ~ v2_pre_topc(A_468)
      | v2_struct_0(A_468) ) ),
    inference(resolution,[status(thm)],[c_42,c_450])).

tff(c_459,plain,(
    ! [A_138,B_166,C_180] :
      ( ~ v5_pre_topc('#skF_2'(A_138,B_166,C_180),k1_tsep_1(A_138,B_166,C_180),'#skF_1'(A_138,B_166,C_180))
      | ~ v1_funct_1('#skF_2'(A_138,B_166,C_180))
      | r3_tsep_1(A_138,B_166,C_180)
      | ~ r1_tsep_1(B_166,C_180)
      | ~ m1_pre_topc(C_180,A_138)
      | v2_struct_0(C_180)
      | ~ m1_pre_topc(B_166,A_138)
      | v2_struct_0(B_166)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(resolution,[status(thm)],[c_44,c_455])).

tff(c_2001,plain,
    ( ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1997,c_459])).

tff(c_2004,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_78,c_247,c_1954,c_2001])).

tff(c_2006,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_80,c_250,c_2004])).

tff(c_2008,plain,(
    r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_74,plain,(
    ! [A_254,B_258,C_260] :
      ( r4_tsep_1(A_254,B_258,C_260)
      | ~ r3_tsep_1(A_254,B_258,C_260)
      | ~ m1_pre_topc(C_260,A_254)
      | v2_struct_0(C_260)
      | ~ m1_pre_topc(B_258,A_254)
      | v2_struct_0(B_258)
      | ~ l1_pre_topc(A_254)
      | ~ v2_pre_topc(A_254)
      | v2_struct_0(A_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_285])).

tff(c_110,plain,
    ( v1_funct_1('#skF_7')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_343])).

tff(c_2014,plain,(
    v1_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2008,c_247,c_110])).

tff(c_108,plain,
    ( v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_6'))
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_343])).

tff(c_2024,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2008,c_247,c_108])).

tff(c_106,plain,
    ( v5_pre_topc('#skF_7','#skF_4','#skF_6')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_343])).

tff(c_2020,plain,(
    v5_pre_topc('#skF_7','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2008,c_247,c_106])).

tff(c_104,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_6'))))
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_343])).

tff(c_2028,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_6')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2008,c_247,c_104])).

tff(c_116,plain,
    ( ~ v2_struct_0('#skF_6')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_343])).

tff(c_2012,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2008,c_247,c_116])).

tff(c_114,plain,
    ( v2_pre_topc('#skF_6')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_343])).

tff(c_2010,plain,(
    v2_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2008,c_247,c_114])).

tff(c_2007,plain,(
    l1_pre_topc('#skF_6') ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_102,plain,
    ( v1_funct_1('#skF_8')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_343])).

tff(c_2016,plain,(
    v1_funct_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2008,c_247,c_102])).

tff(c_100,plain,
    ( v1_funct_2('#skF_8',u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_343])).

tff(c_2022,plain,(
    v1_funct_2('#skF_8',u1_struct_0('#skF_5'),u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2008,c_247,c_100])).

tff(c_98,plain,
    ( v5_pre_topc('#skF_8','#skF_5','#skF_6')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_343])).

tff(c_2018,plain,(
    v5_pre_topc('#skF_8','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2008,c_247,c_98])).

tff(c_96,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))))
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_343])).

tff(c_2026,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2008,c_247,c_96])).

tff(c_2674,plain,(
    ! [C_1167,D_1171,A_1168,E_1170,B_1172,F_1169] :
      ( v5_pre_topc(k10_tmap_1(A_1168,B_1172,C_1167,D_1171,E_1170,F_1169),k1_tsep_1(A_1168,C_1167,D_1171),B_1172)
      | ~ r4_tsep_1(A_1168,C_1167,D_1171)
      | ~ m1_subset_1(F_1169,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_1171),u1_struct_0(B_1172))))
      | ~ v5_pre_topc(F_1169,D_1171,B_1172)
      | ~ v1_funct_2(F_1169,u1_struct_0(D_1171),u1_struct_0(B_1172))
      | ~ v1_funct_1(F_1169)
      | ~ m1_subset_1(E_1170,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1167),u1_struct_0(B_1172))))
      | ~ v5_pre_topc(E_1170,C_1167,B_1172)
      | ~ v1_funct_2(E_1170,u1_struct_0(C_1167),u1_struct_0(B_1172))
      | ~ v1_funct_1(E_1170)
      | ~ r1_tsep_1(C_1167,D_1171)
      | ~ m1_pre_topc(D_1171,A_1168)
      | v2_struct_0(D_1171)
      | ~ m1_pre_topc(C_1167,A_1168)
      | v2_struct_0(C_1167)
      | ~ l1_pre_topc(B_1172)
      | ~ v2_pre_topc(B_1172)
      | v2_struct_0(B_1172)
      | ~ l1_pre_topc(A_1168)
      | ~ v2_pre_topc(A_1168)
      | v2_struct_0(A_1168) ) ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_2688,plain,(
    ! [A_1168,C_1167,E_1170] :
      ( v5_pre_topc(k10_tmap_1(A_1168,'#skF_6',C_1167,'#skF_5',E_1170,'#skF_8'),k1_tsep_1(A_1168,C_1167,'#skF_5'),'#skF_6')
      | ~ r4_tsep_1(A_1168,C_1167,'#skF_5')
      | ~ v5_pre_topc('#skF_8','#skF_5','#skF_6')
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_1170,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1167),u1_struct_0('#skF_6'))))
      | ~ v5_pre_topc(E_1170,C_1167,'#skF_6')
      | ~ v1_funct_2(E_1170,u1_struct_0(C_1167),u1_struct_0('#skF_6'))
      | ~ v1_funct_1(E_1170)
      | ~ r1_tsep_1(C_1167,'#skF_5')
      | ~ m1_pre_topc('#skF_5',A_1168)
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(C_1167,A_1168)
      | v2_struct_0(C_1167)
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc(A_1168)
      | ~ v2_pre_topc(A_1168)
      | v2_struct_0(A_1168) ) ),
    inference(resolution,[status(thm)],[c_2026,c_2674])).

tff(c_2703,plain,(
    ! [A_1168,C_1167,E_1170] :
      ( v5_pre_topc(k10_tmap_1(A_1168,'#skF_6',C_1167,'#skF_5',E_1170,'#skF_8'),k1_tsep_1(A_1168,C_1167,'#skF_5'),'#skF_6')
      | ~ r4_tsep_1(A_1168,C_1167,'#skF_5')
      | ~ m1_subset_1(E_1170,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1167),u1_struct_0('#skF_6'))))
      | ~ v5_pre_topc(E_1170,C_1167,'#skF_6')
      | ~ v1_funct_2(E_1170,u1_struct_0(C_1167),u1_struct_0('#skF_6'))
      | ~ v1_funct_1(E_1170)
      | ~ r1_tsep_1(C_1167,'#skF_5')
      | ~ m1_pre_topc('#skF_5',A_1168)
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(C_1167,A_1168)
      | v2_struct_0(C_1167)
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc(A_1168)
      | ~ v2_pre_topc(A_1168)
      | v2_struct_0(A_1168) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2010,c_2007,c_2016,c_2022,c_2018,c_2688])).

tff(c_2736,plain,(
    ! [A_1176,C_1177,E_1178] :
      ( v5_pre_topc(k10_tmap_1(A_1176,'#skF_6',C_1177,'#skF_5',E_1178,'#skF_8'),k1_tsep_1(A_1176,C_1177,'#skF_5'),'#skF_6')
      | ~ r4_tsep_1(A_1176,C_1177,'#skF_5')
      | ~ m1_subset_1(E_1178,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1177),u1_struct_0('#skF_6'))))
      | ~ v5_pre_topc(E_1178,C_1177,'#skF_6')
      | ~ v1_funct_2(E_1178,u1_struct_0(C_1177),u1_struct_0('#skF_6'))
      | ~ v1_funct_1(E_1178)
      | ~ r1_tsep_1(C_1177,'#skF_5')
      | ~ m1_pre_topc('#skF_5',A_1176)
      | ~ m1_pre_topc(C_1177,A_1176)
      | v2_struct_0(C_1177)
      | ~ l1_pre_topc(A_1176)
      | ~ v2_pre_topc(A_1176)
      | v2_struct_0(A_1176) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2012,c_80,c_2703])).

tff(c_2743,plain,(
    ! [A_1176] :
      ( v5_pre_topc(k10_tmap_1(A_1176,'#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),k1_tsep_1(A_1176,'#skF_4','#skF_5'),'#skF_6')
      | ~ r4_tsep_1(A_1176,'#skF_4','#skF_5')
      | ~ v5_pre_topc('#skF_7','#skF_4','#skF_6')
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_6'))
      | ~ v1_funct_1('#skF_7')
      | ~ r1_tsep_1('#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5',A_1176)
      | ~ m1_pre_topc('#skF_4',A_1176)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_1176)
      | ~ v2_pre_topc(A_1176)
      | v2_struct_0(A_1176) ) ),
    inference(resolution,[status(thm)],[c_2028,c_2736])).

tff(c_2755,plain,(
    ! [A_1176] :
      ( v5_pre_topc(k10_tmap_1(A_1176,'#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),k1_tsep_1(A_1176,'#skF_4','#skF_5'),'#skF_6')
      | ~ r4_tsep_1(A_1176,'#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5',A_1176)
      | ~ m1_pre_topc('#skF_4',A_1176)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_1176)
      | ~ v2_pre_topc(A_1176)
      | v2_struct_0(A_1176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_2014,c_2024,c_2020,c_2743])).

tff(c_2761,plain,(
    ! [A_1179] :
      ( v5_pre_topc(k10_tmap_1(A_1179,'#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),k1_tsep_1(A_1179,'#skF_4','#skF_5'),'#skF_6')
      | ~ r4_tsep_1(A_1179,'#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5',A_1179)
      | ~ m1_pre_topc('#skF_4',A_1179)
      | ~ l1_pre_topc(A_1179)
      | ~ v2_pre_topc(A_1179)
      | v2_struct_0(A_1179) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2755])).

tff(c_2466,plain,(
    ! [B_1123,A_1121,D_1126,F_1125,E_1124,C_1122] :
      ( v1_funct_2(k10_tmap_1(A_1121,B_1123,C_1122,D_1126,E_1124,F_1125),u1_struct_0(k1_tsep_1(A_1121,C_1122,D_1126)),u1_struct_0(B_1123))
      | ~ m1_subset_1(F_1125,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_1126),u1_struct_0(B_1123))))
      | ~ v1_funct_2(F_1125,u1_struct_0(D_1126),u1_struct_0(B_1123))
      | ~ v1_funct_1(F_1125)
      | ~ m1_subset_1(E_1124,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1122),u1_struct_0(B_1123))))
      | ~ v1_funct_2(E_1124,u1_struct_0(C_1122),u1_struct_0(B_1123))
      | ~ v1_funct_1(E_1124)
      | ~ m1_pre_topc(D_1126,A_1121)
      | v2_struct_0(D_1126)
      | ~ m1_pre_topc(C_1122,A_1121)
      | v2_struct_0(C_1122)
      | ~ l1_pre_topc(B_1123)
      | ~ v2_pre_topc(B_1123)
      | v2_struct_0(B_1123)
      | ~ l1_pre_topc(A_1121)
      | ~ v2_pre_topc(A_1121)
      | v2_struct_0(A_1121) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_2300,plain,(
    ! [A_1096,D_1101,C_1097,F_1100,B_1098,E_1099] :
      ( m1_subset_1(k10_tmap_1(A_1096,B_1098,C_1097,D_1101,E_1099,F_1100),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_1096,C_1097,D_1101)),u1_struct_0(B_1098))))
      | ~ m1_subset_1(F_1100,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_1101),u1_struct_0(B_1098))))
      | ~ v1_funct_2(F_1100,u1_struct_0(D_1101),u1_struct_0(B_1098))
      | ~ v1_funct_1(F_1100)
      | ~ m1_subset_1(E_1099,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1097),u1_struct_0(B_1098))))
      | ~ v1_funct_2(E_1099,u1_struct_0(C_1097),u1_struct_0(B_1098))
      | ~ v1_funct_1(E_1099)
      | ~ m1_pre_topc(D_1101,A_1096)
      | v2_struct_0(D_1101)
      | ~ m1_pre_topc(C_1097,A_1096)
      | v2_struct_0(C_1097)
      | ~ l1_pre_topc(B_1098)
      | ~ v2_pre_topc(B_1098)
      | v2_struct_0(B_1098)
      | ~ l1_pre_topc(A_1096)
      | ~ v2_pre_topc(A_1096)
      | v2_struct_0(A_1096) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_2108,plain,(
    ! [E_1058,D_1060,B_1057,C_1056,F_1059,A_1055] :
      ( v1_funct_1(k10_tmap_1(A_1055,B_1057,C_1056,D_1060,E_1058,F_1059))
      | ~ m1_subset_1(F_1059,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_1060),u1_struct_0(B_1057))))
      | ~ v1_funct_2(F_1059,u1_struct_0(D_1060),u1_struct_0(B_1057))
      | ~ v1_funct_1(F_1059)
      | ~ m1_subset_1(E_1058,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1056),u1_struct_0(B_1057))))
      | ~ v1_funct_2(E_1058,u1_struct_0(C_1056),u1_struct_0(B_1057))
      | ~ v1_funct_1(E_1058)
      | ~ m1_pre_topc(D_1060,A_1055)
      | v2_struct_0(D_1060)
      | ~ m1_pre_topc(C_1056,A_1055)
      | v2_struct_0(C_1056)
      | ~ l1_pre_topc(B_1057)
      | ~ v2_pre_topc(B_1057)
      | v2_struct_0(B_1057)
      | ~ l1_pre_topc(A_1055)
      | ~ v2_pre_topc(A_1055)
      | v2_struct_0(A_1055) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_2118,plain,(
    ! [A_1055,C_1056,E_1058] :
      ( v1_funct_1(k10_tmap_1(A_1055,'#skF_6',C_1056,'#skF_5',E_1058,'#skF_8'))
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_1058,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1056),u1_struct_0('#skF_6'))))
      | ~ v1_funct_2(E_1058,u1_struct_0(C_1056),u1_struct_0('#skF_6'))
      | ~ v1_funct_1(E_1058)
      | ~ m1_pre_topc('#skF_5',A_1055)
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(C_1056,A_1055)
      | v2_struct_0(C_1056)
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc(A_1055)
      | ~ v2_pre_topc(A_1055)
      | v2_struct_0(A_1055) ) ),
    inference(resolution,[status(thm)],[c_2026,c_2108])).

tff(c_2128,plain,(
    ! [A_1055,C_1056,E_1058] :
      ( v1_funct_1(k10_tmap_1(A_1055,'#skF_6',C_1056,'#skF_5',E_1058,'#skF_8'))
      | ~ m1_subset_1(E_1058,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1056),u1_struct_0('#skF_6'))))
      | ~ v1_funct_2(E_1058,u1_struct_0(C_1056),u1_struct_0('#skF_6'))
      | ~ v1_funct_1(E_1058)
      | ~ m1_pre_topc('#skF_5',A_1055)
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(C_1056,A_1055)
      | v2_struct_0(C_1056)
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc(A_1055)
      | ~ v2_pre_topc(A_1055)
      | v2_struct_0(A_1055) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2010,c_2007,c_2016,c_2022,c_2118])).

tff(c_2147,plain,(
    ! [A_1066,C_1067,E_1068] :
      ( v1_funct_1(k10_tmap_1(A_1066,'#skF_6',C_1067,'#skF_5',E_1068,'#skF_8'))
      | ~ m1_subset_1(E_1068,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1067),u1_struct_0('#skF_6'))))
      | ~ v1_funct_2(E_1068,u1_struct_0(C_1067),u1_struct_0('#skF_6'))
      | ~ v1_funct_1(E_1068)
      | ~ m1_pre_topc('#skF_5',A_1066)
      | ~ m1_pre_topc(C_1067,A_1066)
      | v2_struct_0(C_1067)
      | ~ l1_pre_topc(A_1066)
      | ~ v2_pre_topc(A_1066)
      | v2_struct_0(A_1066) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2012,c_80,c_2128])).

tff(c_2149,plain,(
    ! [A_1066] :
      ( v1_funct_1(k10_tmap_1(A_1066,'#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'))
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_6'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_pre_topc('#skF_5',A_1066)
      | ~ m1_pre_topc('#skF_4',A_1066)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_1066)
      | ~ v2_pre_topc(A_1066)
      | v2_struct_0(A_1066) ) ),
    inference(resolution,[status(thm)],[c_2028,c_2147])).

tff(c_2154,plain,(
    ! [A_1066] :
      ( v1_funct_1(k10_tmap_1(A_1066,'#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'))
      | ~ m1_pre_topc('#skF_5',A_1066)
      | ~ m1_pre_topc('#skF_4',A_1066)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_1066)
      | ~ v2_pre_topc(A_1066)
      | v2_struct_0(A_1066) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2014,c_2024,c_2149])).

tff(c_2161,plain,(
    ! [A_1070] :
      ( v1_funct_1(k10_tmap_1(A_1070,'#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'))
      | ~ m1_pre_topc('#skF_5',A_1070)
      | ~ m1_pre_topc('#skF_4',A_1070)
      | ~ l1_pre_topc(A_1070)
      | ~ v2_pre_topc(A_1070)
      | v2_struct_0(A_1070) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2154])).

tff(c_94,plain,
    ( ~ m1_subset_1(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_6'))))
    | ~ v5_pre_topc(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_6')
    | ~ v1_funct_2(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_6'))
    | ~ v1_funct_1(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'))
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_343])).

tff(c_2102,plain,
    ( ~ m1_subset_1(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_6'))))
    | ~ v5_pre_topc(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_6')
    | ~ v1_funct_2(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_6'))
    | ~ v1_funct_1(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2008,c_247,c_94])).

tff(c_2103,plain,(
    ~ v1_funct_1(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_2102])).

tff(c_2164,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2161,c_2103])).

tff(c_2167,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_78,c_2164])).

tff(c_2169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_2167])).

tff(c_2170,plain,
    ( ~ v1_funct_2(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_6'))
    | ~ v5_pre_topc(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_6')
    | ~ m1_subset_1(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_6')))) ),
    inference(splitRight,[status(thm)],[c_2102])).

tff(c_2172,plain,(
    ~ m1_subset_1(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_6')))) ),
    inference(splitLeft,[status(thm)],[c_2170])).

tff(c_2311,plain,
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
    inference(resolution,[status(thm)],[c_2300,c_2172])).

tff(c_2325,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_2010,c_2007,c_82,c_78,c_2014,c_2024,c_2028,c_2016,c_2022,c_2026,c_2311])).

tff(c_2327,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_2012,c_84,c_80,c_2325])).

tff(c_2328,plain,
    ( ~ v5_pre_topc(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_6')
    | ~ v1_funct_2(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_2170])).

tff(c_2335,plain,(
    ~ v1_funct_2(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_2328])).

tff(c_2469,plain,
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
    inference(resolution,[status(thm)],[c_2466,c_2335])).

tff(c_2472,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_2010,c_2007,c_82,c_78,c_2014,c_2024,c_2028,c_2016,c_2022,c_2026,c_2469])).

tff(c_2474,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_2012,c_84,c_80,c_2472])).

tff(c_2475,plain,(
    ~ v5_pre_topc(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_2328])).

tff(c_2764,plain,
    ( ~ r4_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2761,c_2475])).

tff(c_2767,plain,
    ( ~ r4_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_78,c_2764])).

tff(c_2768,plain,(
    ~ r4_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_2767])).

tff(c_2771,plain,
    ( ~ r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_2768])).

tff(c_2774,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_78,c_2008,c_2771])).

tff(c_2776,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_80,c_2774])).

tff(c_2778,plain,(
    ~ r1_tsep_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_2777,plain,(
    r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_2806,plain,(
    ! [B_1183,C_1184,A_1185] :
      ( r1_tsep_1(B_1183,C_1184)
      | ~ r3_tsep_1(A_1185,B_1183,C_1184)
      | ~ m1_pre_topc(C_1184,A_1185)
      | v2_struct_0(C_1184)
      | ~ m1_pre_topc(B_1183,A_1185)
      | v2_struct_0(B_1183)
      | ~ l1_pre_topc(A_1185)
      | ~ v2_pre_topc(A_1185)
      | v2_struct_0(A_1185) ) ),
    inference(cnfTransformation,[status(thm)],[f_285])).

tff(c_2809,plain,
    ( r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2777,c_2806])).

tff(c_2812,plain,
    ( r1_tsep_1('#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_78,c_2809])).

tff(c_2814,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_80,c_2778,c_2812])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:11:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.56/4.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.56/4.22  
% 11.56/4.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.56/4.23  %$ r2_funct_2 > v5_pre_topc > v1_funct_2 > r4_tsep_1 > r3_tsep_1 > r1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k2_tsep_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_8 > #skF_4
% 11.56/4.23  
% 11.56/4.23  %Foreground sorts:
% 11.56/4.23  
% 11.56/4.23  
% 11.56/4.23  %Background operators:
% 11.56/4.23  
% 11.56/4.23  
% 11.56/4.23  %Foreground operators:
% 11.56/4.23  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 11.56/4.23  tff(k10_tmap_1, type, k10_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.56/4.23  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 11.56/4.23  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 11.56/4.23  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 11.56/4.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.56/4.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.56/4.23  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.56/4.23  tff('#skF_7', type, '#skF_7': $i).
% 11.56/4.23  tff(r4_tsep_1, type, r4_tsep_1: ($i * $i * $i) > $o).
% 11.56/4.23  tff('#skF_5', type, '#skF_5': $i).
% 11.56/4.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.56/4.23  tff('#skF_6', type, '#skF_6': $i).
% 11.56/4.23  tff('#skF_3', type, '#skF_3': $i).
% 11.56/4.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.56/4.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.56/4.23  tff('#skF_8', type, '#skF_8': $i).
% 11.56/4.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.56/4.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.56/4.23  tff('#skF_4', type, '#skF_4': $i).
% 11.56/4.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.56/4.23  tff(r3_tsep_1, type, r3_tsep_1: ($i * $i * $i) > $o).
% 11.56/4.23  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 11.56/4.23  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 11.56/4.23  tff(k2_tsep_1, type, k2_tsep_1: ($i * $i * $i) > $i).
% 11.56/4.23  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.56/4.23  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 11.56/4.23  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.56/4.23  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 11.56/4.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.56/4.23  
% 11.89/4.27  tff(f_343, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (r3_tsep_1(A, B, C) <=> (r1_tsep_1(B, C) & (![D]: (((~v2_struct_0(D) & v2_pre_topc(D)) & l1_pre_topc(D)) => (![E]: ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(B), u1_struct_0(D))) & v5_pre_topc(E, B, D)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(D))))) => (![F]: ((((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(D))) & v5_pre_topc(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(D))))) => (((v1_funct_1(k10_tmap_1(A, D, B, C, E, F)) & v1_funct_2(k10_tmap_1(A, D, B, C, E, F), u1_struct_0(k1_tsep_1(A, B, C)), u1_struct_0(D))) & v5_pre_topc(k10_tmap_1(A, D, B, C, E, F), k1_tsep_1(A, B, C), D)) & m1_subset_1(k10_tmap_1(A, D, B, C, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, B, C)), u1_struct_0(D))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_tmap_1)).
% 11.89/4.27  tff(f_203, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (r3_tsep_1(A, B, C) <=> (r1_tsep_1(B, C) & (![D]: (((~v2_struct_0(D) & v2_pre_topc(D)) & l1_pre_topc(D)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, B, C)), u1_struct_0(D))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, B, C)), u1_struct_0(D))))) => ((((((((v1_funct_1(k3_tmap_1(A, D, k1_tsep_1(A, B, C), B, E)) & v1_funct_2(k3_tmap_1(A, D, k1_tsep_1(A, B, C), B, E), u1_struct_0(B), u1_struct_0(D))) & v5_pre_topc(k3_tmap_1(A, D, k1_tsep_1(A, B, C), B, E), B, D)) & m1_subset_1(k3_tmap_1(A, D, k1_tsep_1(A, B, C), B, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(D))))) & v1_funct_1(k3_tmap_1(A, D, k1_tsep_1(A, B, C), C, E))) & v1_funct_2(k3_tmap_1(A, D, k1_tsep_1(A, B, C), C, E), u1_struct_0(C), u1_struct_0(D))) & v5_pre_topc(k3_tmap_1(A, D, k1_tsep_1(A, B, C), C, E), C, D)) & m1_subset_1(k3_tmap_1(A, D, k1_tsep_1(A, B, C), C, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(D))))) => (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, B, C)), u1_struct_0(D))) & v5_pre_topc(E, k1_tsep_1(A, B, C), D)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, B, C)), u1_struct_0(D)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t135_tmap_1)).
% 11.89/4.27  tff(f_41, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 11.89/4.27  tff(f_99, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((r1_tsep_1(C, D) | r2_funct_2(u1_struct_0(k2_tsep_1(A, C, D)), u1_struct_0(B), k3_tmap_1(A, B, C, k2_tsep_1(A, C, D), E), k3_tmap_1(A, B, D, k2_tsep_1(A, C, D), F))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) => ((G = k10_tmap_1(A, B, C, D, E, F)) <=> (r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, G), E) & r2_funct_2(u1_struct_0(D), u1_struct_0(B), k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, G), F)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_tmap_1)).
% 11.89/4.27  tff(f_141, axiom, (![A, B, C, D, E, F]: ((((((((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) & ~v2_struct_0(D)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(F)) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_tmap_1)).
% 11.89/4.27  tff(f_285, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => ((r1_tsep_1(B, C) & r4_tsep_1(A, B, C)) <=> r3_tsep_1(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_tsep_1)).
% 11.89/4.27  tff(f_260, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (r1_tsep_1(C, D) => (![E]: ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: ((((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (r4_tsep_1(A, C, D) => (((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & v5_pre_topc(k10_tmap_1(A, B, C, D, E, F), k1_tsep_1(A, C, D), B)) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_tmap_1)).
% 11.89/4.27  tff(c_90, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_343])).
% 11.89/4.27  tff(c_84, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_343])).
% 11.89/4.27  tff(c_80, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_343])).
% 11.89/4.27  tff(c_88, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_343])).
% 11.89/4.27  tff(c_86, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_343])).
% 11.89/4.27  tff(c_82, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_343])).
% 11.89/4.27  tff(c_78, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_343])).
% 11.89/4.27  tff(c_222, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | r1_tsep_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_343])).
% 11.89/4.27  tff(c_247, plain, (r1_tsep_1('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_222])).
% 11.89/4.27  tff(c_112, plain, (l1_pre_topc('#skF_6') | ~r1_tsep_1('#skF_4', '#skF_5') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_343])).
% 11.89/4.27  tff(c_249, plain, (l1_pre_topc('#skF_6') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_247, c_112])).
% 11.89/4.27  tff(c_250, plain, (~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_249])).
% 11.89/4.27  tff(c_46, plain, (![A_138, B_166, C_180]: (v1_funct_1('#skF_2'(A_138, B_166, C_180)) | r3_tsep_1(A_138, B_166, C_180) | ~r1_tsep_1(B_166, C_180) | ~m1_pre_topc(C_180, A_138) | v2_struct_0(C_180) | ~m1_pre_topc(B_166, A_138) | v2_struct_0(B_166) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_203])).
% 11.89/4.27  tff(c_48, plain, (![A_138, B_166, C_180]: (l1_pre_topc('#skF_1'(A_138, B_166, C_180)) | r3_tsep_1(A_138, B_166, C_180) | ~r1_tsep_1(B_166, C_180) | ~m1_pre_topc(C_180, A_138) | v2_struct_0(C_180) | ~m1_pre_topc(B_166, A_138) | v2_struct_0(B_166) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_203])).
% 11.89/4.27  tff(c_50, plain, (![A_138, B_166, C_180]: (v2_pre_topc('#skF_1'(A_138, B_166, C_180)) | r3_tsep_1(A_138, B_166, C_180) | ~r1_tsep_1(B_166, C_180) | ~m1_pre_topc(C_180, A_138) | v2_struct_0(C_180) | ~m1_pre_topc(B_166, A_138) | v2_struct_0(B_166) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_203])).
% 11.89/4.27  tff(c_40, plain, (![A_138, B_166, C_180]: (v1_funct_1(k3_tmap_1(A_138, '#skF_1'(A_138, B_166, C_180), k1_tsep_1(A_138, B_166, C_180), B_166, '#skF_2'(A_138, B_166, C_180))) | r3_tsep_1(A_138, B_166, C_180) | ~r1_tsep_1(B_166, C_180) | ~m1_pre_topc(C_180, A_138) | v2_struct_0(C_180) | ~m1_pre_topc(B_166, A_138) | v2_struct_0(B_166) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_203])).
% 11.89/4.27  tff(c_34, plain, (![A_138, B_166, C_180]: (m1_subset_1(k3_tmap_1(A_138, '#skF_1'(A_138, B_166, C_180), k1_tsep_1(A_138, B_166, C_180), B_166, '#skF_2'(A_138, B_166, C_180)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_166), u1_struct_0('#skF_1'(A_138, B_166, C_180))))) | r3_tsep_1(A_138, B_166, C_180) | ~r1_tsep_1(B_166, C_180) | ~m1_pre_topc(C_180, A_138) | v2_struct_0(C_180) | ~m1_pre_topc(B_166, A_138) | v2_struct_0(B_166) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_203])).
% 11.89/4.27  tff(c_26, plain, (![A_138, B_166, C_180]: (m1_subset_1(k3_tmap_1(A_138, '#skF_1'(A_138, B_166, C_180), k1_tsep_1(A_138, B_166, C_180), C_180, '#skF_2'(A_138, B_166, C_180)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_180), u1_struct_0('#skF_1'(A_138, B_166, C_180))))) | r3_tsep_1(A_138, B_166, C_180) | ~r1_tsep_1(B_166, C_180) | ~m1_pre_topc(C_180, A_138) | v2_struct_0(C_180) | ~m1_pre_topc(B_166, A_138) | v2_struct_0(B_166) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_203])).
% 11.89/4.27  tff(c_299, plain, (![A_429, B_430, C_431]: (m1_subset_1(k3_tmap_1(A_429, '#skF_1'(A_429, B_430, C_431), k1_tsep_1(A_429, B_430, C_431), B_430, '#skF_2'(A_429, B_430, C_431)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_430), u1_struct_0('#skF_1'(A_429, B_430, C_431))))) | r3_tsep_1(A_429, B_430, C_431) | ~r1_tsep_1(B_430, C_431) | ~m1_pre_topc(C_431, A_429) | v2_struct_0(C_431) | ~m1_pre_topc(B_430, A_429) | v2_struct_0(B_430) | ~l1_pre_topc(A_429) | ~v2_pre_topc(A_429) | v2_struct_0(A_429))), inference(cnfTransformation, [status(thm)], [f_203])).
% 11.89/4.27  tff(c_2, plain, (![A_1, B_2, D_4]: (r2_funct_2(A_1, B_2, D_4, D_4) | ~m1_subset_1(D_4, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(D_4, A_1, B_2) | ~v1_funct_1(D_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.89/4.27  tff(c_308, plain, (![B_430, A_429, C_431]: (r2_funct_2(u1_struct_0(B_430), u1_struct_0('#skF_1'(A_429, B_430, C_431)), k3_tmap_1(A_429, '#skF_1'(A_429, B_430, C_431), k1_tsep_1(A_429, B_430, C_431), B_430, '#skF_2'(A_429, B_430, C_431)), k3_tmap_1(A_429, '#skF_1'(A_429, B_430, C_431), k1_tsep_1(A_429, B_430, C_431), B_430, '#skF_2'(A_429, B_430, C_431))) | ~v1_funct_2(k3_tmap_1(A_429, '#skF_1'(A_429, B_430, C_431), k1_tsep_1(A_429, B_430, C_431), B_430, '#skF_2'(A_429, B_430, C_431)), u1_struct_0(B_430), u1_struct_0('#skF_1'(A_429, B_430, C_431))) | ~v1_funct_1(k3_tmap_1(A_429, '#skF_1'(A_429, B_430, C_431), k1_tsep_1(A_429, B_430, C_431), B_430, '#skF_2'(A_429, B_430, C_431))) | r3_tsep_1(A_429, B_430, C_431) | ~r1_tsep_1(B_430, C_431) | ~m1_pre_topc(C_431, A_429) | v2_struct_0(C_431) | ~m1_pre_topc(B_430, A_429) | v2_struct_0(B_430) | ~l1_pre_topc(A_429) | ~v2_pre_topc(A_429) | v2_struct_0(A_429))), inference(resolution, [status(thm)], [c_299, c_2])).
% 11.89/4.27  tff(c_309, plain, (![A_432, B_433, C_434]: (m1_subset_1(k3_tmap_1(A_432, '#skF_1'(A_432, B_433, C_434), k1_tsep_1(A_432, B_433, C_434), C_434, '#skF_2'(A_432, B_433, C_434)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_434), u1_struct_0('#skF_1'(A_432, B_433, C_434))))) | r3_tsep_1(A_432, B_433, C_434) | ~r1_tsep_1(B_433, C_434) | ~m1_pre_topc(C_434, A_432) | v2_struct_0(C_434) | ~m1_pre_topc(B_433, A_432) | v2_struct_0(B_433) | ~l1_pre_topc(A_432) | ~v2_pre_topc(A_432) | v2_struct_0(A_432))), inference(cnfTransformation, [status(thm)], [f_203])).
% 11.89/4.27  tff(c_318, plain, (![C_434, A_432, B_433]: (r2_funct_2(u1_struct_0(C_434), u1_struct_0('#skF_1'(A_432, B_433, C_434)), k3_tmap_1(A_432, '#skF_1'(A_432, B_433, C_434), k1_tsep_1(A_432, B_433, C_434), C_434, '#skF_2'(A_432, B_433, C_434)), k3_tmap_1(A_432, '#skF_1'(A_432, B_433, C_434), k1_tsep_1(A_432, B_433, C_434), C_434, '#skF_2'(A_432, B_433, C_434))) | ~v1_funct_2(k3_tmap_1(A_432, '#skF_1'(A_432, B_433, C_434), k1_tsep_1(A_432, B_433, C_434), C_434, '#skF_2'(A_432, B_433, C_434)), u1_struct_0(C_434), u1_struct_0('#skF_1'(A_432, B_433, C_434))) | ~v1_funct_1(k3_tmap_1(A_432, '#skF_1'(A_432, B_433, C_434), k1_tsep_1(A_432, B_433, C_434), C_434, '#skF_2'(A_432, B_433, C_434))) | r3_tsep_1(A_432, B_433, C_434) | ~r1_tsep_1(B_433, C_434) | ~m1_pre_topc(C_434, A_432) | v2_struct_0(C_434) | ~m1_pre_topc(B_433, A_432) | v2_struct_0(B_433) | ~l1_pre_topc(A_432) | ~v2_pre_topc(A_432) | v2_struct_0(A_432))), inference(resolution, [status(thm)], [c_309, c_2])).
% 11.89/4.27  tff(c_505, plain, (![D_500, C_498, G_495, F_501, B_496, A_499, E_497]: (~r1_tsep_1(C_498, D_500) | k10_tmap_1(A_499, B_496, C_498, D_500, E_497, F_501)=G_495 | ~r2_funct_2(u1_struct_0(D_500), u1_struct_0(B_496), k3_tmap_1(A_499, B_496, k1_tsep_1(A_499, C_498, D_500), D_500, G_495), F_501) | ~r2_funct_2(u1_struct_0(C_498), u1_struct_0(B_496), k3_tmap_1(A_499, B_496, k1_tsep_1(A_499, C_498, D_500), C_498, G_495), E_497) | ~m1_subset_1(G_495, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_499, C_498, D_500)), u1_struct_0(B_496)))) | ~v1_funct_2(G_495, u1_struct_0(k1_tsep_1(A_499, C_498, D_500)), u1_struct_0(B_496)) | ~v1_funct_1(G_495) | ~m1_subset_1(F_501, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_500), u1_struct_0(B_496)))) | ~v1_funct_2(F_501, u1_struct_0(D_500), u1_struct_0(B_496)) | ~v1_funct_1(F_501) | ~m1_subset_1(E_497, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_498), u1_struct_0(B_496)))) | ~v1_funct_2(E_497, u1_struct_0(C_498), u1_struct_0(B_496)) | ~v1_funct_1(E_497) | ~m1_pre_topc(D_500, A_499) | v2_struct_0(D_500) | ~m1_pre_topc(C_498, A_499) | v2_struct_0(C_498) | ~l1_pre_topc(B_496) | ~v2_pre_topc(B_496) | v2_struct_0(B_496) | ~l1_pre_topc(A_499) | ~v2_pre_topc(A_499) | v2_struct_0(A_499))), inference(cnfTransformation, [status(thm)], [f_99])).
% 11.89/4.27  tff(c_1093, plain, (![A_836, B_837, C_838, E_839]: (k10_tmap_1(A_836, '#skF_1'(A_836, B_837, C_838), B_837, C_838, E_839, k3_tmap_1(A_836, '#skF_1'(A_836, B_837, C_838), k1_tsep_1(A_836, B_837, C_838), C_838, '#skF_2'(A_836, B_837, C_838)))='#skF_2'(A_836, B_837, C_838) | ~r2_funct_2(u1_struct_0(B_837), u1_struct_0('#skF_1'(A_836, B_837, C_838)), k3_tmap_1(A_836, '#skF_1'(A_836, B_837, C_838), k1_tsep_1(A_836, B_837, C_838), B_837, '#skF_2'(A_836, B_837, C_838)), E_839) | ~m1_subset_1('#skF_2'(A_836, B_837, C_838), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_836, B_837, C_838)), u1_struct_0('#skF_1'(A_836, B_837, C_838))))) | ~v1_funct_2('#skF_2'(A_836, B_837, C_838), u1_struct_0(k1_tsep_1(A_836, B_837, C_838)), u1_struct_0('#skF_1'(A_836, B_837, C_838))) | ~v1_funct_1('#skF_2'(A_836, B_837, C_838)) | ~m1_subset_1(k3_tmap_1(A_836, '#skF_1'(A_836, B_837, C_838), k1_tsep_1(A_836, B_837, C_838), C_838, '#skF_2'(A_836, B_837, C_838)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_838), u1_struct_0('#skF_1'(A_836, B_837, C_838))))) | ~m1_subset_1(E_839, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_837), u1_struct_0('#skF_1'(A_836, B_837, C_838))))) | ~v1_funct_2(E_839, u1_struct_0(B_837), u1_struct_0('#skF_1'(A_836, B_837, C_838))) | ~v1_funct_1(E_839) | ~l1_pre_topc('#skF_1'(A_836, B_837, C_838)) | ~v2_pre_topc('#skF_1'(A_836, B_837, C_838)) | v2_struct_0('#skF_1'(A_836, B_837, C_838)) | ~v1_funct_2(k3_tmap_1(A_836, '#skF_1'(A_836, B_837, C_838), k1_tsep_1(A_836, B_837, C_838), C_838, '#skF_2'(A_836, B_837, C_838)), u1_struct_0(C_838), u1_struct_0('#skF_1'(A_836, B_837, C_838))) | ~v1_funct_1(k3_tmap_1(A_836, '#skF_1'(A_836, B_837, C_838), k1_tsep_1(A_836, B_837, C_838), C_838, '#skF_2'(A_836, B_837, C_838))) | r3_tsep_1(A_836, B_837, C_838) | ~r1_tsep_1(B_837, C_838) | ~m1_pre_topc(C_838, A_836) | v2_struct_0(C_838) | ~m1_pre_topc(B_837, A_836) | v2_struct_0(B_837) | ~l1_pre_topc(A_836) | ~v2_pre_topc(A_836) | v2_struct_0(A_836))), inference(resolution, [status(thm)], [c_318, c_505])).
% 11.89/4.27  tff(c_1513, plain, (![A_970, B_971, C_972]: (k10_tmap_1(A_970, '#skF_1'(A_970, B_971, C_972), B_971, C_972, k3_tmap_1(A_970, '#skF_1'(A_970, B_971, C_972), k1_tsep_1(A_970, B_971, C_972), B_971, '#skF_2'(A_970, B_971, C_972)), k3_tmap_1(A_970, '#skF_1'(A_970, B_971, C_972), k1_tsep_1(A_970, B_971, C_972), C_972, '#skF_2'(A_970, B_971, C_972)))='#skF_2'(A_970, B_971, C_972) | ~m1_subset_1('#skF_2'(A_970, B_971, C_972), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_970, B_971, C_972)), u1_struct_0('#skF_1'(A_970, B_971, C_972))))) | ~v1_funct_2('#skF_2'(A_970, B_971, C_972), u1_struct_0(k1_tsep_1(A_970, B_971, C_972)), u1_struct_0('#skF_1'(A_970, B_971, C_972))) | ~v1_funct_1('#skF_2'(A_970, B_971, C_972)) | ~m1_subset_1(k3_tmap_1(A_970, '#skF_1'(A_970, B_971, C_972), k1_tsep_1(A_970, B_971, C_972), C_972, '#skF_2'(A_970, B_971, C_972)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_972), u1_struct_0('#skF_1'(A_970, B_971, C_972))))) | ~m1_subset_1(k3_tmap_1(A_970, '#skF_1'(A_970, B_971, C_972), k1_tsep_1(A_970, B_971, C_972), B_971, '#skF_2'(A_970, B_971, C_972)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_971), u1_struct_0('#skF_1'(A_970, B_971, C_972))))) | ~l1_pre_topc('#skF_1'(A_970, B_971, C_972)) | ~v2_pre_topc('#skF_1'(A_970, B_971, C_972)) | v2_struct_0('#skF_1'(A_970, B_971, C_972)) | ~v1_funct_2(k3_tmap_1(A_970, '#skF_1'(A_970, B_971, C_972), k1_tsep_1(A_970, B_971, C_972), C_972, '#skF_2'(A_970, B_971, C_972)), u1_struct_0(C_972), u1_struct_0('#skF_1'(A_970, B_971, C_972))) | ~v1_funct_1(k3_tmap_1(A_970, '#skF_1'(A_970, B_971, C_972), k1_tsep_1(A_970, B_971, C_972), C_972, '#skF_2'(A_970, B_971, C_972))) | ~v1_funct_2(k3_tmap_1(A_970, '#skF_1'(A_970, B_971, C_972), k1_tsep_1(A_970, B_971, C_972), B_971, '#skF_2'(A_970, B_971, C_972)), u1_struct_0(B_971), u1_struct_0('#skF_1'(A_970, B_971, C_972))) | ~v1_funct_1(k3_tmap_1(A_970, '#skF_1'(A_970, B_971, C_972), k1_tsep_1(A_970, B_971, C_972), B_971, '#skF_2'(A_970, B_971, C_972))) | r3_tsep_1(A_970, B_971, C_972) | ~r1_tsep_1(B_971, C_972) | ~m1_pre_topc(C_972, A_970) | v2_struct_0(C_972) | ~m1_pre_topc(B_971, A_970) | v2_struct_0(B_971) | ~l1_pre_topc(A_970) | ~v2_pre_topc(A_970) | v2_struct_0(A_970))), inference(resolution, [status(thm)], [c_308, c_1093])).
% 11.89/4.27  tff(c_1521, plain, (![A_973, B_974, C_975]: (k10_tmap_1(A_973, '#skF_1'(A_973, B_974, C_975), B_974, C_975, k3_tmap_1(A_973, '#skF_1'(A_973, B_974, C_975), k1_tsep_1(A_973, B_974, C_975), B_974, '#skF_2'(A_973, B_974, C_975)), k3_tmap_1(A_973, '#skF_1'(A_973, B_974, C_975), k1_tsep_1(A_973, B_974, C_975), C_975, '#skF_2'(A_973, B_974, C_975)))='#skF_2'(A_973, B_974, C_975) | ~m1_subset_1('#skF_2'(A_973, B_974, C_975), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_973, B_974, C_975)), u1_struct_0('#skF_1'(A_973, B_974, C_975))))) | ~v1_funct_2('#skF_2'(A_973, B_974, C_975), u1_struct_0(k1_tsep_1(A_973, B_974, C_975)), u1_struct_0('#skF_1'(A_973, B_974, C_975))) | ~v1_funct_1('#skF_2'(A_973, B_974, C_975)) | ~m1_subset_1(k3_tmap_1(A_973, '#skF_1'(A_973, B_974, C_975), k1_tsep_1(A_973, B_974, C_975), B_974, '#skF_2'(A_973, B_974, C_975)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_974), u1_struct_0('#skF_1'(A_973, B_974, C_975))))) | ~l1_pre_topc('#skF_1'(A_973, B_974, C_975)) | ~v2_pre_topc('#skF_1'(A_973, B_974, C_975)) | v2_struct_0('#skF_1'(A_973, B_974, C_975)) | ~v1_funct_2(k3_tmap_1(A_973, '#skF_1'(A_973, B_974, C_975), k1_tsep_1(A_973, B_974, C_975), C_975, '#skF_2'(A_973, B_974, C_975)), u1_struct_0(C_975), u1_struct_0('#skF_1'(A_973, B_974, C_975))) | ~v1_funct_1(k3_tmap_1(A_973, '#skF_1'(A_973, B_974, C_975), k1_tsep_1(A_973, B_974, C_975), C_975, '#skF_2'(A_973, B_974, C_975))) | ~v1_funct_2(k3_tmap_1(A_973, '#skF_1'(A_973, B_974, C_975), k1_tsep_1(A_973, B_974, C_975), B_974, '#skF_2'(A_973, B_974, C_975)), u1_struct_0(B_974), u1_struct_0('#skF_1'(A_973, B_974, C_975))) | ~v1_funct_1(k3_tmap_1(A_973, '#skF_1'(A_973, B_974, C_975), k1_tsep_1(A_973, B_974, C_975), B_974, '#skF_2'(A_973, B_974, C_975))) | r3_tsep_1(A_973, B_974, C_975) | ~r1_tsep_1(B_974, C_975) | ~m1_pre_topc(C_975, A_973) | v2_struct_0(C_975) | ~m1_pre_topc(B_974, A_973) | v2_struct_0(B_974) | ~l1_pre_topc(A_973) | ~v2_pre_topc(A_973) | v2_struct_0(A_973))), inference(resolution, [status(thm)], [c_26, c_1513])).
% 11.89/4.27  tff(c_1529, plain, (![A_976, B_977, C_978]: (k10_tmap_1(A_976, '#skF_1'(A_976, B_977, C_978), B_977, C_978, k3_tmap_1(A_976, '#skF_1'(A_976, B_977, C_978), k1_tsep_1(A_976, B_977, C_978), B_977, '#skF_2'(A_976, B_977, C_978)), k3_tmap_1(A_976, '#skF_1'(A_976, B_977, C_978), k1_tsep_1(A_976, B_977, C_978), C_978, '#skF_2'(A_976, B_977, C_978)))='#skF_2'(A_976, B_977, C_978) | ~m1_subset_1('#skF_2'(A_976, B_977, C_978), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_976, B_977, C_978)), u1_struct_0('#skF_1'(A_976, B_977, C_978))))) | ~v1_funct_2('#skF_2'(A_976, B_977, C_978), u1_struct_0(k1_tsep_1(A_976, B_977, C_978)), u1_struct_0('#skF_1'(A_976, B_977, C_978))) | ~v1_funct_1('#skF_2'(A_976, B_977, C_978)) | ~l1_pre_topc('#skF_1'(A_976, B_977, C_978)) | ~v2_pre_topc('#skF_1'(A_976, B_977, C_978)) | v2_struct_0('#skF_1'(A_976, B_977, C_978)) | ~v1_funct_2(k3_tmap_1(A_976, '#skF_1'(A_976, B_977, C_978), k1_tsep_1(A_976, B_977, C_978), C_978, '#skF_2'(A_976, B_977, C_978)), u1_struct_0(C_978), u1_struct_0('#skF_1'(A_976, B_977, C_978))) | ~v1_funct_1(k3_tmap_1(A_976, '#skF_1'(A_976, B_977, C_978), k1_tsep_1(A_976, B_977, C_978), C_978, '#skF_2'(A_976, B_977, C_978))) | ~v1_funct_2(k3_tmap_1(A_976, '#skF_1'(A_976, B_977, C_978), k1_tsep_1(A_976, B_977, C_978), B_977, '#skF_2'(A_976, B_977, C_978)), u1_struct_0(B_977), u1_struct_0('#skF_1'(A_976, B_977, C_978))) | ~v1_funct_1(k3_tmap_1(A_976, '#skF_1'(A_976, B_977, C_978), k1_tsep_1(A_976, B_977, C_978), B_977, '#skF_2'(A_976, B_977, C_978))) | r3_tsep_1(A_976, B_977, C_978) | ~r1_tsep_1(B_977, C_978) | ~m1_pre_topc(C_978, A_976) | v2_struct_0(C_978) | ~m1_pre_topc(B_977, A_976) | v2_struct_0(B_977) | ~l1_pre_topc(A_976) | ~v2_pre_topc(A_976) | v2_struct_0(A_976))), inference(resolution, [status(thm)], [c_34, c_1521])).
% 11.89/4.27  tff(c_144, plain, (![D_367, E_371, F_373]: (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v5_pre_topc(k10_tmap_1('#skF_3', D_367, '#skF_4', '#skF_5', E_371, F_373), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), D_367) | ~m1_subset_1(F_373, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(D_367)))) | ~v5_pre_topc(F_373, '#skF_5', D_367) | ~v1_funct_2(F_373, u1_struct_0('#skF_5'), u1_struct_0(D_367)) | ~v1_funct_1(F_373) | ~m1_subset_1(E_371, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(D_367)))) | ~v5_pre_topc(E_371, '#skF_4', D_367) | ~v1_funct_2(E_371, u1_struct_0('#skF_4'), u1_struct_0(D_367)) | ~v1_funct_1(E_371) | ~l1_pre_topc(D_367) | ~v2_pre_topc(D_367) | v2_struct_0(D_367))), inference(cnfTransformation, [status(thm)], [f_343])).
% 11.89/4.27  tff(c_353, plain, (![D_444, E_445, F_446]: (v5_pre_topc(k10_tmap_1('#skF_3', D_444, '#skF_4', '#skF_5', E_445, F_446), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), D_444) | ~m1_subset_1(F_446, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(D_444)))) | ~v5_pre_topc(F_446, '#skF_5', D_444) | ~v1_funct_2(F_446, u1_struct_0('#skF_5'), u1_struct_0(D_444)) | ~v1_funct_1(F_446) | ~m1_subset_1(E_445, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(D_444)))) | ~v5_pre_topc(E_445, '#skF_4', D_444) | ~v1_funct_2(E_445, u1_struct_0('#skF_4'), u1_struct_0(D_444)) | ~v1_funct_1(E_445) | ~l1_pre_topc(D_444) | ~v2_pre_topc(D_444) | v2_struct_0(D_444))), inference(negUnitSimplification, [status(thm)], [c_250, c_144])).
% 11.89/4.27  tff(c_356, plain, (![A_138, B_166, E_445]: (v5_pre_topc(k10_tmap_1('#skF_3', '#skF_1'(A_138, B_166, '#skF_5'), '#skF_4', '#skF_5', E_445, k3_tmap_1(A_138, '#skF_1'(A_138, B_166, '#skF_5'), k1_tsep_1(A_138, B_166, '#skF_5'), '#skF_5', '#skF_2'(A_138, B_166, '#skF_5'))), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_1'(A_138, B_166, '#skF_5')) | ~v5_pre_topc(k3_tmap_1(A_138, '#skF_1'(A_138, B_166, '#skF_5'), k1_tsep_1(A_138, B_166, '#skF_5'), '#skF_5', '#skF_2'(A_138, B_166, '#skF_5')), '#skF_5', '#skF_1'(A_138, B_166, '#skF_5')) | ~v1_funct_2(k3_tmap_1(A_138, '#skF_1'(A_138, B_166, '#skF_5'), k1_tsep_1(A_138, B_166, '#skF_5'), '#skF_5', '#skF_2'(A_138, B_166, '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'(A_138, B_166, '#skF_5'))) | ~v1_funct_1(k3_tmap_1(A_138, '#skF_1'(A_138, B_166, '#skF_5'), k1_tsep_1(A_138, B_166, '#skF_5'), '#skF_5', '#skF_2'(A_138, B_166, '#skF_5'))) | ~m1_subset_1(E_445, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'(A_138, B_166, '#skF_5'))))) | ~v5_pre_topc(E_445, '#skF_4', '#skF_1'(A_138, B_166, '#skF_5')) | ~v1_funct_2(E_445, u1_struct_0('#skF_4'), u1_struct_0('#skF_1'(A_138, B_166, '#skF_5'))) | ~v1_funct_1(E_445) | ~l1_pre_topc('#skF_1'(A_138, B_166, '#skF_5')) | ~v2_pre_topc('#skF_1'(A_138, B_166, '#skF_5')) | v2_struct_0('#skF_1'(A_138, B_166, '#skF_5')) | r3_tsep_1(A_138, B_166, '#skF_5') | ~r1_tsep_1(B_166, '#skF_5') | ~m1_pre_topc('#skF_5', A_138) | v2_struct_0('#skF_5') | ~m1_pre_topc(B_166, A_138) | v2_struct_0(B_166) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(resolution, [status(thm)], [c_26, c_353])).
% 11.89/4.27  tff(c_362, plain, (![A_138, B_166, E_445]: (v5_pre_topc(k10_tmap_1('#skF_3', '#skF_1'(A_138, B_166, '#skF_5'), '#skF_4', '#skF_5', E_445, k3_tmap_1(A_138, '#skF_1'(A_138, B_166, '#skF_5'), k1_tsep_1(A_138, B_166, '#skF_5'), '#skF_5', '#skF_2'(A_138, B_166, '#skF_5'))), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_1'(A_138, B_166, '#skF_5')) | ~v5_pre_topc(k3_tmap_1(A_138, '#skF_1'(A_138, B_166, '#skF_5'), k1_tsep_1(A_138, B_166, '#skF_5'), '#skF_5', '#skF_2'(A_138, B_166, '#skF_5')), '#skF_5', '#skF_1'(A_138, B_166, '#skF_5')) | ~v1_funct_2(k3_tmap_1(A_138, '#skF_1'(A_138, B_166, '#skF_5'), k1_tsep_1(A_138, B_166, '#skF_5'), '#skF_5', '#skF_2'(A_138, B_166, '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'(A_138, B_166, '#skF_5'))) | ~v1_funct_1(k3_tmap_1(A_138, '#skF_1'(A_138, B_166, '#skF_5'), k1_tsep_1(A_138, B_166, '#skF_5'), '#skF_5', '#skF_2'(A_138, B_166, '#skF_5'))) | ~m1_subset_1(E_445, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'(A_138, B_166, '#skF_5'))))) | ~v5_pre_topc(E_445, '#skF_4', '#skF_1'(A_138, B_166, '#skF_5')) | ~v1_funct_2(E_445, u1_struct_0('#skF_4'), u1_struct_0('#skF_1'(A_138, B_166, '#skF_5'))) | ~v1_funct_1(E_445) | ~l1_pre_topc('#skF_1'(A_138, B_166, '#skF_5')) | ~v2_pre_topc('#skF_1'(A_138, B_166, '#skF_5')) | v2_struct_0('#skF_1'(A_138, B_166, '#skF_5')) | r3_tsep_1(A_138, B_166, '#skF_5') | ~r1_tsep_1(B_166, '#skF_5') | ~m1_pre_topc('#skF_5', A_138) | ~m1_pre_topc(B_166, A_138) | v2_struct_0(B_166) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(negUnitSimplification, [status(thm)], [c_80, c_356])).
% 11.89/4.27  tff(c_1583, plain, (v5_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1529, c_362])).
% 11.89/4.27  tff(c_1669, plain, (v5_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_82, c_78, c_247, c_88, c_86, c_82, c_78, c_247, c_1583])).
% 11.89/4.27  tff(c_1670, plain, (v5_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_80, c_250, c_1669])).
% 11.89/4.27  tff(c_1700, plain, (~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_1670])).
% 11.89/4.27  tff(c_1704, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_40, c_1700])).
% 11.89/4.27  tff(c_1707, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_82, c_78, c_247, c_1704])).
% 11.89/4.27  tff(c_1709, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_80, c_250, c_1707])).
% 11.89/4.27  tff(c_1711, plain, (v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_1670])).
% 11.89/4.27  tff(c_38, plain, (![A_138, B_166, C_180]: (v1_funct_2(k3_tmap_1(A_138, '#skF_1'(A_138, B_166, C_180), k1_tsep_1(A_138, B_166, C_180), B_166, '#skF_2'(A_138, B_166, C_180)), u1_struct_0(B_166), u1_struct_0('#skF_1'(A_138, B_166, C_180))) | r3_tsep_1(A_138, B_166, C_180) | ~r1_tsep_1(B_166, C_180) | ~m1_pre_topc(C_180, A_138) | v2_struct_0(C_180) | ~m1_pre_topc(B_166, A_138) | v2_struct_0(B_166) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_203])).
% 11.89/4.27  tff(c_28, plain, (![A_138, B_166, C_180]: (v5_pre_topc(k3_tmap_1(A_138, '#skF_1'(A_138, B_166, C_180), k1_tsep_1(A_138, B_166, C_180), C_180, '#skF_2'(A_138, B_166, C_180)), C_180, '#skF_1'(A_138, B_166, C_180)) | r3_tsep_1(A_138, B_166, C_180) | ~r1_tsep_1(B_166, C_180) | ~m1_pre_topc(C_180, A_138) | v2_struct_0(C_180) | ~m1_pre_topc(B_166, A_138) | v2_struct_0(B_166) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_203])).
% 11.89/4.27  tff(c_1710, plain, (~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v5_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_1670])).
% 11.89/4.27  tff(c_1712, plain, (~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_1710])).
% 11.89/4.27  tff(c_1715, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_28, c_1712])).
% 11.89/4.27  tff(c_1718, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_82, c_78, c_247, c_1715])).
% 11.89/4.27  tff(c_1720, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_80, c_250, c_1718])).
% 11.89/4.27  tff(c_1721, plain, (~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | v5_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_1710])).
% 11.89/4.27  tff(c_1734, plain, (~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_1721])).
% 11.89/4.27  tff(c_1737, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_1734])).
% 11.89/4.27  tff(c_1740, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_82, c_78, c_247, c_1737])).
% 11.89/4.27  tff(c_1742, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_80, c_250, c_1740])).
% 11.89/4.27  tff(c_1744, plain, (v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_1721])).
% 11.89/4.27  tff(c_32, plain, (![A_138, B_166, C_180]: (v1_funct_1(k3_tmap_1(A_138, '#skF_1'(A_138, B_166, C_180), k1_tsep_1(A_138, B_166, C_180), C_180, '#skF_2'(A_138, B_166, C_180))) | r3_tsep_1(A_138, B_166, C_180) | ~r1_tsep_1(B_166, C_180) | ~m1_pre_topc(C_180, A_138) | v2_struct_0(C_180) | ~m1_pre_topc(B_166, A_138) | v2_struct_0(B_166) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_203])).
% 11.89/4.27  tff(c_1722, plain, (v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_1710])).
% 11.89/4.27  tff(c_118, plain, (![D_367, E_371, F_373]: (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | m1_subset_1(k10_tmap_1('#skF_3', D_367, '#skF_4', '#skF_5', E_371, F_373), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0(D_367)))) | ~m1_subset_1(F_373, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(D_367)))) | ~v5_pre_topc(F_373, '#skF_5', D_367) | ~v1_funct_2(F_373, u1_struct_0('#skF_5'), u1_struct_0(D_367)) | ~v1_funct_1(F_373) | ~m1_subset_1(E_371, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(D_367)))) | ~v5_pre_topc(E_371, '#skF_4', D_367) | ~v1_funct_2(E_371, u1_struct_0('#skF_4'), u1_struct_0(D_367)) | ~v1_funct_1(E_371) | ~l1_pre_topc(D_367) | ~v2_pre_topc(D_367) | v2_struct_0(D_367))), inference(cnfTransformation, [status(thm)], [f_343])).
% 11.89/4.27  tff(c_397, plain, (![D_450, E_451, F_452]: (m1_subset_1(k10_tmap_1('#skF_3', D_450, '#skF_4', '#skF_5', E_451, F_452), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0(D_450)))) | ~m1_subset_1(F_452, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(D_450)))) | ~v5_pre_topc(F_452, '#skF_5', D_450) | ~v1_funct_2(F_452, u1_struct_0('#skF_5'), u1_struct_0(D_450)) | ~v1_funct_1(F_452) | ~m1_subset_1(E_451, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(D_450)))) | ~v5_pre_topc(E_451, '#skF_4', D_450) | ~v1_funct_2(E_451, u1_struct_0('#skF_4'), u1_struct_0(D_450)) | ~v1_funct_1(E_451) | ~l1_pre_topc(D_450) | ~v2_pre_topc(D_450) | v2_struct_0(D_450))), inference(negUnitSimplification, [status(thm)], [c_250, c_118])).
% 11.89/4.27  tff(c_403, plain, (![D_450, E_451, F_452]: (r2_funct_2(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0(D_450), k10_tmap_1('#skF_3', D_450, '#skF_4', '#skF_5', E_451, F_452), k10_tmap_1('#skF_3', D_450, '#skF_4', '#skF_5', E_451, F_452)) | ~v1_funct_2(k10_tmap_1('#skF_3', D_450, '#skF_4', '#skF_5', E_451, F_452), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0(D_450)) | ~v1_funct_1(k10_tmap_1('#skF_3', D_450, '#skF_4', '#skF_5', E_451, F_452)) | ~m1_subset_1(F_452, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(D_450)))) | ~v5_pre_topc(F_452, '#skF_5', D_450) | ~v1_funct_2(F_452, u1_struct_0('#skF_5'), u1_struct_0(D_450)) | ~v1_funct_1(F_452) | ~m1_subset_1(E_451, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(D_450)))) | ~v5_pre_topc(E_451, '#skF_4', D_450) | ~v1_funct_2(E_451, u1_struct_0('#skF_4'), u1_struct_0(D_450)) | ~v1_funct_1(E_451) | ~l1_pre_topc(D_450) | ~v2_pre_topc(D_450) | v2_struct_0(D_450))), inference(resolution, [status(thm)], [c_397, c_2])).
% 11.89/4.27  tff(c_1642, plain, (r2_funct_2(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')), k10_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_5', k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))), '#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k10_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_5', k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k10_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_5', k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1529, c_403])).
% 11.89/4.27  tff(c_1690, plain, (r2_funct_2(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')), k10_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_5', k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))), '#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k10_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_5', k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k10_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_5', k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_82, c_78, c_247, c_1642])).
% 11.89/4.27  tff(c_1691, plain, (r2_funct_2(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')), k10_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_5', k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))), '#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k10_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_5', k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k10_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_5', k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_80, c_250, c_1690])).
% 11.89/4.27  tff(c_1746, plain, (r2_funct_2(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')), k10_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_5', k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))), '#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k10_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_5', k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k10_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_5', k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_1711, c_1744, c_1722, c_1691])).
% 11.89/4.27  tff(c_1747, plain, (~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_1746])).
% 11.89/4.27  tff(c_1750, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_1747])).
% 11.89/4.27  tff(c_1753, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_82, c_78, c_247, c_1750])).
% 11.89/4.27  tff(c_1755, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_80, c_250, c_1753])).
% 11.89/4.27  tff(c_1757, plain, (v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_1746])).
% 11.89/4.27  tff(c_1743, plain, (~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v5_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_1721])).
% 11.89/4.27  tff(c_1759, plain, (~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v5_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1757, c_1743])).
% 11.89/4.27  tff(c_1760, plain, (~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')))))), inference(splitLeft, [status(thm)], [c_1759])).
% 11.89/4.27  tff(c_1763, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_1760])).
% 11.89/4.27  tff(c_1766, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_82, c_78, c_247, c_1763])).
% 11.89/4.27  tff(c_1768, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_80, c_250, c_1766])).
% 11.89/4.27  tff(c_1770, plain, (m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')))))), inference(splitRight, [status(thm)], [c_1759])).
% 11.89/4.27  tff(c_22, plain, (![B_133, A_132, C_134, E_136, F_137, D_135]: (v1_funct_1(k10_tmap_1(A_132, B_133, C_134, D_135, E_136, F_137)) | ~m1_subset_1(F_137, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_135), u1_struct_0(B_133)))) | ~v1_funct_2(F_137, u1_struct_0(D_135), u1_struct_0(B_133)) | ~v1_funct_1(F_137) | ~m1_subset_1(E_136, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_134), u1_struct_0(B_133)))) | ~v1_funct_2(E_136, u1_struct_0(C_134), u1_struct_0(B_133)) | ~v1_funct_1(E_136) | ~m1_pre_topc(D_135, A_132) | v2_struct_0(D_135) | ~m1_pre_topc(C_134, A_132) | v2_struct_0(C_134) | ~l1_pre_topc(B_133) | ~v2_pre_topc(B_133) | v2_struct_0(B_133) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132) | v2_struct_0(A_132))), inference(cnfTransformation, [status(thm)], [f_141])).
% 11.89/4.27  tff(c_1786, plain, (![A_132, C_134, E_136]: (v1_funct_1(k10_tmap_1(A_132, '#skF_1'('#skF_3', '#skF_4', '#skF_5'), C_134, '#skF_4', E_136, k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(E_136, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_134), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2(E_136, u1_struct_0(C_134), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(E_136) | ~m1_pre_topc('#skF_4', A_132) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_134, A_132) | v2_struct_0(C_134) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132) | v2_struct_0(A_132))), inference(resolution, [status(thm)], [c_1770, c_22])).
% 11.89/4.27  tff(c_1822, plain, (![A_132, C_134, E_136]: (v1_funct_1(k10_tmap_1(A_132, '#skF_1'('#skF_3', '#skF_4', '#skF_5'), C_134, '#skF_4', E_136, k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))) | ~m1_subset_1(E_136, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_134), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2(E_136, u1_struct_0(C_134), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(E_136) | ~m1_pre_topc('#skF_4', A_132) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_134, A_132) | v2_struct_0(C_134) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132) | v2_struct_0(A_132))), inference(demodulation, [status(thm), theory('equality')], [c_1711, c_1744, c_1786])).
% 11.89/4.27  tff(c_1823, plain, (![A_132, C_134, E_136]: (v1_funct_1(k10_tmap_1(A_132, '#skF_1'('#skF_3', '#skF_4', '#skF_5'), C_134, '#skF_4', E_136, k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))) | ~m1_subset_1(E_136, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_134), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2(E_136, u1_struct_0(C_134), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(E_136) | ~m1_pre_topc('#skF_4', A_132) | ~m1_pre_topc(C_134, A_132) | v2_struct_0(C_134) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132) | v2_struct_0(A_132))), inference(negUnitSimplification, [status(thm)], [c_84, c_1822])).
% 11.89/4.27  tff(c_1850, plain, (~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_1823])).
% 11.89/4.27  tff(c_1853, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_1850])).
% 11.89/4.27  tff(c_1856, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_82, c_78, c_247, c_1853])).
% 11.89/4.27  tff(c_1858, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_80, c_250, c_1856])).
% 11.89/4.27  tff(c_1859, plain, (![A_132, C_134, E_136]: (~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v1_funct_1(k10_tmap_1(A_132, '#skF_1'('#skF_3', '#skF_4', '#skF_5'), C_134, '#skF_4', E_136, k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))) | ~m1_subset_1(E_136, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_134), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2(E_136, u1_struct_0(C_134), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(E_136) | ~m1_pre_topc('#skF_4', A_132) | ~m1_pre_topc(C_134, A_132) | v2_struct_0(C_134) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132) | v2_struct_0(A_132))), inference(splitRight, [status(thm)], [c_1823])).
% 11.89/4.27  tff(c_1873, plain, (~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_1859])).
% 11.89/4.27  tff(c_1876, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_1873])).
% 11.89/4.27  tff(c_1879, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_82, c_78, c_247, c_1876])).
% 11.89/4.27  tff(c_1881, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_80, c_250, c_1879])).
% 11.89/4.27  tff(c_1882, plain, (![A_132, C_134, E_136]: (v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v1_funct_1(k10_tmap_1(A_132, '#skF_1'('#skF_3', '#skF_4', '#skF_5'), C_134, '#skF_4', E_136, k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))) | ~m1_subset_1(E_136, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_134), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2(E_136, u1_struct_0(C_134), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(E_136) | ~m1_pre_topc('#skF_4', A_132) | ~m1_pre_topc(C_134, A_132) | v2_struct_0(C_134) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132) | v2_struct_0(A_132))), inference(splitRight, [status(thm)], [c_1859])).
% 11.89/4.27  tff(c_1884, plain, (v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_1882])).
% 11.89/4.27  tff(c_52, plain, (![A_138, B_166, C_180]: (~v2_struct_0('#skF_1'(A_138, B_166, C_180)) | r3_tsep_1(A_138, B_166, C_180) | ~r1_tsep_1(B_166, C_180) | ~m1_pre_topc(C_180, A_138) | v2_struct_0(C_180) | ~m1_pre_topc(B_166, A_138) | v2_struct_0(B_166) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_203])).
% 11.89/4.27  tff(c_1887, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1884, c_52])).
% 11.89/4.27  tff(c_1890, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_82, c_78, c_247, c_1887])).
% 11.89/4.27  tff(c_1892, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_80, c_250, c_1890])).
% 11.89/4.27  tff(c_1894, plain, (~v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_1882])).
% 11.89/4.27  tff(c_30, plain, (![A_138, B_166, C_180]: (v1_funct_2(k3_tmap_1(A_138, '#skF_1'(A_138, B_166, C_180), k1_tsep_1(A_138, B_166, C_180), C_180, '#skF_2'(A_138, B_166, C_180)), u1_struct_0(C_180), u1_struct_0('#skF_1'(A_138, B_166, C_180))) | r3_tsep_1(A_138, B_166, C_180) | ~r1_tsep_1(B_166, C_180) | ~m1_pre_topc(C_180, A_138) | v2_struct_0(C_180) | ~m1_pre_topc(B_166, A_138) | v2_struct_0(B_166) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_203])).
% 11.89/4.27  tff(c_1860, plain, (v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_1823])).
% 11.89/4.27  tff(c_1883, plain, (l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_1859])).
% 11.89/4.27  tff(c_1788, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_1770, c_2])).
% 11.89/4.27  tff(c_1826, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_1711, c_1744, c_1788])).
% 11.89/4.27  tff(c_512, plain, (![A_432, B_433, C_434, E_497]: (k10_tmap_1(A_432, '#skF_1'(A_432, B_433, C_434), B_433, C_434, E_497, k3_tmap_1(A_432, '#skF_1'(A_432, B_433, C_434), k1_tsep_1(A_432, B_433, C_434), C_434, '#skF_2'(A_432, B_433, C_434)))='#skF_2'(A_432, B_433, C_434) | ~r2_funct_2(u1_struct_0(B_433), u1_struct_0('#skF_1'(A_432, B_433, C_434)), k3_tmap_1(A_432, '#skF_1'(A_432, B_433, C_434), k1_tsep_1(A_432, B_433, C_434), B_433, '#skF_2'(A_432, B_433, C_434)), E_497) | ~m1_subset_1('#skF_2'(A_432, B_433, C_434), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_432, B_433, C_434)), u1_struct_0('#skF_1'(A_432, B_433, C_434))))) | ~v1_funct_2('#skF_2'(A_432, B_433, C_434), u1_struct_0(k1_tsep_1(A_432, B_433, C_434)), u1_struct_0('#skF_1'(A_432, B_433, C_434))) | ~v1_funct_1('#skF_2'(A_432, B_433, C_434)) | ~m1_subset_1(k3_tmap_1(A_432, '#skF_1'(A_432, B_433, C_434), k1_tsep_1(A_432, B_433, C_434), C_434, '#skF_2'(A_432, B_433, C_434)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_434), u1_struct_0('#skF_1'(A_432, B_433, C_434))))) | ~m1_subset_1(E_497, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_433), u1_struct_0('#skF_1'(A_432, B_433, C_434))))) | ~v1_funct_2(E_497, u1_struct_0(B_433), u1_struct_0('#skF_1'(A_432, B_433, C_434))) | ~v1_funct_1(E_497) | ~l1_pre_topc('#skF_1'(A_432, B_433, C_434)) | ~v2_pre_topc('#skF_1'(A_432, B_433, C_434)) | v2_struct_0('#skF_1'(A_432, B_433, C_434)) | ~v1_funct_2(k3_tmap_1(A_432, '#skF_1'(A_432, B_433, C_434), k1_tsep_1(A_432, B_433, C_434), C_434, '#skF_2'(A_432, B_433, C_434)), u1_struct_0(C_434), u1_struct_0('#skF_1'(A_432, B_433, C_434))) | ~v1_funct_1(k3_tmap_1(A_432, '#skF_1'(A_432, B_433, C_434), k1_tsep_1(A_432, B_433, C_434), C_434, '#skF_2'(A_432, B_433, C_434))) | r3_tsep_1(A_432, B_433, C_434) | ~r1_tsep_1(B_433, C_434) | ~m1_pre_topc(C_434, A_432) | v2_struct_0(C_434) | ~m1_pre_topc(B_433, A_432) | v2_struct_0(B_433) | ~l1_pre_topc(A_432) | ~v2_pre_topc(A_432) | v2_struct_0(A_432))), inference(resolution, [status(thm)], [c_318, c_505])).
% 11.89/4.27  tff(c_1839, plain, (k10_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_5', k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))='#skF_2'('#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1826, c_512])).
% 11.89/4.27  tff(c_1844, plain, (k10_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_5', k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))='#skF_2'('#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_82, c_78, c_247, c_1757, c_1711, c_1744, c_1770, c_1839])).
% 11.89/4.27  tff(c_1845, plain, (k10_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_5', k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))='#skF_2'('#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_80, c_250, c_1844])).
% 11.89/4.27  tff(c_1896, plain, (k10_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_5', k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))='#skF_2'('#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_1860, c_1883, c_1845])).
% 11.89/4.27  tff(c_1897, plain, (~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_1896])).
% 11.89/4.27  tff(c_1900, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_30, c_1897])).
% 11.89/4.27  tff(c_1903, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_82, c_78, c_247, c_1900])).
% 11.89/4.27  tff(c_1905, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_80, c_250, c_1903])).
% 11.89/4.27  tff(c_1907, plain, (v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_1896])).
% 11.89/4.27  tff(c_1769, plain, (~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | v5_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_1759])).
% 11.89/4.27  tff(c_1942, plain, (~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | v5_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1907, c_1860, c_1883, c_1769])).
% 11.89/4.27  tff(c_1943, plain, (~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | v5_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_1894, c_1942])).
% 11.89/4.27  tff(c_1944, plain, (~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_1943])).
% 11.89/4.27  tff(c_1947, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_46, c_1944])).
% 11.89/4.27  tff(c_1950, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_82, c_78, c_247, c_1947])).
% 11.89/4.27  tff(c_1952, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_80, c_250, c_1950])).
% 11.89/4.27  tff(c_1954, plain, (v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_1943])).
% 11.89/4.27  tff(c_42, plain, (![A_138, B_166, C_180]: (m1_subset_1('#skF_2'(A_138, B_166, C_180), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_138, B_166, C_180)), u1_struct_0('#skF_1'(A_138, B_166, C_180))))) | r3_tsep_1(A_138, B_166, C_180) | ~r1_tsep_1(B_166, C_180) | ~m1_pre_topc(C_180, A_138) | v2_struct_0(C_180) | ~m1_pre_topc(B_166, A_138) | v2_struct_0(B_166) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_203])).
% 11.89/4.27  tff(c_44, plain, (![A_138, B_166, C_180]: (v1_funct_2('#skF_2'(A_138, B_166, C_180), u1_struct_0(k1_tsep_1(A_138, B_166, C_180)), u1_struct_0('#skF_1'(A_138, B_166, C_180))) | r3_tsep_1(A_138, B_166, C_180) | ~r1_tsep_1(B_166, C_180) | ~m1_pre_topc(C_180, A_138) | v2_struct_0(C_180) | ~m1_pre_topc(B_166, A_138) | v2_struct_0(B_166) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_203])).
% 11.89/4.27  tff(c_36, plain, (![A_138, B_166, C_180]: (v5_pre_topc(k3_tmap_1(A_138, '#skF_1'(A_138, B_166, C_180), k1_tsep_1(A_138, B_166, C_180), B_166, '#skF_2'(A_138, B_166, C_180)), B_166, '#skF_1'(A_138, B_166, C_180)) | r3_tsep_1(A_138, B_166, C_180) | ~r1_tsep_1(B_166, C_180) | ~m1_pre_topc(C_180, A_138) | v2_struct_0(C_180) | ~m1_pre_topc(B_166, A_138) | v2_struct_0(B_166) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_203])).
% 11.89/4.27  tff(c_1953, plain, (~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v5_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_1943])).
% 11.89/4.27  tff(c_1955, plain, (~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_1953])).
% 11.89/4.27  tff(c_1958, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_1955])).
% 11.89/4.27  tff(c_1961, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_82, c_78, c_247, c_1958])).
% 11.89/4.27  tff(c_1963, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_80, c_250, c_1961])).
% 11.89/4.27  tff(c_1964, plain, (~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | v5_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_1953])).
% 11.89/4.27  tff(c_1966, plain, (~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_1964])).
% 11.89/4.27  tff(c_1969, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_1966])).
% 11.89/4.27  tff(c_1972, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_82, c_78, c_247, c_1969])).
% 11.89/4.27  tff(c_1974, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_80, c_250, c_1972])).
% 11.89/4.27  tff(c_1975, plain, (~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | v5_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_1964])).
% 11.89/4.27  tff(c_1988, plain, (~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')))))), inference(splitLeft, [status(thm)], [c_1975])).
% 11.89/4.27  tff(c_1991, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_1988])).
% 11.89/4.27  tff(c_1994, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_82, c_78, c_247, c_1991])).
% 11.89/4.27  tff(c_1996, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_80, c_250, c_1994])).
% 11.89/4.27  tff(c_1997, plain, (v5_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_1975])).
% 11.89/4.27  tff(c_450, plain, (![A_465, B_466, C_467]: (~m1_subset_1('#skF_2'(A_465, B_466, C_467), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_465, B_466, C_467)), u1_struct_0('#skF_1'(A_465, B_466, C_467))))) | ~v5_pre_topc('#skF_2'(A_465, B_466, C_467), k1_tsep_1(A_465, B_466, C_467), '#skF_1'(A_465, B_466, C_467)) | ~v1_funct_2('#skF_2'(A_465, B_466, C_467), u1_struct_0(k1_tsep_1(A_465, B_466, C_467)), u1_struct_0('#skF_1'(A_465, B_466, C_467))) | ~v1_funct_1('#skF_2'(A_465, B_466, C_467)) | r3_tsep_1(A_465, B_466, C_467) | ~r1_tsep_1(B_466, C_467) | ~m1_pre_topc(C_467, A_465) | v2_struct_0(C_467) | ~m1_pre_topc(B_466, A_465) | v2_struct_0(B_466) | ~l1_pre_topc(A_465) | ~v2_pre_topc(A_465) | v2_struct_0(A_465))), inference(cnfTransformation, [status(thm)], [f_203])).
% 11.89/4.27  tff(c_455, plain, (![A_468, B_469, C_470]: (~v5_pre_topc('#skF_2'(A_468, B_469, C_470), k1_tsep_1(A_468, B_469, C_470), '#skF_1'(A_468, B_469, C_470)) | ~v1_funct_2('#skF_2'(A_468, B_469, C_470), u1_struct_0(k1_tsep_1(A_468, B_469, C_470)), u1_struct_0('#skF_1'(A_468, B_469, C_470))) | ~v1_funct_1('#skF_2'(A_468, B_469, C_470)) | r3_tsep_1(A_468, B_469, C_470) | ~r1_tsep_1(B_469, C_470) | ~m1_pre_topc(C_470, A_468) | v2_struct_0(C_470) | ~m1_pre_topc(B_469, A_468) | v2_struct_0(B_469) | ~l1_pre_topc(A_468) | ~v2_pre_topc(A_468) | v2_struct_0(A_468))), inference(resolution, [status(thm)], [c_42, c_450])).
% 11.89/4.27  tff(c_459, plain, (![A_138, B_166, C_180]: (~v5_pre_topc('#skF_2'(A_138, B_166, C_180), k1_tsep_1(A_138, B_166, C_180), '#skF_1'(A_138, B_166, C_180)) | ~v1_funct_1('#skF_2'(A_138, B_166, C_180)) | r3_tsep_1(A_138, B_166, C_180) | ~r1_tsep_1(B_166, C_180) | ~m1_pre_topc(C_180, A_138) | v2_struct_0(C_180) | ~m1_pre_topc(B_166, A_138) | v2_struct_0(B_166) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(resolution, [status(thm)], [c_44, c_455])).
% 11.89/4.27  tff(c_2001, plain, (~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1997, c_459])).
% 11.89/4.27  tff(c_2004, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_82, c_78, c_247, c_1954, c_2001])).
% 11.89/4.27  tff(c_2006, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_80, c_250, c_2004])).
% 11.89/4.27  tff(c_2008, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_249])).
% 11.89/4.27  tff(c_74, plain, (![A_254, B_258, C_260]: (r4_tsep_1(A_254, B_258, C_260) | ~r3_tsep_1(A_254, B_258, C_260) | ~m1_pre_topc(C_260, A_254) | v2_struct_0(C_260) | ~m1_pre_topc(B_258, A_254) | v2_struct_0(B_258) | ~l1_pre_topc(A_254) | ~v2_pre_topc(A_254) | v2_struct_0(A_254))), inference(cnfTransformation, [status(thm)], [f_285])).
% 11.89/4.27  tff(c_110, plain, (v1_funct_1('#skF_7') | ~r1_tsep_1('#skF_4', '#skF_5') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_343])).
% 11.89/4.27  tff(c_2014, plain, (v1_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2008, c_247, c_110])).
% 11.89/4.27  tff(c_108, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_6')) | ~r1_tsep_1('#skF_4', '#skF_5') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_343])).
% 11.89/4.27  tff(c_2024, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2008, c_247, c_108])).
% 11.89/4.27  tff(c_106, plain, (v5_pre_topc('#skF_7', '#skF_4', '#skF_6') | ~r1_tsep_1('#skF_4', '#skF_5') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_343])).
% 11.89/4.27  tff(c_2020, plain, (v5_pre_topc('#skF_7', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2008, c_247, c_106])).
% 11.89/4.27  tff(c_104, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_6')))) | ~r1_tsep_1('#skF_4', '#skF_5') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_343])).
% 11.89/4.27  tff(c_2028, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_2008, c_247, c_104])).
% 11.89/4.27  tff(c_116, plain, (~v2_struct_0('#skF_6') | ~r1_tsep_1('#skF_4', '#skF_5') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_343])).
% 11.89/4.27  tff(c_2012, plain, (~v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2008, c_247, c_116])).
% 11.89/4.27  tff(c_114, plain, (v2_pre_topc('#skF_6') | ~r1_tsep_1('#skF_4', '#skF_5') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_343])).
% 11.89/4.27  tff(c_2010, plain, (v2_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2008, c_247, c_114])).
% 11.89/4.27  tff(c_2007, plain, (l1_pre_topc('#skF_6')), inference(splitRight, [status(thm)], [c_249])).
% 11.89/4.27  tff(c_102, plain, (v1_funct_1('#skF_8') | ~r1_tsep_1('#skF_4', '#skF_5') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_343])).
% 11.89/4.27  tff(c_2016, plain, (v1_funct_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2008, c_247, c_102])).
% 11.89/4.27  tff(c_100, plain, (v1_funct_2('#skF_8', u1_struct_0('#skF_5'), u1_struct_0('#skF_6')) | ~r1_tsep_1('#skF_4', '#skF_5') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_343])).
% 11.89/4.27  tff(c_2022, plain, (v1_funct_2('#skF_8', u1_struct_0('#skF_5'), u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2008, c_247, c_100])).
% 11.89/4.27  tff(c_98, plain, (v5_pre_topc('#skF_8', '#skF_5', '#skF_6') | ~r1_tsep_1('#skF_4', '#skF_5') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_343])).
% 11.89/4.27  tff(c_2018, plain, (v5_pre_topc('#skF_8', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2008, c_247, c_98])).
% 11.89/4.27  tff(c_96, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_6')))) | ~r1_tsep_1('#skF_4', '#skF_5') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_343])).
% 11.89/4.27  tff(c_2026, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_2008, c_247, c_96])).
% 11.89/4.27  tff(c_2674, plain, (![C_1167, D_1171, A_1168, E_1170, B_1172, F_1169]: (v5_pre_topc(k10_tmap_1(A_1168, B_1172, C_1167, D_1171, E_1170, F_1169), k1_tsep_1(A_1168, C_1167, D_1171), B_1172) | ~r4_tsep_1(A_1168, C_1167, D_1171) | ~m1_subset_1(F_1169, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_1171), u1_struct_0(B_1172)))) | ~v5_pre_topc(F_1169, D_1171, B_1172) | ~v1_funct_2(F_1169, u1_struct_0(D_1171), u1_struct_0(B_1172)) | ~v1_funct_1(F_1169) | ~m1_subset_1(E_1170, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1167), u1_struct_0(B_1172)))) | ~v5_pre_topc(E_1170, C_1167, B_1172) | ~v1_funct_2(E_1170, u1_struct_0(C_1167), u1_struct_0(B_1172)) | ~v1_funct_1(E_1170) | ~r1_tsep_1(C_1167, D_1171) | ~m1_pre_topc(D_1171, A_1168) | v2_struct_0(D_1171) | ~m1_pre_topc(C_1167, A_1168) | v2_struct_0(C_1167) | ~l1_pre_topc(B_1172) | ~v2_pre_topc(B_1172) | v2_struct_0(B_1172) | ~l1_pre_topc(A_1168) | ~v2_pre_topc(A_1168) | v2_struct_0(A_1168))), inference(cnfTransformation, [status(thm)], [f_260])).
% 11.89/4.27  tff(c_2688, plain, (![A_1168, C_1167, E_1170]: (v5_pre_topc(k10_tmap_1(A_1168, '#skF_6', C_1167, '#skF_5', E_1170, '#skF_8'), k1_tsep_1(A_1168, C_1167, '#skF_5'), '#skF_6') | ~r4_tsep_1(A_1168, C_1167, '#skF_5') | ~v5_pre_topc('#skF_8', '#skF_5', '#skF_6') | ~v1_funct_2('#skF_8', u1_struct_0('#skF_5'), u1_struct_0('#skF_6')) | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_1170, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1167), u1_struct_0('#skF_6')))) | ~v5_pre_topc(E_1170, C_1167, '#skF_6') | ~v1_funct_2(E_1170, u1_struct_0(C_1167), u1_struct_0('#skF_6')) | ~v1_funct_1(E_1170) | ~r1_tsep_1(C_1167, '#skF_5') | ~m1_pre_topc('#skF_5', A_1168) | v2_struct_0('#skF_5') | ~m1_pre_topc(C_1167, A_1168) | v2_struct_0(C_1167) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~l1_pre_topc(A_1168) | ~v2_pre_topc(A_1168) | v2_struct_0(A_1168))), inference(resolution, [status(thm)], [c_2026, c_2674])).
% 11.89/4.27  tff(c_2703, plain, (![A_1168, C_1167, E_1170]: (v5_pre_topc(k10_tmap_1(A_1168, '#skF_6', C_1167, '#skF_5', E_1170, '#skF_8'), k1_tsep_1(A_1168, C_1167, '#skF_5'), '#skF_6') | ~r4_tsep_1(A_1168, C_1167, '#skF_5') | ~m1_subset_1(E_1170, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1167), u1_struct_0('#skF_6')))) | ~v5_pre_topc(E_1170, C_1167, '#skF_6') | ~v1_funct_2(E_1170, u1_struct_0(C_1167), u1_struct_0('#skF_6')) | ~v1_funct_1(E_1170) | ~r1_tsep_1(C_1167, '#skF_5') | ~m1_pre_topc('#skF_5', A_1168) | v2_struct_0('#skF_5') | ~m1_pre_topc(C_1167, A_1168) | v2_struct_0(C_1167) | v2_struct_0('#skF_6') | ~l1_pre_topc(A_1168) | ~v2_pre_topc(A_1168) | v2_struct_0(A_1168))), inference(demodulation, [status(thm), theory('equality')], [c_2010, c_2007, c_2016, c_2022, c_2018, c_2688])).
% 11.89/4.27  tff(c_2736, plain, (![A_1176, C_1177, E_1178]: (v5_pre_topc(k10_tmap_1(A_1176, '#skF_6', C_1177, '#skF_5', E_1178, '#skF_8'), k1_tsep_1(A_1176, C_1177, '#skF_5'), '#skF_6') | ~r4_tsep_1(A_1176, C_1177, '#skF_5') | ~m1_subset_1(E_1178, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1177), u1_struct_0('#skF_6')))) | ~v5_pre_topc(E_1178, C_1177, '#skF_6') | ~v1_funct_2(E_1178, u1_struct_0(C_1177), u1_struct_0('#skF_6')) | ~v1_funct_1(E_1178) | ~r1_tsep_1(C_1177, '#skF_5') | ~m1_pre_topc('#skF_5', A_1176) | ~m1_pre_topc(C_1177, A_1176) | v2_struct_0(C_1177) | ~l1_pre_topc(A_1176) | ~v2_pre_topc(A_1176) | v2_struct_0(A_1176))), inference(negUnitSimplification, [status(thm)], [c_2012, c_80, c_2703])).
% 11.89/4.27  tff(c_2743, plain, (![A_1176]: (v5_pre_topc(k10_tmap_1(A_1176, '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8'), k1_tsep_1(A_1176, '#skF_4', '#skF_5'), '#skF_6') | ~r4_tsep_1(A_1176, '#skF_4', '#skF_5') | ~v5_pre_topc('#skF_7', '#skF_4', '#skF_6') | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_6')) | ~v1_funct_1('#skF_7') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', A_1176) | ~m1_pre_topc('#skF_4', A_1176) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_1176) | ~v2_pre_topc(A_1176) | v2_struct_0(A_1176))), inference(resolution, [status(thm)], [c_2028, c_2736])).
% 11.89/4.27  tff(c_2755, plain, (![A_1176]: (v5_pre_topc(k10_tmap_1(A_1176, '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8'), k1_tsep_1(A_1176, '#skF_4', '#skF_5'), '#skF_6') | ~r4_tsep_1(A_1176, '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', A_1176) | ~m1_pre_topc('#skF_4', A_1176) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_1176) | ~v2_pre_topc(A_1176) | v2_struct_0(A_1176))), inference(demodulation, [status(thm), theory('equality')], [c_247, c_2014, c_2024, c_2020, c_2743])).
% 11.89/4.27  tff(c_2761, plain, (![A_1179]: (v5_pre_topc(k10_tmap_1(A_1179, '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8'), k1_tsep_1(A_1179, '#skF_4', '#skF_5'), '#skF_6') | ~r4_tsep_1(A_1179, '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', A_1179) | ~m1_pre_topc('#skF_4', A_1179) | ~l1_pre_topc(A_1179) | ~v2_pre_topc(A_1179) | v2_struct_0(A_1179))), inference(negUnitSimplification, [status(thm)], [c_84, c_2755])).
% 11.89/4.27  tff(c_2466, plain, (![B_1123, A_1121, D_1126, F_1125, E_1124, C_1122]: (v1_funct_2(k10_tmap_1(A_1121, B_1123, C_1122, D_1126, E_1124, F_1125), u1_struct_0(k1_tsep_1(A_1121, C_1122, D_1126)), u1_struct_0(B_1123)) | ~m1_subset_1(F_1125, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_1126), u1_struct_0(B_1123)))) | ~v1_funct_2(F_1125, u1_struct_0(D_1126), u1_struct_0(B_1123)) | ~v1_funct_1(F_1125) | ~m1_subset_1(E_1124, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1122), u1_struct_0(B_1123)))) | ~v1_funct_2(E_1124, u1_struct_0(C_1122), u1_struct_0(B_1123)) | ~v1_funct_1(E_1124) | ~m1_pre_topc(D_1126, A_1121) | v2_struct_0(D_1126) | ~m1_pre_topc(C_1122, A_1121) | v2_struct_0(C_1122) | ~l1_pre_topc(B_1123) | ~v2_pre_topc(B_1123) | v2_struct_0(B_1123) | ~l1_pre_topc(A_1121) | ~v2_pre_topc(A_1121) | v2_struct_0(A_1121))), inference(cnfTransformation, [status(thm)], [f_141])).
% 11.89/4.27  tff(c_2300, plain, (![A_1096, D_1101, C_1097, F_1100, B_1098, E_1099]: (m1_subset_1(k10_tmap_1(A_1096, B_1098, C_1097, D_1101, E_1099, F_1100), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_1096, C_1097, D_1101)), u1_struct_0(B_1098)))) | ~m1_subset_1(F_1100, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_1101), u1_struct_0(B_1098)))) | ~v1_funct_2(F_1100, u1_struct_0(D_1101), u1_struct_0(B_1098)) | ~v1_funct_1(F_1100) | ~m1_subset_1(E_1099, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1097), u1_struct_0(B_1098)))) | ~v1_funct_2(E_1099, u1_struct_0(C_1097), u1_struct_0(B_1098)) | ~v1_funct_1(E_1099) | ~m1_pre_topc(D_1101, A_1096) | v2_struct_0(D_1101) | ~m1_pre_topc(C_1097, A_1096) | v2_struct_0(C_1097) | ~l1_pre_topc(B_1098) | ~v2_pre_topc(B_1098) | v2_struct_0(B_1098) | ~l1_pre_topc(A_1096) | ~v2_pre_topc(A_1096) | v2_struct_0(A_1096))), inference(cnfTransformation, [status(thm)], [f_141])).
% 11.89/4.27  tff(c_2108, plain, (![E_1058, D_1060, B_1057, C_1056, F_1059, A_1055]: (v1_funct_1(k10_tmap_1(A_1055, B_1057, C_1056, D_1060, E_1058, F_1059)) | ~m1_subset_1(F_1059, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_1060), u1_struct_0(B_1057)))) | ~v1_funct_2(F_1059, u1_struct_0(D_1060), u1_struct_0(B_1057)) | ~v1_funct_1(F_1059) | ~m1_subset_1(E_1058, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1056), u1_struct_0(B_1057)))) | ~v1_funct_2(E_1058, u1_struct_0(C_1056), u1_struct_0(B_1057)) | ~v1_funct_1(E_1058) | ~m1_pre_topc(D_1060, A_1055) | v2_struct_0(D_1060) | ~m1_pre_topc(C_1056, A_1055) | v2_struct_0(C_1056) | ~l1_pre_topc(B_1057) | ~v2_pre_topc(B_1057) | v2_struct_0(B_1057) | ~l1_pre_topc(A_1055) | ~v2_pre_topc(A_1055) | v2_struct_0(A_1055))), inference(cnfTransformation, [status(thm)], [f_141])).
% 11.89/4.27  tff(c_2118, plain, (![A_1055, C_1056, E_1058]: (v1_funct_1(k10_tmap_1(A_1055, '#skF_6', C_1056, '#skF_5', E_1058, '#skF_8')) | ~v1_funct_2('#skF_8', u1_struct_0('#skF_5'), u1_struct_0('#skF_6')) | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_1058, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1056), u1_struct_0('#skF_6')))) | ~v1_funct_2(E_1058, u1_struct_0(C_1056), u1_struct_0('#skF_6')) | ~v1_funct_1(E_1058) | ~m1_pre_topc('#skF_5', A_1055) | v2_struct_0('#skF_5') | ~m1_pre_topc(C_1056, A_1055) | v2_struct_0(C_1056) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~l1_pre_topc(A_1055) | ~v2_pre_topc(A_1055) | v2_struct_0(A_1055))), inference(resolution, [status(thm)], [c_2026, c_2108])).
% 11.89/4.27  tff(c_2128, plain, (![A_1055, C_1056, E_1058]: (v1_funct_1(k10_tmap_1(A_1055, '#skF_6', C_1056, '#skF_5', E_1058, '#skF_8')) | ~m1_subset_1(E_1058, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1056), u1_struct_0('#skF_6')))) | ~v1_funct_2(E_1058, u1_struct_0(C_1056), u1_struct_0('#skF_6')) | ~v1_funct_1(E_1058) | ~m1_pre_topc('#skF_5', A_1055) | v2_struct_0('#skF_5') | ~m1_pre_topc(C_1056, A_1055) | v2_struct_0(C_1056) | v2_struct_0('#skF_6') | ~l1_pre_topc(A_1055) | ~v2_pre_topc(A_1055) | v2_struct_0(A_1055))), inference(demodulation, [status(thm), theory('equality')], [c_2010, c_2007, c_2016, c_2022, c_2118])).
% 11.89/4.27  tff(c_2147, plain, (![A_1066, C_1067, E_1068]: (v1_funct_1(k10_tmap_1(A_1066, '#skF_6', C_1067, '#skF_5', E_1068, '#skF_8')) | ~m1_subset_1(E_1068, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_1067), u1_struct_0('#skF_6')))) | ~v1_funct_2(E_1068, u1_struct_0(C_1067), u1_struct_0('#skF_6')) | ~v1_funct_1(E_1068) | ~m1_pre_topc('#skF_5', A_1066) | ~m1_pre_topc(C_1067, A_1066) | v2_struct_0(C_1067) | ~l1_pre_topc(A_1066) | ~v2_pre_topc(A_1066) | v2_struct_0(A_1066))), inference(negUnitSimplification, [status(thm)], [c_2012, c_80, c_2128])).
% 11.89/4.27  tff(c_2149, plain, (![A_1066]: (v1_funct_1(k10_tmap_1(A_1066, '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8')) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_6')) | ~v1_funct_1('#skF_7') | ~m1_pre_topc('#skF_5', A_1066) | ~m1_pre_topc('#skF_4', A_1066) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_1066) | ~v2_pre_topc(A_1066) | v2_struct_0(A_1066))), inference(resolution, [status(thm)], [c_2028, c_2147])).
% 11.89/4.27  tff(c_2154, plain, (![A_1066]: (v1_funct_1(k10_tmap_1(A_1066, '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8')) | ~m1_pre_topc('#skF_5', A_1066) | ~m1_pre_topc('#skF_4', A_1066) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_1066) | ~v2_pre_topc(A_1066) | v2_struct_0(A_1066))), inference(demodulation, [status(thm), theory('equality')], [c_2014, c_2024, c_2149])).
% 11.89/4.27  tff(c_2161, plain, (![A_1070]: (v1_funct_1(k10_tmap_1(A_1070, '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8')) | ~m1_pre_topc('#skF_5', A_1070) | ~m1_pre_topc('#skF_4', A_1070) | ~l1_pre_topc(A_1070) | ~v2_pre_topc(A_1070) | v2_struct_0(A_1070))), inference(negUnitSimplification, [status(thm)], [c_84, c_2154])).
% 11.89/4.27  tff(c_94, plain, (~m1_subset_1(k10_tmap_1('#skF_3', '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_6')))) | ~v5_pre_topc(k10_tmap_1('#skF_3', '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_6') | ~v1_funct_2(k10_tmap_1('#skF_3', '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_6')) | ~v1_funct_1(k10_tmap_1('#skF_3', '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8')) | ~r1_tsep_1('#skF_4', '#skF_5') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_343])).
% 11.89/4.27  tff(c_2102, plain, (~m1_subset_1(k10_tmap_1('#skF_3', '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_6')))) | ~v5_pre_topc(k10_tmap_1('#skF_3', '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_6') | ~v1_funct_2(k10_tmap_1('#skF_3', '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_6')) | ~v1_funct_1(k10_tmap_1('#skF_3', '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2008, c_247, c_94])).
% 11.89/4.27  tff(c_2103, plain, (~v1_funct_1(k10_tmap_1('#skF_3', '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8'))), inference(splitLeft, [status(thm)], [c_2102])).
% 11.89/4.27  tff(c_2164, plain, (~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_2161, c_2103])).
% 11.89/4.27  tff(c_2167, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_82, c_78, c_2164])).
% 11.89/4.27  tff(c_2169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_2167])).
% 11.89/4.27  tff(c_2170, plain, (~v1_funct_2(k10_tmap_1('#skF_3', '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_6')) | ~v5_pre_topc(k10_tmap_1('#skF_3', '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_6') | ~m1_subset_1(k10_tmap_1('#skF_3', '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_6'))))), inference(splitRight, [status(thm)], [c_2102])).
% 11.89/4.27  tff(c_2172, plain, (~m1_subset_1(k10_tmap_1('#skF_3', '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_6'))))), inference(splitLeft, [status(thm)], [c_2170])).
% 11.89/4.27  tff(c_2311, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_6')))) | ~v1_funct_2('#skF_8', u1_struct_0('#skF_5'), u1_struct_0('#skF_6')) | ~v1_funct_1('#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_6')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_6')) | ~v1_funct_1('#skF_7') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_2300, c_2172])).
% 11.89/4.27  tff(c_2325, plain, (v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_6') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_2010, c_2007, c_82, c_78, c_2014, c_2024, c_2028, c_2016, c_2022, c_2026, c_2311])).
% 11.89/4.27  tff(c_2327, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_2012, c_84, c_80, c_2325])).
% 11.89/4.27  tff(c_2328, plain, (~v5_pre_topc(k10_tmap_1('#skF_3', '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_6') | ~v1_funct_2(k10_tmap_1('#skF_3', '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_2170])).
% 11.89/4.27  tff(c_2335, plain, (~v1_funct_2(k10_tmap_1('#skF_3', '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_2328])).
% 11.89/4.27  tff(c_2469, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_6')))) | ~v1_funct_2('#skF_8', u1_struct_0('#skF_5'), u1_struct_0('#skF_6')) | ~v1_funct_1('#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_6')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_6')) | ~v1_funct_1('#skF_7') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_2466, c_2335])).
% 11.89/4.27  tff(c_2472, plain, (v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_6') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_2010, c_2007, c_82, c_78, c_2014, c_2024, c_2028, c_2016, c_2022, c_2026, c_2469])).
% 11.89/4.27  tff(c_2474, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_2012, c_84, c_80, c_2472])).
% 11.89/4.27  tff(c_2475, plain, (~v5_pre_topc(k10_tmap_1('#skF_3', '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_2328])).
% 11.89/4.27  tff(c_2764, plain, (~r4_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_2761, c_2475])).
% 11.89/4.27  tff(c_2767, plain, (~r4_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_82, c_78, c_2764])).
% 11.89/4.27  tff(c_2768, plain, (~r4_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_90, c_2767])).
% 11.89/4.27  tff(c_2771, plain, (~r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_74, c_2768])).
% 11.89/4.27  tff(c_2774, plain, (v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_82, c_78, c_2008, c_2771])).
% 11.89/4.27  tff(c_2776, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_80, c_2774])).
% 11.89/4.27  tff(c_2778, plain, (~r1_tsep_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_222])).
% 11.89/4.27  tff(c_2777, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_222])).
% 11.89/4.27  tff(c_2806, plain, (![B_1183, C_1184, A_1185]: (r1_tsep_1(B_1183, C_1184) | ~r3_tsep_1(A_1185, B_1183, C_1184) | ~m1_pre_topc(C_1184, A_1185) | v2_struct_0(C_1184) | ~m1_pre_topc(B_1183, A_1185) | v2_struct_0(B_1183) | ~l1_pre_topc(A_1185) | ~v2_pre_topc(A_1185) | v2_struct_0(A_1185))), inference(cnfTransformation, [status(thm)], [f_285])).
% 11.89/4.27  tff(c_2809, plain, (r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_2777, c_2806])).
% 11.89/4.27  tff(c_2812, plain, (r1_tsep_1('#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_82, c_78, c_2809])).
% 11.89/4.27  tff(c_2814, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_80, c_2778, c_2812])).
% 11.89/4.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.89/4.27  
% 11.89/4.27  Inference rules
% 11.89/4.27  ----------------------
% 11.89/4.27  #Ref     : 0
% 11.89/4.27  #Sup     : 448
% 11.89/4.27  #Fact    : 0
% 11.89/4.27  #Define  : 0
% 11.89/4.27  #Split   : 27
% 11.89/4.27  #Chain   : 0
% 11.89/4.27  #Close   : 0
% 11.89/4.27  
% 11.89/4.27  Ordering : KBO
% 11.89/4.27  
% 11.89/4.27  Simplification rules
% 11.89/4.27  ----------------------
% 11.89/4.27  #Subsume      : 213
% 11.89/4.27  #Demod        : 806
% 11.89/4.27  #Tautology    : 208
% 11.89/4.27  #SimpNegUnit  : 109
% 11.89/4.27  #BackRed      : 0
% 11.89/4.27  
% 11.89/4.27  #Partial instantiations: 0
% 11.89/4.27  #Strategies tried      : 1
% 11.89/4.27  
% 11.89/4.27  Timing (in seconds)
% 11.89/4.27  ----------------------
% 11.89/4.28  Preprocessing        : 0.55
% 11.89/4.28  Parsing              : 0.25
% 11.89/4.28  CNF conversion       : 0.09
% 11.89/4.28  Main loop            : 2.84
% 11.89/4.28  Inferencing          : 0.66
% 11.89/4.28  Reduction            : 0.47
% 11.89/4.28  Demodulation         : 0.32
% 11.89/4.28  BG Simplification    : 0.11
% 11.89/4.28  Subsumption          : 1.53
% 11.89/4.28  Abstraction          : 0.11
% 11.89/4.28  MUC search           : 0.00
% 11.89/4.28  Cooper               : 0.00
% 11.89/4.28  Total                : 3.48
% 11.89/4.28  Index Insertion      : 0.00
% 11.89/4.28  Index Deletion       : 0.00
% 11.89/4.28  Index Matching       : 0.00
% 11.89/4.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
