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
% DateTime   : Thu Dec  3 10:28:12 EST 2020

% Result     : Theorem 7.69s
% Output     : CNFRefutation 8.10s
% Verified   : 
% Statistics : Number of formulae       :  285 (171335 expanded)
%              Number of leaves         :   36 (59666 expanded)
%              Depth                    :   44
%              Number of atoms          : 2016 (2233415 expanded)
%              Number of equality atoms :   29 (19271 expanded)
%              Maximal formula depth    :   39 (   9 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v5_pre_topc > v1_funct_2 > r4_tsep_1 > r3_tsep_1 > r1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_8 > #skF_4

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

tff(f_321,negated_conjecture,(
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

tff(f_145,axiom,(
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

tff(f_181,axiom,(
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

tff(f_238,axiom,(
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

tff(f_263,axiom,(
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

tff(c_80,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_321])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_321])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_321])).

tff(c_78,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_321])).

tff(c_76,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_321])).

tff(c_72,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_321])).

tff(c_68,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_321])).

tff(c_212,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | r1_tsep_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_321])).

tff(c_237,plain,(
    r1_tsep_1('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_212])).

tff(c_92,plain,
    ( v1_funct_1('#skF_8')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_321])).

tff(c_239,plain,
    ( v1_funct_1('#skF_8')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_92])).

tff(c_240,plain,(
    ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_239])).

tff(c_34,plain,(
    ! [A_11,B_39,C_53] :
      ( v1_funct_1('#skF_2'(A_11,B_39,C_53))
      | r3_tsep_1(A_11,B_39,C_53)
      | ~ r1_tsep_1(B_39,C_53)
      | ~ m1_pre_topc(C_53,A_11)
      | v2_struct_0(C_53)
      | ~ m1_pre_topc(B_39,A_11)
      | v2_struct_0(B_39)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_30,plain,(
    ! [A_11,B_39,C_53] :
      ( m1_subset_1('#skF_2'(A_11,B_39,C_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_11,B_39,C_53)),u1_struct_0('#skF_1'(A_11,B_39,C_53)))))
      | r3_tsep_1(A_11,B_39,C_53)
      | ~ r1_tsep_1(B_39,C_53)
      | ~ m1_pre_topc(C_53,A_11)
      | v2_struct_0(C_53)
      | ~ m1_pre_topc(B_39,A_11)
      | v2_struct_0(B_39)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_26,plain,(
    ! [A_11,B_39,C_53] :
      ( v1_funct_2(k3_tmap_1(A_11,'#skF_1'(A_11,B_39,C_53),k1_tsep_1(A_11,B_39,C_53),B_39,'#skF_2'(A_11,B_39,C_53)),u1_struct_0(B_39),u1_struct_0('#skF_1'(A_11,B_39,C_53)))
      | r3_tsep_1(A_11,B_39,C_53)
      | ~ r1_tsep_1(B_39,C_53)
      | ~ m1_pre_topc(C_53,A_11)
      | v2_struct_0(C_53)
      | ~ m1_pre_topc(B_39,A_11)
      | v2_struct_0(B_39)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_38,plain,(
    ! [A_11,B_39,C_53] :
      ( v2_pre_topc('#skF_1'(A_11,B_39,C_53))
      | r3_tsep_1(A_11,B_39,C_53)
      | ~ r1_tsep_1(B_39,C_53)
      | ~ m1_pre_topc(C_53,A_11)
      | v2_struct_0(C_53)
      | ~ m1_pre_topc(B_39,A_11)
      | v2_struct_0(B_39)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_18,plain,(
    ! [A_11,B_39,C_53] :
      ( v1_funct_2(k3_tmap_1(A_11,'#skF_1'(A_11,B_39,C_53),k1_tsep_1(A_11,B_39,C_53),C_53,'#skF_2'(A_11,B_39,C_53)),u1_struct_0(C_53),u1_struct_0('#skF_1'(A_11,B_39,C_53)))
      | r3_tsep_1(A_11,B_39,C_53)
      | ~ r1_tsep_1(B_39,C_53)
      | ~ m1_pre_topc(C_53,A_11)
      | v2_struct_0(C_53)
      | ~ m1_pre_topc(B_39,A_11)
      | v2_struct_0(B_39)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_299,plain,(
    ! [A_336,B_337,C_338] :
      ( m1_subset_1(k3_tmap_1(A_336,'#skF_1'(A_336,B_337,C_338),k1_tsep_1(A_336,B_337,C_338),C_338,'#skF_2'(A_336,B_337,C_338)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_338),u1_struct_0('#skF_1'(A_336,B_337,C_338)))))
      | r3_tsep_1(A_336,B_337,C_338)
      | ~ r1_tsep_1(B_337,C_338)
      | ~ m1_pre_topc(C_338,A_336)
      | v2_struct_0(C_338)
      | ~ m1_pre_topc(B_337,A_336)
      | v2_struct_0(B_337)
      | ~ l1_pre_topc(A_336)
      | ~ v2_pre_topc(A_336)
      | v2_struct_0(A_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_186,plain,(
    ! [D_271,E_275,F_277] :
      ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
      | v1_funct_1(k10_tmap_1('#skF_3',D_271,'#skF_4','#skF_5',E_275,F_277))
      | ~ m1_subset_1(F_277,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(D_271))))
      | ~ v5_pre_topc(F_277,'#skF_5',D_271)
      | ~ v1_funct_2(F_277,u1_struct_0('#skF_5'),u1_struct_0(D_271))
      | ~ v1_funct_1(F_277)
      | ~ m1_subset_1(E_275,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(D_271))))
      | ~ v5_pre_topc(E_275,'#skF_4',D_271)
      | ~ v1_funct_2(E_275,u1_struct_0('#skF_4'),u1_struct_0(D_271))
      | ~ v1_funct_1(E_275)
      | ~ l1_pre_topc(D_271)
      | ~ v2_pre_topc(D_271)
      | v2_struct_0(D_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_321])).

tff(c_273,plain,(
    ! [D_271,E_275,F_277] :
      ( v1_funct_1(k10_tmap_1('#skF_3',D_271,'#skF_4','#skF_5',E_275,F_277))
      | ~ m1_subset_1(F_277,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(D_271))))
      | ~ v5_pre_topc(F_277,'#skF_5',D_271)
      | ~ v1_funct_2(F_277,u1_struct_0('#skF_5'),u1_struct_0(D_271))
      | ~ v1_funct_1(F_277)
      | ~ m1_subset_1(E_275,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(D_271))))
      | ~ v5_pre_topc(E_275,'#skF_4',D_271)
      | ~ v1_funct_2(E_275,u1_struct_0('#skF_4'),u1_struct_0(D_271))
      | ~ v1_funct_1(E_275)
      | ~ l1_pre_topc(D_271)
      | ~ v2_pre_topc(D_271)
      | v2_struct_0(D_271) ) ),
    inference(negUnitSimplification,[status(thm)],[c_240,c_186])).

tff(c_302,plain,(
    ! [A_336,B_337,E_275] :
      ( v1_funct_1(k10_tmap_1('#skF_3','#skF_1'(A_336,B_337,'#skF_5'),'#skF_4','#skF_5',E_275,k3_tmap_1(A_336,'#skF_1'(A_336,B_337,'#skF_5'),k1_tsep_1(A_336,B_337,'#skF_5'),'#skF_5','#skF_2'(A_336,B_337,'#skF_5'))))
      | ~ v5_pre_topc(k3_tmap_1(A_336,'#skF_1'(A_336,B_337,'#skF_5'),k1_tsep_1(A_336,B_337,'#skF_5'),'#skF_5','#skF_2'(A_336,B_337,'#skF_5')),'#skF_5','#skF_1'(A_336,B_337,'#skF_5'))
      | ~ v1_funct_2(k3_tmap_1(A_336,'#skF_1'(A_336,B_337,'#skF_5'),k1_tsep_1(A_336,B_337,'#skF_5'),'#skF_5','#skF_2'(A_336,B_337,'#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'(A_336,B_337,'#skF_5')))
      | ~ v1_funct_1(k3_tmap_1(A_336,'#skF_1'(A_336,B_337,'#skF_5'),k1_tsep_1(A_336,B_337,'#skF_5'),'#skF_5','#skF_2'(A_336,B_337,'#skF_5')))
      | ~ m1_subset_1(E_275,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'(A_336,B_337,'#skF_5')))))
      | ~ v5_pre_topc(E_275,'#skF_4','#skF_1'(A_336,B_337,'#skF_5'))
      | ~ v1_funct_2(E_275,u1_struct_0('#skF_4'),u1_struct_0('#skF_1'(A_336,B_337,'#skF_5')))
      | ~ v1_funct_1(E_275)
      | ~ l1_pre_topc('#skF_1'(A_336,B_337,'#skF_5'))
      | ~ v2_pre_topc('#skF_1'(A_336,B_337,'#skF_5'))
      | v2_struct_0('#skF_1'(A_336,B_337,'#skF_5'))
      | r3_tsep_1(A_336,B_337,'#skF_5')
      | ~ r1_tsep_1(B_337,'#skF_5')
      | ~ m1_pre_topc('#skF_5',A_336)
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(B_337,A_336)
      | v2_struct_0(B_337)
      | ~ l1_pre_topc(A_336)
      | ~ v2_pre_topc(A_336)
      | v2_struct_0(A_336) ) ),
    inference(resolution,[status(thm)],[c_299,c_273])).

tff(c_578,plain,(
    ! [A_453,B_454,E_455] :
      ( v1_funct_1(k10_tmap_1('#skF_3','#skF_1'(A_453,B_454,'#skF_5'),'#skF_4','#skF_5',E_455,k3_tmap_1(A_453,'#skF_1'(A_453,B_454,'#skF_5'),k1_tsep_1(A_453,B_454,'#skF_5'),'#skF_5','#skF_2'(A_453,B_454,'#skF_5'))))
      | ~ v5_pre_topc(k3_tmap_1(A_453,'#skF_1'(A_453,B_454,'#skF_5'),k1_tsep_1(A_453,B_454,'#skF_5'),'#skF_5','#skF_2'(A_453,B_454,'#skF_5')),'#skF_5','#skF_1'(A_453,B_454,'#skF_5'))
      | ~ v1_funct_2(k3_tmap_1(A_453,'#skF_1'(A_453,B_454,'#skF_5'),k1_tsep_1(A_453,B_454,'#skF_5'),'#skF_5','#skF_2'(A_453,B_454,'#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'(A_453,B_454,'#skF_5')))
      | ~ v1_funct_1(k3_tmap_1(A_453,'#skF_1'(A_453,B_454,'#skF_5'),k1_tsep_1(A_453,B_454,'#skF_5'),'#skF_5','#skF_2'(A_453,B_454,'#skF_5')))
      | ~ m1_subset_1(E_455,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'(A_453,B_454,'#skF_5')))))
      | ~ v5_pre_topc(E_455,'#skF_4','#skF_1'(A_453,B_454,'#skF_5'))
      | ~ v1_funct_2(E_455,u1_struct_0('#skF_4'),u1_struct_0('#skF_1'(A_453,B_454,'#skF_5')))
      | ~ v1_funct_1(E_455)
      | ~ l1_pre_topc('#skF_1'(A_453,B_454,'#skF_5'))
      | ~ v2_pre_topc('#skF_1'(A_453,B_454,'#skF_5'))
      | v2_struct_0('#skF_1'(A_453,B_454,'#skF_5'))
      | r3_tsep_1(A_453,B_454,'#skF_5')
      | ~ r1_tsep_1(B_454,'#skF_5')
      | ~ m1_pre_topc('#skF_5',A_453)
      | ~ m1_pre_topc(B_454,A_453)
      | v2_struct_0(B_454)
      | ~ l1_pre_topc(A_453)
      | ~ v2_pre_topc(A_453)
      | v2_struct_0(A_453) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_302])).

tff(c_584,plain,(
    ! [A_11,B_39,E_455] :
      ( v1_funct_1(k10_tmap_1('#skF_3','#skF_1'(A_11,B_39,'#skF_5'),'#skF_4','#skF_5',E_455,k3_tmap_1(A_11,'#skF_1'(A_11,B_39,'#skF_5'),k1_tsep_1(A_11,B_39,'#skF_5'),'#skF_5','#skF_2'(A_11,B_39,'#skF_5'))))
      | ~ v5_pre_topc(k3_tmap_1(A_11,'#skF_1'(A_11,B_39,'#skF_5'),k1_tsep_1(A_11,B_39,'#skF_5'),'#skF_5','#skF_2'(A_11,B_39,'#skF_5')),'#skF_5','#skF_1'(A_11,B_39,'#skF_5'))
      | ~ v1_funct_1(k3_tmap_1(A_11,'#skF_1'(A_11,B_39,'#skF_5'),k1_tsep_1(A_11,B_39,'#skF_5'),'#skF_5','#skF_2'(A_11,B_39,'#skF_5')))
      | ~ m1_subset_1(E_455,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'(A_11,B_39,'#skF_5')))))
      | ~ v5_pre_topc(E_455,'#skF_4','#skF_1'(A_11,B_39,'#skF_5'))
      | ~ v1_funct_2(E_455,u1_struct_0('#skF_4'),u1_struct_0('#skF_1'(A_11,B_39,'#skF_5')))
      | ~ v1_funct_1(E_455)
      | ~ l1_pre_topc('#skF_1'(A_11,B_39,'#skF_5'))
      | ~ v2_pre_topc('#skF_1'(A_11,B_39,'#skF_5'))
      | v2_struct_0('#skF_1'(A_11,B_39,'#skF_5'))
      | r3_tsep_1(A_11,B_39,'#skF_5')
      | ~ r1_tsep_1(B_39,'#skF_5')
      | ~ m1_pre_topc('#skF_5',A_11)
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(B_39,A_11)
      | v2_struct_0(B_39)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(resolution,[status(thm)],[c_18,c_578])).

tff(c_589,plain,(
    ! [A_11,B_39,E_455] :
      ( v1_funct_1(k10_tmap_1('#skF_3','#skF_1'(A_11,B_39,'#skF_5'),'#skF_4','#skF_5',E_455,k3_tmap_1(A_11,'#skF_1'(A_11,B_39,'#skF_5'),k1_tsep_1(A_11,B_39,'#skF_5'),'#skF_5','#skF_2'(A_11,B_39,'#skF_5'))))
      | ~ v5_pre_topc(k3_tmap_1(A_11,'#skF_1'(A_11,B_39,'#skF_5'),k1_tsep_1(A_11,B_39,'#skF_5'),'#skF_5','#skF_2'(A_11,B_39,'#skF_5')),'#skF_5','#skF_1'(A_11,B_39,'#skF_5'))
      | ~ v1_funct_1(k3_tmap_1(A_11,'#skF_1'(A_11,B_39,'#skF_5'),k1_tsep_1(A_11,B_39,'#skF_5'),'#skF_5','#skF_2'(A_11,B_39,'#skF_5')))
      | ~ m1_subset_1(E_455,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'(A_11,B_39,'#skF_5')))))
      | ~ v5_pre_topc(E_455,'#skF_4','#skF_1'(A_11,B_39,'#skF_5'))
      | ~ v1_funct_2(E_455,u1_struct_0('#skF_4'),u1_struct_0('#skF_1'(A_11,B_39,'#skF_5')))
      | ~ v1_funct_1(E_455)
      | ~ l1_pre_topc('#skF_1'(A_11,B_39,'#skF_5'))
      | ~ v2_pre_topc('#skF_1'(A_11,B_39,'#skF_5'))
      | v2_struct_0('#skF_1'(A_11,B_39,'#skF_5'))
      | r3_tsep_1(A_11,B_39,'#skF_5')
      | ~ r1_tsep_1(B_39,'#skF_5')
      | ~ m1_pre_topc('#skF_5',A_11)
      | ~ m1_pre_topc(B_39,A_11)
      | v2_struct_0(B_39)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_584])).

tff(c_160,plain,(
    ! [D_271,E_275,F_277] :
      ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
      | v1_funct_2(k10_tmap_1('#skF_3',D_271,'#skF_4','#skF_5',E_275,F_277),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0(D_271))
      | ~ m1_subset_1(F_277,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(D_271))))
      | ~ v5_pre_topc(F_277,'#skF_5',D_271)
      | ~ v1_funct_2(F_277,u1_struct_0('#skF_5'),u1_struct_0(D_271))
      | ~ v1_funct_1(F_277)
      | ~ m1_subset_1(E_275,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(D_271))))
      | ~ v5_pre_topc(E_275,'#skF_4',D_271)
      | ~ v1_funct_2(E_275,u1_struct_0('#skF_4'),u1_struct_0(D_271))
      | ~ v1_funct_1(E_275)
      | ~ l1_pre_topc(D_271)
      | ~ v2_pre_topc(D_271)
      | v2_struct_0(D_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_321])).

tff(c_366,plain,(
    ! [D_271,E_275,F_277] :
      ( v1_funct_2(k10_tmap_1('#skF_3',D_271,'#skF_4','#skF_5',E_275,F_277),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0(D_271))
      | ~ m1_subset_1(F_277,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(D_271))))
      | ~ v5_pre_topc(F_277,'#skF_5',D_271)
      | ~ v1_funct_2(F_277,u1_struct_0('#skF_5'),u1_struct_0(D_271))
      | ~ v1_funct_1(F_277)
      | ~ m1_subset_1(E_275,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(D_271))))
      | ~ v5_pre_topc(E_275,'#skF_4',D_271)
      | ~ v1_funct_2(E_275,u1_struct_0('#skF_4'),u1_struct_0(D_271))
      | ~ v1_funct_1(E_275)
      | ~ l1_pre_topc(D_271)
      | ~ v2_pre_topc(D_271)
      | v2_struct_0(D_271) ) ),
    inference(negUnitSimplification,[status(thm)],[c_240,c_160])).

tff(c_6,plain,(
    ! [B_6,C_7,E_9,D_8,A_5,F_10] :
      ( m1_subset_1(k10_tmap_1(A_5,B_6,C_7,D_8,E_9,F_10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_5,C_7,D_8)),u1_struct_0(B_6))))
      | ~ m1_subset_1(F_10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_8),u1_struct_0(B_6))))
      | ~ v1_funct_2(F_10,u1_struct_0(D_8),u1_struct_0(B_6))
      | ~ v1_funct_1(F_10)
      | ~ m1_subset_1(E_9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_7),u1_struct_0(B_6))))
      | ~ v1_funct_2(E_9,u1_struct_0(C_7),u1_struct_0(B_6))
      | ~ v1_funct_1(E_9)
      | ~ m1_pre_topc(D_8,A_5)
      | v2_struct_0(D_8)
      | ~ m1_pre_topc(C_7,A_5)
      | v2_struct_0(C_7)
      | ~ l1_pre_topc(B_6)
      | ~ v2_pre_topc(B_6)
      | v2_struct_0(B_6)
      | ~ l1_pre_topc(A_5)
      | ~ v2_pre_topc(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_455,plain,(
    ! [B_380,C_379,A_381,E_378,D_382] :
      ( r2_funct_2(u1_struct_0(k1_tsep_1(A_381,C_379,D_382)),u1_struct_0(B_380),E_378,k10_tmap_1(A_381,B_380,C_379,D_382,k3_tmap_1(A_381,B_380,k1_tsep_1(A_381,C_379,D_382),C_379,E_378),k3_tmap_1(A_381,B_380,k1_tsep_1(A_381,C_379,D_382),D_382,E_378)))
      | ~ m1_subset_1(E_378,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_381,C_379,D_382)),u1_struct_0(B_380))))
      | ~ v1_funct_2(E_378,u1_struct_0(k1_tsep_1(A_381,C_379,D_382)),u1_struct_0(B_380))
      | ~ v1_funct_1(E_378)
      | ~ m1_pre_topc(D_382,A_381)
      | v2_struct_0(D_382)
      | ~ m1_pre_topc(C_379,A_381)
      | v2_struct_0(C_379)
      | ~ l1_pre_topc(B_380)
      | ~ v2_pre_topc(B_380)
      | v2_struct_0(B_380)
      | ~ l1_pre_topc(A_381)
      | ~ v2_pre_topc(A_381)
      | v2_struct_0(A_381) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_4,plain,(
    ! [D_4,C_3,A_1,B_2] :
      ( D_4 = C_3
      | ~ r2_funct_2(A_1,B_2,C_3,D_4)
      | ~ m1_subset_1(D_4,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(D_4,A_1,B_2)
      | ~ v1_funct_1(D_4)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(C_3,A_1,B_2)
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_611,plain,(
    ! [C_493,B_494,D_496,A_492,E_495] :
      ( k10_tmap_1(A_492,B_494,C_493,D_496,k3_tmap_1(A_492,B_494,k1_tsep_1(A_492,C_493,D_496),C_493,E_495),k3_tmap_1(A_492,B_494,k1_tsep_1(A_492,C_493,D_496),D_496,E_495)) = E_495
      | ~ m1_subset_1(k10_tmap_1(A_492,B_494,C_493,D_496,k3_tmap_1(A_492,B_494,k1_tsep_1(A_492,C_493,D_496),C_493,E_495),k3_tmap_1(A_492,B_494,k1_tsep_1(A_492,C_493,D_496),D_496,E_495)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_492,C_493,D_496)),u1_struct_0(B_494))))
      | ~ v1_funct_2(k10_tmap_1(A_492,B_494,C_493,D_496,k3_tmap_1(A_492,B_494,k1_tsep_1(A_492,C_493,D_496),C_493,E_495),k3_tmap_1(A_492,B_494,k1_tsep_1(A_492,C_493,D_496),D_496,E_495)),u1_struct_0(k1_tsep_1(A_492,C_493,D_496)),u1_struct_0(B_494))
      | ~ v1_funct_1(k10_tmap_1(A_492,B_494,C_493,D_496,k3_tmap_1(A_492,B_494,k1_tsep_1(A_492,C_493,D_496),C_493,E_495),k3_tmap_1(A_492,B_494,k1_tsep_1(A_492,C_493,D_496),D_496,E_495)))
      | ~ m1_subset_1(E_495,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_492,C_493,D_496)),u1_struct_0(B_494))))
      | ~ v1_funct_2(E_495,u1_struct_0(k1_tsep_1(A_492,C_493,D_496)),u1_struct_0(B_494))
      | ~ v1_funct_1(E_495)
      | ~ m1_pre_topc(D_496,A_492)
      | v2_struct_0(D_496)
      | ~ m1_pre_topc(C_493,A_492)
      | v2_struct_0(C_493)
      | ~ l1_pre_topc(B_494)
      | ~ v2_pre_topc(B_494)
      | v2_struct_0(B_494)
      | ~ l1_pre_topc(A_492)
      | ~ v2_pre_topc(A_492)
      | v2_struct_0(A_492) ) ),
    inference(resolution,[status(thm)],[c_455,c_4])).

tff(c_632,plain,(
    ! [D_533,C_535,E_537,A_536,B_534] :
      ( k10_tmap_1(A_536,B_534,C_535,D_533,k3_tmap_1(A_536,B_534,k1_tsep_1(A_536,C_535,D_533),C_535,E_537),k3_tmap_1(A_536,B_534,k1_tsep_1(A_536,C_535,D_533),D_533,E_537)) = E_537
      | ~ v1_funct_2(k10_tmap_1(A_536,B_534,C_535,D_533,k3_tmap_1(A_536,B_534,k1_tsep_1(A_536,C_535,D_533),C_535,E_537),k3_tmap_1(A_536,B_534,k1_tsep_1(A_536,C_535,D_533),D_533,E_537)),u1_struct_0(k1_tsep_1(A_536,C_535,D_533)),u1_struct_0(B_534))
      | ~ v1_funct_1(k10_tmap_1(A_536,B_534,C_535,D_533,k3_tmap_1(A_536,B_534,k1_tsep_1(A_536,C_535,D_533),C_535,E_537),k3_tmap_1(A_536,B_534,k1_tsep_1(A_536,C_535,D_533),D_533,E_537)))
      | ~ m1_subset_1(E_537,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_536,C_535,D_533)),u1_struct_0(B_534))))
      | ~ v1_funct_2(E_537,u1_struct_0(k1_tsep_1(A_536,C_535,D_533)),u1_struct_0(B_534))
      | ~ v1_funct_1(E_537)
      | ~ m1_subset_1(k3_tmap_1(A_536,B_534,k1_tsep_1(A_536,C_535,D_533),D_533,E_537),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_533),u1_struct_0(B_534))))
      | ~ v1_funct_2(k3_tmap_1(A_536,B_534,k1_tsep_1(A_536,C_535,D_533),D_533,E_537),u1_struct_0(D_533),u1_struct_0(B_534))
      | ~ v1_funct_1(k3_tmap_1(A_536,B_534,k1_tsep_1(A_536,C_535,D_533),D_533,E_537))
      | ~ m1_subset_1(k3_tmap_1(A_536,B_534,k1_tsep_1(A_536,C_535,D_533),C_535,E_537),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_535),u1_struct_0(B_534))))
      | ~ v1_funct_2(k3_tmap_1(A_536,B_534,k1_tsep_1(A_536,C_535,D_533),C_535,E_537),u1_struct_0(C_535),u1_struct_0(B_534))
      | ~ v1_funct_1(k3_tmap_1(A_536,B_534,k1_tsep_1(A_536,C_535,D_533),C_535,E_537))
      | ~ m1_pre_topc(D_533,A_536)
      | v2_struct_0(D_533)
      | ~ m1_pre_topc(C_535,A_536)
      | v2_struct_0(C_535)
      | ~ l1_pre_topc(B_534)
      | ~ v2_pre_topc(B_534)
      | v2_struct_0(B_534)
      | ~ l1_pre_topc(A_536)
      | ~ v2_pre_topc(A_536)
      | v2_struct_0(A_536) ) ),
    inference(resolution,[status(thm)],[c_6,c_611])).

tff(c_640,plain,(
    ! [D_271,E_537] :
      ( k10_tmap_1('#skF_3',D_271,'#skF_4','#skF_5',k3_tmap_1('#skF_3',D_271,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_537),k3_tmap_1('#skF_3',D_271,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_537)) = E_537
      | ~ v1_funct_1(k10_tmap_1('#skF_3',D_271,'#skF_4','#skF_5',k3_tmap_1('#skF_3',D_271,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_537),k3_tmap_1('#skF_3',D_271,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_537)))
      | ~ m1_subset_1(E_537,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0(D_271))))
      | ~ v1_funct_2(E_537,u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0(D_271))
      | ~ v1_funct_1(E_537)
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(k3_tmap_1('#skF_3',D_271,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_537),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(D_271))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_3',D_271,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_537),'#skF_5',D_271)
      | ~ v1_funct_2(k3_tmap_1('#skF_3',D_271,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_537),u1_struct_0('#skF_5'),u1_struct_0(D_271))
      | ~ v1_funct_1(k3_tmap_1('#skF_3',D_271,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_537))
      | ~ m1_subset_1(k3_tmap_1('#skF_3',D_271,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_537),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(D_271))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_3',D_271,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_537),'#skF_4',D_271)
      | ~ v1_funct_2(k3_tmap_1('#skF_3',D_271,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_537),u1_struct_0('#skF_4'),u1_struct_0(D_271))
      | ~ v1_funct_1(k3_tmap_1('#skF_3',D_271,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_537))
      | ~ l1_pre_topc(D_271)
      | ~ v2_pre_topc(D_271)
      | v2_struct_0(D_271) ) ),
    inference(resolution,[status(thm)],[c_366,c_632])).

tff(c_644,plain,(
    ! [D_271,E_537] :
      ( k10_tmap_1('#skF_3',D_271,'#skF_4','#skF_5',k3_tmap_1('#skF_3',D_271,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_537),k3_tmap_1('#skF_3',D_271,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_537)) = E_537
      | ~ v1_funct_1(k10_tmap_1('#skF_3',D_271,'#skF_4','#skF_5',k3_tmap_1('#skF_3',D_271,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_537),k3_tmap_1('#skF_3',D_271,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_537)))
      | ~ m1_subset_1(E_537,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0(D_271))))
      | ~ v1_funct_2(E_537,u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0(D_271))
      | ~ v1_funct_1(E_537)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(k3_tmap_1('#skF_3',D_271,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_537),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(D_271))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_3',D_271,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_537),'#skF_5',D_271)
      | ~ v1_funct_2(k3_tmap_1('#skF_3',D_271,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_537),u1_struct_0('#skF_5'),u1_struct_0(D_271))
      | ~ v1_funct_1(k3_tmap_1('#skF_3',D_271,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_537))
      | ~ m1_subset_1(k3_tmap_1('#skF_3',D_271,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_537),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(D_271))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_3',D_271,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_537),'#skF_4',D_271)
      | ~ v1_funct_2(k3_tmap_1('#skF_3',D_271,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_537),u1_struct_0('#skF_4'),u1_struct_0(D_271))
      | ~ v1_funct_1(k3_tmap_1('#skF_3',D_271,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_537))
      | ~ l1_pre_topc(D_271)
      | ~ v2_pre_topc(D_271)
      | v2_struct_0(D_271) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_68,c_640])).

tff(c_725,plain,(
    ! [D_547,E_548] :
      ( k10_tmap_1('#skF_3',D_547,'#skF_4','#skF_5',k3_tmap_1('#skF_3',D_547,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_548),k3_tmap_1('#skF_3',D_547,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_548)) = E_548
      | ~ v1_funct_1(k10_tmap_1('#skF_3',D_547,'#skF_4','#skF_5',k3_tmap_1('#skF_3',D_547,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_548),k3_tmap_1('#skF_3',D_547,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_548)))
      | ~ m1_subset_1(E_548,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0(D_547))))
      | ~ v1_funct_2(E_548,u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0(D_547))
      | ~ v1_funct_1(E_548)
      | ~ m1_subset_1(k3_tmap_1('#skF_3',D_547,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_548),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(D_547))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_3',D_547,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_548),'#skF_5',D_547)
      | ~ v1_funct_2(k3_tmap_1('#skF_3',D_547,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_548),u1_struct_0('#skF_5'),u1_struct_0(D_547))
      | ~ v1_funct_1(k3_tmap_1('#skF_3',D_547,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_548))
      | ~ m1_subset_1(k3_tmap_1('#skF_3',D_547,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_548),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(D_547))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_3',D_547,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_548),'#skF_4',D_547)
      | ~ v1_funct_2(k3_tmap_1('#skF_3',D_547,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_548),u1_struct_0('#skF_4'),u1_struct_0(D_547))
      | ~ v1_funct_1(k3_tmap_1('#skF_3',D_547,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_548))
      | ~ l1_pre_topc(D_547)
      | ~ v2_pre_topc(D_547)
      | v2_struct_0(D_547) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_70,c_644])).

tff(c_731,plain,
    ( k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_5',k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))) = '#skF_2'('#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5'))
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
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_589,c_725])).

tff(c_738,plain,
    ( k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_5',k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))) = '#skF_2'('#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_68,c_237,c_731])).

tff(c_739,plain,
    ( k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_5',k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))) = '#skF_2'('#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_240,c_738])).

tff(c_768,plain,(
    ~ v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_739])).

tff(c_771,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_768])).

tff(c_774,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_68,c_237,c_771])).

tff(c_776,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_70,c_240,c_774])).

tff(c_778,plain,(
    v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_739])).

tff(c_36,plain,(
    ! [A_11,B_39,C_53] :
      ( l1_pre_topc('#skF_1'(A_11,B_39,C_53))
      | r3_tsep_1(A_11,B_39,C_53)
      | ~ r1_tsep_1(B_39,C_53)
      | ~ m1_pre_topc(C_53,A_11)
      | v2_struct_0(C_53)
      | ~ m1_pre_topc(B_39,A_11)
      | v2_struct_0(B_39)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_22,plain,(
    ! [A_11,B_39,C_53] :
      ( m1_subset_1(k3_tmap_1(A_11,'#skF_1'(A_11,B_39,C_53),k1_tsep_1(A_11,B_39,C_53),B_39,'#skF_2'(A_11,B_39,C_53)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_39),u1_struct_0('#skF_1'(A_11,B_39,C_53)))))
      | r3_tsep_1(A_11,B_39,C_53)
      | ~ r1_tsep_1(B_39,C_53)
      | ~ m1_pre_topc(C_53,A_11)
      | v2_struct_0(C_53)
      | ~ m1_pre_topc(B_39,A_11)
      | v2_struct_0(B_39)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_14,plain,(
    ! [A_11,B_39,C_53] :
      ( m1_subset_1(k3_tmap_1(A_11,'#skF_1'(A_11,B_39,C_53),k1_tsep_1(A_11,B_39,C_53),C_53,'#skF_2'(A_11,B_39,C_53)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_53),u1_struct_0('#skF_1'(A_11,B_39,C_53)))))
      | r3_tsep_1(A_11,B_39,C_53)
      | ~ r1_tsep_1(B_39,C_53)
      | ~ m1_pre_topc(C_53,A_11)
      | v2_struct_0(C_53)
      | ~ m1_pre_topc(B_39,A_11)
      | v2_struct_0(B_39)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_325,plain,(
    ! [C_342,B_341,D_339,F_340,A_343,E_344] :
      ( v1_funct_1(k10_tmap_1(A_343,B_341,C_342,D_339,E_344,F_340))
      | ~ m1_subset_1(F_340,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_339),u1_struct_0(B_341))))
      | ~ v1_funct_2(F_340,u1_struct_0(D_339),u1_struct_0(B_341))
      | ~ v1_funct_1(F_340)
      | ~ m1_subset_1(E_344,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_342),u1_struct_0(B_341))))
      | ~ v1_funct_2(E_344,u1_struct_0(C_342),u1_struct_0(B_341))
      | ~ v1_funct_1(E_344)
      | ~ m1_pre_topc(D_339,A_343)
      | v2_struct_0(D_339)
      | ~ m1_pre_topc(C_342,A_343)
      | v2_struct_0(C_342)
      | ~ l1_pre_topc(B_341)
      | ~ v2_pre_topc(B_341)
      | v2_struct_0(B_341)
      | ~ l1_pre_topc(A_343)
      | ~ v2_pre_topc(A_343)
      | v2_struct_0(A_343) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_592,plain,(
    ! [B_464,C_465,E_468,C_466,A_467,A_463] :
      ( v1_funct_1(k10_tmap_1(A_463,'#skF_1'(A_467,B_464,C_465),C_466,C_465,E_468,k3_tmap_1(A_467,'#skF_1'(A_467,B_464,C_465),k1_tsep_1(A_467,B_464,C_465),C_465,'#skF_2'(A_467,B_464,C_465))))
      | ~ v1_funct_2(k3_tmap_1(A_467,'#skF_1'(A_467,B_464,C_465),k1_tsep_1(A_467,B_464,C_465),C_465,'#skF_2'(A_467,B_464,C_465)),u1_struct_0(C_465),u1_struct_0('#skF_1'(A_467,B_464,C_465)))
      | ~ v1_funct_1(k3_tmap_1(A_467,'#skF_1'(A_467,B_464,C_465),k1_tsep_1(A_467,B_464,C_465),C_465,'#skF_2'(A_467,B_464,C_465)))
      | ~ m1_subset_1(E_468,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_466),u1_struct_0('#skF_1'(A_467,B_464,C_465)))))
      | ~ v1_funct_2(E_468,u1_struct_0(C_466),u1_struct_0('#skF_1'(A_467,B_464,C_465)))
      | ~ v1_funct_1(E_468)
      | ~ m1_pre_topc(C_465,A_463)
      | ~ m1_pre_topc(C_466,A_463)
      | v2_struct_0(C_466)
      | ~ l1_pre_topc('#skF_1'(A_467,B_464,C_465))
      | ~ v2_pre_topc('#skF_1'(A_467,B_464,C_465))
      | v2_struct_0('#skF_1'(A_467,B_464,C_465))
      | ~ l1_pre_topc(A_463)
      | ~ v2_pre_topc(A_463)
      | v2_struct_0(A_463)
      | r3_tsep_1(A_467,B_464,C_465)
      | ~ r1_tsep_1(B_464,C_465)
      | ~ m1_pre_topc(C_465,A_467)
      | v2_struct_0(C_465)
      | ~ m1_pre_topc(B_464,A_467)
      | v2_struct_0(B_464)
      | ~ l1_pre_topc(A_467)
      | ~ v2_pre_topc(A_467)
      | v2_struct_0(A_467) ) ),
    inference(resolution,[status(thm)],[c_14,c_325])).

tff(c_599,plain,(
    ! [E_468,B_39,C_466,C_53,A_463,A_11] :
      ( v1_funct_1(k10_tmap_1(A_463,'#skF_1'(A_11,B_39,C_53),C_466,C_53,E_468,k3_tmap_1(A_11,'#skF_1'(A_11,B_39,C_53),k1_tsep_1(A_11,B_39,C_53),C_53,'#skF_2'(A_11,B_39,C_53))))
      | ~ v1_funct_1(k3_tmap_1(A_11,'#skF_1'(A_11,B_39,C_53),k1_tsep_1(A_11,B_39,C_53),C_53,'#skF_2'(A_11,B_39,C_53)))
      | ~ m1_subset_1(E_468,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_466),u1_struct_0('#skF_1'(A_11,B_39,C_53)))))
      | ~ v1_funct_2(E_468,u1_struct_0(C_466),u1_struct_0('#skF_1'(A_11,B_39,C_53)))
      | ~ v1_funct_1(E_468)
      | ~ m1_pre_topc(C_53,A_463)
      | ~ m1_pre_topc(C_466,A_463)
      | v2_struct_0(C_466)
      | ~ l1_pre_topc('#skF_1'(A_11,B_39,C_53))
      | ~ v2_pre_topc('#skF_1'(A_11,B_39,C_53))
      | v2_struct_0('#skF_1'(A_11,B_39,C_53))
      | ~ l1_pre_topc(A_463)
      | ~ v2_pre_topc(A_463)
      | v2_struct_0(A_463)
      | r3_tsep_1(A_11,B_39,C_53)
      | ~ r1_tsep_1(B_39,C_53)
      | ~ m1_pre_topc(C_53,A_11)
      | v2_struct_0(C_53)
      | ~ m1_pre_topc(B_39,A_11)
      | v2_struct_0(B_39)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(resolution,[status(thm)],[c_18,c_592])).

tff(c_8,plain,(
    ! [B_6,C_7,E_9,D_8,A_5,F_10] :
      ( v1_funct_2(k10_tmap_1(A_5,B_6,C_7,D_8,E_9,F_10),u1_struct_0(k1_tsep_1(A_5,C_7,D_8)),u1_struct_0(B_6))
      | ~ m1_subset_1(F_10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_8),u1_struct_0(B_6))))
      | ~ v1_funct_2(F_10,u1_struct_0(D_8),u1_struct_0(B_6))
      | ~ v1_funct_1(F_10)
      | ~ m1_subset_1(E_9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_7),u1_struct_0(B_6))))
      | ~ v1_funct_2(E_9,u1_struct_0(C_7),u1_struct_0(B_6))
      | ~ v1_funct_1(E_9)
      | ~ m1_pre_topc(D_8,A_5)
      | v2_struct_0(D_8)
      | ~ m1_pre_topc(C_7,A_5)
      | v2_struct_0(C_7)
      | ~ l1_pre_topc(B_6)
      | ~ v2_pre_topc(B_6)
      | v2_struct_0(B_6)
      | ~ l1_pre_topc(A_5)
      | ~ v2_pre_topc(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_646,plain,(
    ! [E_540,D_538,C_541,B_539,A_542] :
      ( k10_tmap_1(A_542,B_539,C_541,D_538,k3_tmap_1(A_542,B_539,k1_tsep_1(A_542,C_541,D_538),C_541,E_540),k3_tmap_1(A_542,B_539,k1_tsep_1(A_542,C_541,D_538),D_538,E_540)) = E_540
      | ~ v1_funct_1(k10_tmap_1(A_542,B_539,C_541,D_538,k3_tmap_1(A_542,B_539,k1_tsep_1(A_542,C_541,D_538),C_541,E_540),k3_tmap_1(A_542,B_539,k1_tsep_1(A_542,C_541,D_538),D_538,E_540)))
      | ~ m1_subset_1(E_540,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_542,C_541,D_538)),u1_struct_0(B_539))))
      | ~ v1_funct_2(E_540,u1_struct_0(k1_tsep_1(A_542,C_541,D_538)),u1_struct_0(B_539))
      | ~ v1_funct_1(E_540)
      | ~ m1_subset_1(k3_tmap_1(A_542,B_539,k1_tsep_1(A_542,C_541,D_538),D_538,E_540),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_538),u1_struct_0(B_539))))
      | ~ v1_funct_2(k3_tmap_1(A_542,B_539,k1_tsep_1(A_542,C_541,D_538),D_538,E_540),u1_struct_0(D_538),u1_struct_0(B_539))
      | ~ v1_funct_1(k3_tmap_1(A_542,B_539,k1_tsep_1(A_542,C_541,D_538),D_538,E_540))
      | ~ m1_subset_1(k3_tmap_1(A_542,B_539,k1_tsep_1(A_542,C_541,D_538),C_541,E_540),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_541),u1_struct_0(B_539))))
      | ~ v1_funct_2(k3_tmap_1(A_542,B_539,k1_tsep_1(A_542,C_541,D_538),C_541,E_540),u1_struct_0(C_541),u1_struct_0(B_539))
      | ~ v1_funct_1(k3_tmap_1(A_542,B_539,k1_tsep_1(A_542,C_541,D_538),C_541,E_540))
      | ~ m1_pre_topc(D_538,A_542)
      | v2_struct_0(D_538)
      | ~ m1_pre_topc(C_541,A_542)
      | v2_struct_0(C_541)
      | ~ l1_pre_topc(B_539)
      | ~ v2_pre_topc(B_539)
      | v2_struct_0(B_539)
      | ~ l1_pre_topc(A_542)
      | ~ v2_pre_topc(A_542)
      | v2_struct_0(A_542) ) ),
    inference(resolution,[status(thm)],[c_8,c_632])).

tff(c_760,plain,(
    ! [A_588,B_589,C_590] :
      ( k10_tmap_1(A_588,'#skF_1'(A_588,B_589,C_590),B_589,C_590,k3_tmap_1(A_588,'#skF_1'(A_588,B_589,C_590),k1_tsep_1(A_588,B_589,C_590),B_589,'#skF_2'(A_588,B_589,C_590)),k3_tmap_1(A_588,'#skF_1'(A_588,B_589,C_590),k1_tsep_1(A_588,B_589,C_590),C_590,'#skF_2'(A_588,B_589,C_590))) = '#skF_2'(A_588,B_589,C_590)
      | ~ m1_subset_1('#skF_2'(A_588,B_589,C_590),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_588,B_589,C_590)),u1_struct_0('#skF_1'(A_588,B_589,C_590)))))
      | ~ v1_funct_2('#skF_2'(A_588,B_589,C_590),u1_struct_0(k1_tsep_1(A_588,B_589,C_590)),u1_struct_0('#skF_1'(A_588,B_589,C_590)))
      | ~ v1_funct_1('#skF_2'(A_588,B_589,C_590))
      | ~ m1_subset_1(k3_tmap_1(A_588,'#skF_1'(A_588,B_589,C_590),k1_tsep_1(A_588,B_589,C_590),C_590,'#skF_2'(A_588,B_589,C_590)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_590),u1_struct_0('#skF_1'(A_588,B_589,C_590)))))
      | ~ v1_funct_2(k3_tmap_1(A_588,'#skF_1'(A_588,B_589,C_590),k1_tsep_1(A_588,B_589,C_590),C_590,'#skF_2'(A_588,B_589,C_590)),u1_struct_0(C_590),u1_struct_0('#skF_1'(A_588,B_589,C_590)))
      | ~ v1_funct_1(k3_tmap_1(A_588,'#skF_1'(A_588,B_589,C_590),k1_tsep_1(A_588,B_589,C_590),C_590,'#skF_2'(A_588,B_589,C_590)))
      | ~ m1_subset_1(k3_tmap_1(A_588,'#skF_1'(A_588,B_589,C_590),k1_tsep_1(A_588,B_589,C_590),B_589,'#skF_2'(A_588,B_589,C_590)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_589),u1_struct_0('#skF_1'(A_588,B_589,C_590)))))
      | ~ v1_funct_2(k3_tmap_1(A_588,'#skF_1'(A_588,B_589,C_590),k1_tsep_1(A_588,B_589,C_590),B_589,'#skF_2'(A_588,B_589,C_590)),u1_struct_0(B_589),u1_struct_0('#skF_1'(A_588,B_589,C_590)))
      | ~ v1_funct_1(k3_tmap_1(A_588,'#skF_1'(A_588,B_589,C_590),k1_tsep_1(A_588,B_589,C_590),B_589,'#skF_2'(A_588,B_589,C_590)))
      | ~ l1_pre_topc('#skF_1'(A_588,B_589,C_590))
      | ~ v2_pre_topc('#skF_1'(A_588,B_589,C_590))
      | v2_struct_0('#skF_1'(A_588,B_589,C_590))
      | r3_tsep_1(A_588,B_589,C_590)
      | ~ r1_tsep_1(B_589,C_590)
      | ~ m1_pre_topc(C_590,A_588)
      | v2_struct_0(C_590)
      | ~ m1_pre_topc(B_589,A_588)
      | v2_struct_0(B_589)
      | ~ l1_pre_topc(A_588)
      | ~ v2_pre_topc(A_588)
      | v2_struct_0(A_588) ) ),
    inference(resolution,[status(thm)],[c_599,c_646])).

tff(c_779,plain,(
    ! [A_591,B_592,C_593] :
      ( k10_tmap_1(A_591,'#skF_1'(A_591,B_592,C_593),B_592,C_593,k3_tmap_1(A_591,'#skF_1'(A_591,B_592,C_593),k1_tsep_1(A_591,B_592,C_593),B_592,'#skF_2'(A_591,B_592,C_593)),k3_tmap_1(A_591,'#skF_1'(A_591,B_592,C_593),k1_tsep_1(A_591,B_592,C_593),C_593,'#skF_2'(A_591,B_592,C_593))) = '#skF_2'(A_591,B_592,C_593)
      | ~ m1_subset_1('#skF_2'(A_591,B_592,C_593),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_591,B_592,C_593)),u1_struct_0('#skF_1'(A_591,B_592,C_593)))))
      | ~ v1_funct_2('#skF_2'(A_591,B_592,C_593),u1_struct_0(k1_tsep_1(A_591,B_592,C_593)),u1_struct_0('#skF_1'(A_591,B_592,C_593)))
      | ~ v1_funct_1('#skF_2'(A_591,B_592,C_593))
      | ~ v1_funct_2(k3_tmap_1(A_591,'#skF_1'(A_591,B_592,C_593),k1_tsep_1(A_591,B_592,C_593),C_593,'#skF_2'(A_591,B_592,C_593)),u1_struct_0(C_593),u1_struct_0('#skF_1'(A_591,B_592,C_593)))
      | ~ v1_funct_1(k3_tmap_1(A_591,'#skF_1'(A_591,B_592,C_593),k1_tsep_1(A_591,B_592,C_593),C_593,'#skF_2'(A_591,B_592,C_593)))
      | ~ m1_subset_1(k3_tmap_1(A_591,'#skF_1'(A_591,B_592,C_593),k1_tsep_1(A_591,B_592,C_593),B_592,'#skF_2'(A_591,B_592,C_593)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_592),u1_struct_0('#skF_1'(A_591,B_592,C_593)))))
      | ~ v1_funct_2(k3_tmap_1(A_591,'#skF_1'(A_591,B_592,C_593),k1_tsep_1(A_591,B_592,C_593),B_592,'#skF_2'(A_591,B_592,C_593)),u1_struct_0(B_592),u1_struct_0('#skF_1'(A_591,B_592,C_593)))
      | ~ v1_funct_1(k3_tmap_1(A_591,'#skF_1'(A_591,B_592,C_593),k1_tsep_1(A_591,B_592,C_593),B_592,'#skF_2'(A_591,B_592,C_593)))
      | ~ l1_pre_topc('#skF_1'(A_591,B_592,C_593))
      | ~ v2_pre_topc('#skF_1'(A_591,B_592,C_593))
      | v2_struct_0('#skF_1'(A_591,B_592,C_593))
      | r3_tsep_1(A_591,B_592,C_593)
      | ~ r1_tsep_1(B_592,C_593)
      | ~ m1_pre_topc(C_593,A_591)
      | v2_struct_0(C_593)
      | ~ m1_pre_topc(B_592,A_591)
      | v2_struct_0(B_592)
      | ~ l1_pre_topc(A_591)
      | ~ v2_pre_topc(A_591)
      | v2_struct_0(A_591) ) ),
    inference(resolution,[status(thm)],[c_14,c_760])).

tff(c_787,plain,(
    ! [A_594,B_595,C_596] :
      ( k10_tmap_1(A_594,'#skF_1'(A_594,B_595,C_596),B_595,C_596,k3_tmap_1(A_594,'#skF_1'(A_594,B_595,C_596),k1_tsep_1(A_594,B_595,C_596),B_595,'#skF_2'(A_594,B_595,C_596)),k3_tmap_1(A_594,'#skF_1'(A_594,B_595,C_596),k1_tsep_1(A_594,B_595,C_596),C_596,'#skF_2'(A_594,B_595,C_596))) = '#skF_2'(A_594,B_595,C_596)
      | ~ m1_subset_1('#skF_2'(A_594,B_595,C_596),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_594,B_595,C_596)),u1_struct_0('#skF_1'(A_594,B_595,C_596)))))
      | ~ v1_funct_2('#skF_2'(A_594,B_595,C_596),u1_struct_0(k1_tsep_1(A_594,B_595,C_596)),u1_struct_0('#skF_1'(A_594,B_595,C_596)))
      | ~ v1_funct_1('#skF_2'(A_594,B_595,C_596))
      | ~ v1_funct_2(k3_tmap_1(A_594,'#skF_1'(A_594,B_595,C_596),k1_tsep_1(A_594,B_595,C_596),C_596,'#skF_2'(A_594,B_595,C_596)),u1_struct_0(C_596),u1_struct_0('#skF_1'(A_594,B_595,C_596)))
      | ~ v1_funct_1(k3_tmap_1(A_594,'#skF_1'(A_594,B_595,C_596),k1_tsep_1(A_594,B_595,C_596),C_596,'#skF_2'(A_594,B_595,C_596)))
      | ~ v1_funct_2(k3_tmap_1(A_594,'#skF_1'(A_594,B_595,C_596),k1_tsep_1(A_594,B_595,C_596),B_595,'#skF_2'(A_594,B_595,C_596)),u1_struct_0(B_595),u1_struct_0('#skF_1'(A_594,B_595,C_596)))
      | ~ v1_funct_1(k3_tmap_1(A_594,'#skF_1'(A_594,B_595,C_596),k1_tsep_1(A_594,B_595,C_596),B_595,'#skF_2'(A_594,B_595,C_596)))
      | ~ l1_pre_topc('#skF_1'(A_594,B_595,C_596))
      | ~ v2_pre_topc('#skF_1'(A_594,B_595,C_596))
      | v2_struct_0('#skF_1'(A_594,B_595,C_596))
      | r3_tsep_1(A_594,B_595,C_596)
      | ~ r1_tsep_1(B_595,C_596)
      | ~ m1_pre_topc(C_596,A_594)
      | v2_struct_0(C_596)
      | ~ m1_pre_topc(B_595,A_594)
      | v2_struct_0(B_595)
      | ~ l1_pre_topc(A_594)
      | ~ v2_pre_topc(A_594)
      | v2_struct_0(A_594) ) ),
    inference(resolution,[status(thm)],[c_22,c_779])).

tff(c_134,plain,(
    ! [D_271,E_275,F_277] :
      ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
      | v5_pre_topc(k10_tmap_1('#skF_3',D_271,'#skF_4','#skF_5',E_275,F_277),k1_tsep_1('#skF_3','#skF_4','#skF_5'),D_271)
      | ~ m1_subset_1(F_277,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(D_271))))
      | ~ v5_pre_topc(F_277,'#skF_5',D_271)
      | ~ v1_funct_2(F_277,u1_struct_0('#skF_5'),u1_struct_0(D_271))
      | ~ v1_funct_1(F_277)
      | ~ m1_subset_1(E_275,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(D_271))))
      | ~ v5_pre_topc(E_275,'#skF_4',D_271)
      | ~ v1_funct_2(E_275,u1_struct_0('#skF_4'),u1_struct_0(D_271))
      | ~ v1_funct_1(E_275)
      | ~ l1_pre_topc(D_271)
      | ~ v2_pre_topc(D_271)
      | v2_struct_0(D_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_321])).

tff(c_343,plain,(
    ! [D_348,E_349,F_350] :
      ( v5_pre_topc(k10_tmap_1('#skF_3',D_348,'#skF_4','#skF_5',E_349,F_350),k1_tsep_1('#skF_3','#skF_4','#skF_5'),D_348)
      | ~ m1_subset_1(F_350,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(D_348))))
      | ~ v5_pre_topc(F_350,'#skF_5',D_348)
      | ~ v1_funct_2(F_350,u1_struct_0('#skF_5'),u1_struct_0(D_348))
      | ~ v1_funct_1(F_350)
      | ~ m1_subset_1(E_349,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(D_348))))
      | ~ v5_pre_topc(E_349,'#skF_4',D_348)
      | ~ v1_funct_2(E_349,u1_struct_0('#skF_4'),u1_struct_0(D_348))
      | ~ v1_funct_1(E_349)
      | ~ l1_pre_topc(D_348)
      | ~ v2_pre_topc(D_348)
      | v2_struct_0(D_348) ) ),
    inference(negUnitSimplification,[status(thm)],[c_240,c_134])).

tff(c_346,plain,(
    ! [A_11,B_39,E_349] :
      ( v5_pre_topc(k10_tmap_1('#skF_3','#skF_1'(A_11,B_39,'#skF_5'),'#skF_4','#skF_5',E_349,k3_tmap_1(A_11,'#skF_1'(A_11,B_39,'#skF_5'),k1_tsep_1(A_11,B_39,'#skF_5'),'#skF_5','#skF_2'(A_11,B_39,'#skF_5'))),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_1'(A_11,B_39,'#skF_5'))
      | ~ v5_pre_topc(k3_tmap_1(A_11,'#skF_1'(A_11,B_39,'#skF_5'),k1_tsep_1(A_11,B_39,'#skF_5'),'#skF_5','#skF_2'(A_11,B_39,'#skF_5')),'#skF_5','#skF_1'(A_11,B_39,'#skF_5'))
      | ~ v1_funct_2(k3_tmap_1(A_11,'#skF_1'(A_11,B_39,'#skF_5'),k1_tsep_1(A_11,B_39,'#skF_5'),'#skF_5','#skF_2'(A_11,B_39,'#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'(A_11,B_39,'#skF_5')))
      | ~ v1_funct_1(k3_tmap_1(A_11,'#skF_1'(A_11,B_39,'#skF_5'),k1_tsep_1(A_11,B_39,'#skF_5'),'#skF_5','#skF_2'(A_11,B_39,'#skF_5')))
      | ~ m1_subset_1(E_349,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'(A_11,B_39,'#skF_5')))))
      | ~ v5_pre_topc(E_349,'#skF_4','#skF_1'(A_11,B_39,'#skF_5'))
      | ~ v1_funct_2(E_349,u1_struct_0('#skF_4'),u1_struct_0('#skF_1'(A_11,B_39,'#skF_5')))
      | ~ v1_funct_1(E_349)
      | ~ l1_pre_topc('#skF_1'(A_11,B_39,'#skF_5'))
      | ~ v2_pre_topc('#skF_1'(A_11,B_39,'#skF_5'))
      | v2_struct_0('#skF_1'(A_11,B_39,'#skF_5'))
      | r3_tsep_1(A_11,B_39,'#skF_5')
      | ~ r1_tsep_1(B_39,'#skF_5')
      | ~ m1_pre_topc('#skF_5',A_11)
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(B_39,A_11)
      | v2_struct_0(B_39)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(resolution,[status(thm)],[c_14,c_343])).

tff(c_352,plain,(
    ! [A_11,B_39,E_349] :
      ( v5_pre_topc(k10_tmap_1('#skF_3','#skF_1'(A_11,B_39,'#skF_5'),'#skF_4','#skF_5',E_349,k3_tmap_1(A_11,'#skF_1'(A_11,B_39,'#skF_5'),k1_tsep_1(A_11,B_39,'#skF_5'),'#skF_5','#skF_2'(A_11,B_39,'#skF_5'))),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_1'(A_11,B_39,'#skF_5'))
      | ~ v5_pre_topc(k3_tmap_1(A_11,'#skF_1'(A_11,B_39,'#skF_5'),k1_tsep_1(A_11,B_39,'#skF_5'),'#skF_5','#skF_2'(A_11,B_39,'#skF_5')),'#skF_5','#skF_1'(A_11,B_39,'#skF_5'))
      | ~ v1_funct_2(k3_tmap_1(A_11,'#skF_1'(A_11,B_39,'#skF_5'),k1_tsep_1(A_11,B_39,'#skF_5'),'#skF_5','#skF_2'(A_11,B_39,'#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'(A_11,B_39,'#skF_5')))
      | ~ v1_funct_1(k3_tmap_1(A_11,'#skF_1'(A_11,B_39,'#skF_5'),k1_tsep_1(A_11,B_39,'#skF_5'),'#skF_5','#skF_2'(A_11,B_39,'#skF_5')))
      | ~ m1_subset_1(E_349,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'(A_11,B_39,'#skF_5')))))
      | ~ v5_pre_topc(E_349,'#skF_4','#skF_1'(A_11,B_39,'#skF_5'))
      | ~ v1_funct_2(E_349,u1_struct_0('#skF_4'),u1_struct_0('#skF_1'(A_11,B_39,'#skF_5')))
      | ~ v1_funct_1(E_349)
      | ~ l1_pre_topc('#skF_1'(A_11,B_39,'#skF_5'))
      | ~ v2_pre_topc('#skF_1'(A_11,B_39,'#skF_5'))
      | v2_struct_0('#skF_1'(A_11,B_39,'#skF_5'))
      | r3_tsep_1(A_11,B_39,'#skF_5')
      | ~ r1_tsep_1(B_39,'#skF_5')
      | ~ m1_pre_topc('#skF_5',A_11)
      | ~ m1_pre_topc(B_39,A_11)
      | v2_struct_0(B_39)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_346])).

tff(c_831,plain,
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
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_787,c_352])).

tff(c_893,plain,
    ( v5_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_68,c_237,c_778,c_78,c_76,c_72,c_68,c_237,c_778,c_831])).

tff(c_894,plain,
    ( v5_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_70,c_240,c_893])).

tff(c_912,plain,(
    ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_894])).

tff(c_916,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_912])).

tff(c_919,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_68,c_237,c_916])).

tff(c_921,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_70,c_240,c_919])).

tff(c_923,plain,(
    l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_894])).

tff(c_28,plain,(
    ! [A_11,B_39,C_53] :
      ( v1_funct_1(k3_tmap_1(A_11,'#skF_1'(A_11,B_39,C_53),k1_tsep_1(A_11,B_39,C_53),B_39,'#skF_2'(A_11,B_39,C_53)))
      | r3_tsep_1(A_11,B_39,C_53)
      | ~ r1_tsep_1(B_39,C_53)
      | ~ m1_pre_topc(C_53,A_11)
      | v2_struct_0(C_53)
      | ~ m1_pre_topc(B_39,A_11)
      | v2_struct_0(B_39)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_16,plain,(
    ! [A_11,B_39,C_53] :
      ( v5_pre_topc(k3_tmap_1(A_11,'#skF_1'(A_11,B_39,C_53),k1_tsep_1(A_11,B_39,C_53),C_53,'#skF_2'(A_11,B_39,C_53)),C_53,'#skF_1'(A_11,B_39,C_53))
      | r3_tsep_1(A_11,B_39,C_53)
      | ~ r1_tsep_1(B_39,C_53)
      | ~ m1_pre_topc(C_53,A_11)
      | v2_struct_0(C_53)
      | ~ m1_pre_topc(B_39,A_11)
      | v2_struct_0(B_39)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_922,plain,
    ( ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v5_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_894])).

tff(c_924,plain,(
    ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_922])).

tff(c_940,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_924])).

tff(c_943,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_68,c_237,c_940])).

tff(c_945,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_70,c_240,c_943])).

tff(c_946,plain,
    ( ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | v5_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_922])).

tff(c_948,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_946])).

tff(c_954,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_948])).

tff(c_957,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_68,c_237,c_954])).

tff(c_959,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_70,c_240,c_957])).

tff(c_961,plain,(
    v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_946])).

tff(c_960,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v5_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_946])).

tff(c_962,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))))) ),
    inference(splitLeft,[status(thm)],[c_960])).

tff(c_978,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_962])).

tff(c_981,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_68,c_237,c_978])).

tff(c_983,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_70,c_240,c_981])).

tff(c_985,plain,(
    m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))))) ),
    inference(splitRight,[status(thm)],[c_960])).

tff(c_10,plain,(
    ! [B_6,C_7,E_9,D_8,A_5,F_10] :
      ( v1_funct_1(k10_tmap_1(A_5,B_6,C_7,D_8,E_9,F_10))
      | ~ m1_subset_1(F_10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_8),u1_struct_0(B_6))))
      | ~ v1_funct_2(F_10,u1_struct_0(D_8),u1_struct_0(B_6))
      | ~ v1_funct_1(F_10)
      | ~ m1_subset_1(E_9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_7),u1_struct_0(B_6))))
      | ~ v1_funct_2(E_9,u1_struct_0(C_7),u1_struct_0(B_6))
      | ~ v1_funct_1(E_9)
      | ~ m1_pre_topc(D_8,A_5)
      | v2_struct_0(D_8)
      | ~ m1_pre_topc(C_7,A_5)
      | v2_struct_0(C_7)
      | ~ l1_pre_topc(B_6)
      | ~ v2_pre_topc(B_6)
      | v2_struct_0(B_6)
      | ~ l1_pre_topc(A_5)
      | ~ v2_pre_topc(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_993,plain,(
    ! [A_5,C_7,E_9] :
      ( v1_funct_1(k10_tmap_1(A_5,'#skF_1'('#skF_3','#skF_4','#skF_5'),C_7,'#skF_4',E_9,k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5'))))
      | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
      | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(E_9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_7),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
      | ~ v1_funct_2(E_9,u1_struct_0(C_7),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
      | ~ v1_funct_1(E_9)
      | ~ m1_pre_topc('#skF_4',A_5)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_7,A_5)
      | v2_struct_0(C_7)
      | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ l1_pre_topc(A_5)
      | ~ v2_pre_topc(A_5)
      | v2_struct_0(A_5) ) ),
    inference(resolution,[status(thm)],[c_985,c_10])).

tff(c_1010,plain,(
    ! [A_5,C_7,E_9] :
      ( v1_funct_1(k10_tmap_1(A_5,'#skF_1'('#skF_3','#skF_4','#skF_5'),C_7,'#skF_4',E_9,k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5'))))
      | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(E_9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_7),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
      | ~ v1_funct_2(E_9,u1_struct_0(C_7),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
      | ~ v1_funct_1(E_9)
      | ~ m1_pre_topc('#skF_4',A_5)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_7,A_5)
      | v2_struct_0(C_7)
      | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ l1_pre_topc(A_5)
      | ~ v2_pre_topc(A_5)
      | v2_struct_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_778,c_923,c_961,c_993])).

tff(c_1011,plain,(
    ! [A_5,C_7,E_9] :
      ( v1_funct_1(k10_tmap_1(A_5,'#skF_1'('#skF_3','#skF_4','#skF_5'),C_7,'#skF_4',E_9,k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5'))))
      | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(E_9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_7),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
      | ~ v1_funct_2(E_9,u1_struct_0(C_7),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
      | ~ v1_funct_1(E_9)
      | ~ m1_pre_topc('#skF_4',A_5)
      | ~ m1_pre_topc(C_7,A_5)
      | v2_struct_0(C_7)
      | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ l1_pre_topc(A_5)
      | ~ v2_pre_topc(A_5)
      | v2_struct_0(A_5) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1010])).

tff(c_1063,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_1011])).

tff(c_1066,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_1063])).

tff(c_1069,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_68,c_237,c_1066])).

tff(c_1071,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_70,c_240,c_1069])).

tff(c_1072,plain,(
    ! [A_5,C_7,E_9] :
      ( v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | v1_funct_1(k10_tmap_1(A_5,'#skF_1'('#skF_3','#skF_4','#skF_5'),C_7,'#skF_4',E_9,k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5'))))
      | ~ m1_subset_1(E_9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_7),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
      | ~ v1_funct_2(E_9,u1_struct_0(C_7),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
      | ~ v1_funct_1(E_9)
      | ~ m1_pre_topc('#skF_4',A_5)
      | ~ m1_pre_topc(C_7,A_5)
      | v2_struct_0(C_7)
      | ~ l1_pre_topc(A_5)
      | ~ v2_pre_topc(A_5)
      | v2_struct_0(A_5) ) ),
    inference(splitRight,[status(thm)],[c_1011])).

tff(c_1081,plain,(
    v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1072])).

tff(c_40,plain,(
    ! [A_11,B_39,C_53] :
      ( ~ v2_struct_0('#skF_1'(A_11,B_39,C_53))
      | r3_tsep_1(A_11,B_39,C_53)
      | ~ r1_tsep_1(B_39,C_53)
      | ~ m1_pre_topc(C_53,A_11)
      | v2_struct_0(C_53)
      | ~ m1_pre_topc(B_39,A_11)
      | v2_struct_0(B_39)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1087,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1081,c_40])).

tff(c_1090,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_68,c_237,c_1087])).

tff(c_1092,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_70,c_240,c_1090])).

tff(c_1094,plain,(
    ~ v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1072])).

tff(c_947,plain,(
    v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_922])).

tff(c_24,plain,(
    ! [A_11,B_39,C_53] :
      ( v5_pre_topc(k3_tmap_1(A_11,'#skF_1'(A_11,B_39,C_53),k1_tsep_1(A_11,B_39,C_53),B_39,'#skF_2'(A_11,B_39,C_53)),B_39,'#skF_1'(A_11,B_39,C_53))
      | r3_tsep_1(A_11,B_39,C_53)
      | ~ r1_tsep_1(B_39,C_53)
      | ~ m1_pre_topc(C_53,A_11)
      | v2_struct_0(C_53)
      | ~ m1_pre_topc(B_39,A_11)
      | v2_struct_0(B_39)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_2,plain,(
    ! [A_1,B_2,D_4] :
      ( r2_funct_2(A_1,B_2,D_4,D_4)
      | ~ m1_subset_1(D_4,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(D_4,A_1,B_2)
      | ~ v1_funct_1(D_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_995,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_985,c_2])).

tff(c_1014,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_961,c_995])).

tff(c_1015,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_1014])).

tff(c_1055,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_1015])).

tff(c_1058,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_68,c_237,c_1055])).

tff(c_1060,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_70,c_240,c_1058])).

tff(c_1062,plain,(
    v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_1014])).

tff(c_56,plain,(
    ! [A_95,C_143,E_155,F_157,D_151,B_127] :
      ( v5_pre_topc(k10_tmap_1(A_95,B_127,C_143,D_151,E_155,F_157),k1_tsep_1(A_95,C_143,D_151),B_127)
      | ~ r4_tsep_1(A_95,C_143,D_151)
      | ~ m1_subset_1(F_157,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_151),u1_struct_0(B_127))))
      | ~ v5_pre_topc(F_157,D_151,B_127)
      | ~ v1_funct_2(F_157,u1_struct_0(D_151),u1_struct_0(B_127))
      | ~ v1_funct_1(F_157)
      | ~ m1_subset_1(E_155,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_143),u1_struct_0(B_127))))
      | ~ v5_pre_topc(E_155,C_143,B_127)
      | ~ v1_funct_2(E_155,u1_struct_0(C_143),u1_struct_0(B_127))
      | ~ v1_funct_1(E_155)
      | ~ r1_tsep_1(C_143,D_151)
      | ~ m1_pre_topc(D_151,A_95)
      | v2_struct_0(D_151)
      | ~ m1_pre_topc(C_143,A_95)
      | v2_struct_0(C_143)
      | ~ l1_pre_topc(B_127)
      | ~ v2_pre_topc(B_127)
      | v2_struct_0(B_127)
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_991,plain,(
    ! [A_95,C_143,E_155] :
      ( v5_pre_topc(k10_tmap_1(A_95,'#skF_1'('#skF_3','#skF_4','#skF_5'),C_143,'#skF_4',E_155,k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5'))),k1_tsep_1(A_95,C_143,'#skF_4'),'#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ r4_tsep_1(A_95,C_143,'#skF_4')
      | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
      | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(E_155,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_143),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
      | ~ v5_pre_topc(E_155,C_143,'#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ v1_funct_2(E_155,u1_struct_0(C_143),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
      | ~ v1_funct_1(E_155)
      | ~ r1_tsep_1(C_143,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_95)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_143,A_95)
      | v2_struct_0(C_143)
      | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95)
      | v2_struct_0(A_95) ) ),
    inference(resolution,[status(thm)],[c_985,c_56])).

tff(c_1006,plain,(
    ! [A_95,C_143,E_155] :
      ( v5_pre_topc(k10_tmap_1(A_95,'#skF_1'('#skF_3','#skF_4','#skF_5'),C_143,'#skF_4',E_155,k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5'))),k1_tsep_1(A_95,C_143,'#skF_4'),'#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ r4_tsep_1(A_95,C_143,'#skF_4')
      | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(E_155,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_143),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
      | ~ v5_pre_topc(E_155,C_143,'#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ v1_funct_2(E_155,u1_struct_0(C_143),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
      | ~ v1_funct_1(E_155)
      | ~ r1_tsep_1(C_143,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_95)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_143,A_95)
      | v2_struct_0(C_143)
      | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95)
      | v2_struct_0(A_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_778,c_923,c_961,c_991])).

tff(c_1007,plain,(
    ! [A_95,C_143,E_155] :
      ( v5_pre_topc(k10_tmap_1(A_95,'#skF_1'('#skF_3','#skF_4','#skF_5'),C_143,'#skF_4',E_155,k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5'))),k1_tsep_1(A_95,C_143,'#skF_4'),'#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ r4_tsep_1(A_95,C_143,'#skF_4')
      | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(E_155,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_143),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
      | ~ v5_pre_topc(E_155,C_143,'#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ v1_funct_2(E_155,u1_struct_0(C_143),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
      | ~ v1_funct_1(E_155)
      | ~ r1_tsep_1(C_143,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_95)
      | ~ m1_pre_topc(C_143,A_95)
      | v2_struct_0(C_143)
      | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95)
      | v2_struct_0(A_95) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1006])).

tff(c_1097,plain,(
    ! [A_95,C_143,E_155] :
      ( v5_pre_topc(k10_tmap_1(A_95,'#skF_1'('#skF_3','#skF_4','#skF_5'),C_143,'#skF_4',E_155,k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5'))),k1_tsep_1(A_95,C_143,'#skF_4'),'#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ r4_tsep_1(A_95,C_143,'#skF_4')
      | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(E_155,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_143),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
      | ~ v5_pre_topc(E_155,C_143,'#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ v1_funct_2(E_155,u1_struct_0(C_143),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
      | ~ v1_funct_1(E_155)
      | ~ r1_tsep_1(C_143,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_95)
      | ~ m1_pre_topc(C_143,A_95)
      | v2_struct_0(C_143)
      | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95)
      | v2_struct_0(A_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1062,c_1007])).

tff(c_1098,plain,(
    ! [A_95,C_143,E_155] :
      ( v5_pre_topc(k10_tmap_1(A_95,'#skF_1'('#skF_3','#skF_4','#skF_5'),C_143,'#skF_4',E_155,k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5'))),k1_tsep_1(A_95,C_143,'#skF_4'),'#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ r4_tsep_1(A_95,C_143,'#skF_4')
      | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(E_155,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_143),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
      | ~ v5_pre_topc(E_155,C_143,'#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ v1_funct_2(E_155,u1_struct_0(C_143),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
      | ~ v1_funct_1(E_155)
      | ~ r1_tsep_1(C_143,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_95)
      | ~ m1_pre_topc(C_143,A_95)
      | v2_struct_0(C_143)
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95)
      | v2_struct_0(A_95) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1094,c_1097])).

tff(c_1099,plain,(
    ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1098])).

tff(c_1102,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_1099])).

tff(c_1105,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_68,c_237,c_1102])).

tff(c_1107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_70,c_240,c_1105])).

tff(c_1109,plain,(
    v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1098])).

tff(c_777,plain,
    ( ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_5',k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))) = '#skF_2'('#skF_3','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_739])).

tff(c_1126,plain,
    ( ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_5',k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))) = '#skF_2'('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_947,c_985,c_1109,c_1062,c_961,c_923,c_777])).

tff(c_1127,plain,
    ( ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_5',k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))) = '#skF_2'('#skF_3','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_1094,c_1126])).

tff(c_1128,plain,(
    ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))))) ),
    inference(splitLeft,[status(thm)],[c_1127])).

tff(c_1131,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_1128])).

tff(c_1134,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_68,c_237,c_1131])).

tff(c_1136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_70,c_240,c_1134])).

tff(c_1138,plain,(
    m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))))) ),
    inference(splitRight,[status(thm)],[c_1127])).

tff(c_1176,plain,
    ( r2_funct_2(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_1138,c_2])).

tff(c_1177,plain,(
    ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1176])).

tff(c_1180,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_1177])).

tff(c_1183,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_68,c_237,c_1180])).

tff(c_1185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_70,c_240,c_1183])).

tff(c_1187,plain,(
    v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1176])).

tff(c_20,plain,(
    ! [A_11,B_39,C_53] :
      ( v1_funct_1(k3_tmap_1(A_11,'#skF_1'(A_11,B_39,C_53),k1_tsep_1(A_11,B_39,C_53),C_53,'#skF_2'(A_11,B_39,C_53)))
      | r3_tsep_1(A_11,B_39,C_53)
      | ~ r1_tsep_1(B_39,C_53)
      | ~ m1_pre_topc(C_53,A_11)
      | v2_struct_0(C_53)
      | ~ m1_pre_topc(B_39,A_11)
      | v2_struct_0(B_39)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_984,plain,
    ( ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | v5_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_960])).

tff(c_1112,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | v5_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1062,c_1109,c_984])).

tff(c_1113,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | v5_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_1094,c_1112])).

tff(c_1114,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_1113])).

tff(c_1117,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_1114])).

tff(c_1120,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_68,c_237,c_1117])).

tff(c_1122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_70,c_240,c_1120])).

tff(c_1124,plain,(
    v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_1113])).

tff(c_32,plain,(
    ! [A_11,B_39,C_53] :
      ( v1_funct_2('#skF_2'(A_11,B_39,C_53),u1_struct_0(k1_tsep_1(A_11,B_39,C_53)),u1_struct_0('#skF_1'(A_11,B_39,C_53)))
      | r3_tsep_1(A_11,B_39,C_53)
      | ~ r1_tsep_1(B_39,C_53)
      | ~ m1_pre_topc(C_53,A_11)
      | v2_struct_0(C_53)
      | ~ m1_pre_topc(B_39,A_11)
      | v2_struct_0(B_39)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1186,plain,
    ( ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | r2_funct_2(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')),'#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_2'('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1176])).

tff(c_1188,plain,(
    ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_1186])).

tff(c_1195,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_1188])).

tff(c_1198,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_68,c_237,c_1195])).

tff(c_1200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_70,c_240,c_1198])).

tff(c_1202,plain,(
    v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_1186])).

tff(c_645,plain,(
    ! [D_271,E_537] :
      ( k10_tmap_1('#skF_3',D_271,'#skF_4','#skF_5',k3_tmap_1('#skF_3',D_271,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_537),k3_tmap_1('#skF_3',D_271,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_537)) = E_537
      | ~ v1_funct_1(k10_tmap_1('#skF_3',D_271,'#skF_4','#skF_5',k3_tmap_1('#skF_3',D_271,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_537),k3_tmap_1('#skF_3',D_271,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_537)))
      | ~ m1_subset_1(E_537,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0(D_271))))
      | ~ v1_funct_2(E_537,u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0(D_271))
      | ~ v1_funct_1(E_537)
      | ~ m1_subset_1(k3_tmap_1('#skF_3',D_271,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_537),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(D_271))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_3',D_271,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_537),'#skF_5',D_271)
      | ~ v1_funct_2(k3_tmap_1('#skF_3',D_271,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_537),u1_struct_0('#skF_5'),u1_struct_0(D_271))
      | ~ v1_funct_1(k3_tmap_1('#skF_3',D_271,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5',E_537))
      | ~ m1_subset_1(k3_tmap_1('#skF_3',D_271,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_537),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(D_271))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_3',D_271,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_537),'#skF_4',D_271)
      | ~ v1_funct_2(k3_tmap_1('#skF_3',D_271,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_537),u1_struct_0('#skF_4'),u1_struct_0(D_271))
      | ~ v1_funct_1(k3_tmap_1('#skF_3',D_271,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4',E_537))
      | ~ l1_pre_topc(D_271)
      | ~ v2_pre_topc(D_271)
      | v2_struct_0(D_271) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_70,c_644])).

tff(c_808,plain,
    ( k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_5',k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))) = '#skF_2'('#skF_3','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
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
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_787,c_645])).

tff(c_889,plain,
    ( k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_5',k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))) = '#skF_2'('#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_68,c_237,c_778,c_778,c_808])).

tff(c_890,plain,
    ( k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_5',k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))) = '#skF_2'('#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_70,c_240,c_889])).

tff(c_1210,plain,
    ( k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_5',k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))) = '#skF_2'('#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_923,c_961,c_1062,c_1124,c_1187,c_1202,c_1138,c_1109,c_985,c_947,c_890])).

tff(c_1211,plain,
    ( k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_5',k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))) = '#skF_2'('#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1094,c_1210])).

tff(c_1212,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_1211])).

tff(c_1215,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_1212])).

tff(c_1218,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_68,c_237,c_1215])).

tff(c_1220,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_70,c_240,c_1218])).

tff(c_1222,plain,(
    v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_1211])).

tff(c_1221,plain,
    ( ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_5',k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))) = '#skF_2'('#skF_3','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_1211])).

tff(c_1223,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))))) ),
    inference(splitLeft,[status(thm)],[c_1221])).

tff(c_1226,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_1223])).

tff(c_1229,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_68,c_237,c_1226])).

tff(c_1231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_70,c_240,c_1229])).

tff(c_1233,plain,(
    m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))))) ),
    inference(splitRight,[status(thm)],[c_1221])).

tff(c_728,plain,
    ( k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_5',k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))) = '#skF_2'('#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_599,c_725])).

tff(c_734,plain,
    ( k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_5',k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))) = '#skF_2'('#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_68,c_237,c_728])).

tff(c_735,plain,
    ( k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_5',k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))) = '#skF_2'('#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2('#skF_2'('#skF_3','#skF_4','#skF_5'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_2'('#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_5'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v5_pre_topc(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ m1_subset_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4'),u1_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')))
    | ~ l1_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_70,c_240,c_734])).

tff(c_1282,plain,
    ( k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_5',k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))) = '#skF_2'('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_778,c_923,c_961,c_1062,c_985,c_1124,c_1109,c_1222,c_947,c_1233,c_1187,c_1202,c_1138,c_735])).

tff(c_1283,plain,(
    k10_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_5',k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4','#skF_2'('#skF_3','#skF_4','#skF_5')),k3_tmap_1('#skF_3','#skF_1'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))) = '#skF_2'('#skF_3','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_1094,c_1282])).

tff(c_1321,plain,
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
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1283,c_352])).

tff(c_1401,plain,
    ( v5_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_1'('#skF_3','#skF_4','#skF_5'))
    | v2_struct_0('#skF_1'('#skF_3','#skF_4','#skF_5'))
    | r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_68,c_237,c_778,c_923,c_961,c_1062,c_1109,c_985,c_1124,c_1222,c_947,c_1321])).

tff(c_1402,plain,(
    v5_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_240,c_1094,c_1401])).

tff(c_440,plain,(
    ! [A_369,B_370,C_371] :
      ( ~ m1_subset_1('#skF_2'(A_369,B_370,C_371),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_369,B_370,C_371)),u1_struct_0('#skF_1'(A_369,B_370,C_371)))))
      | ~ v5_pre_topc('#skF_2'(A_369,B_370,C_371),k1_tsep_1(A_369,B_370,C_371),'#skF_1'(A_369,B_370,C_371))
      | ~ v1_funct_2('#skF_2'(A_369,B_370,C_371),u1_struct_0(k1_tsep_1(A_369,B_370,C_371)),u1_struct_0('#skF_1'(A_369,B_370,C_371)))
      | ~ v1_funct_1('#skF_2'(A_369,B_370,C_371))
      | r3_tsep_1(A_369,B_370,C_371)
      | ~ r1_tsep_1(B_370,C_371)
      | ~ m1_pre_topc(C_371,A_369)
      | v2_struct_0(C_371)
      | ~ m1_pre_topc(B_370,A_369)
      | v2_struct_0(B_370)
      | ~ l1_pre_topc(A_369)
      | ~ v2_pre_topc(A_369)
      | v2_struct_0(A_369) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_445,plain,(
    ! [A_372,B_373,C_374] :
      ( ~ v5_pre_topc('#skF_2'(A_372,B_373,C_374),k1_tsep_1(A_372,B_373,C_374),'#skF_1'(A_372,B_373,C_374))
      | ~ v1_funct_2('#skF_2'(A_372,B_373,C_374),u1_struct_0(k1_tsep_1(A_372,B_373,C_374)),u1_struct_0('#skF_1'(A_372,B_373,C_374)))
      | ~ v1_funct_1('#skF_2'(A_372,B_373,C_374))
      | r3_tsep_1(A_372,B_373,C_374)
      | ~ r1_tsep_1(B_373,C_374)
      | ~ m1_pre_topc(C_374,A_372)
      | v2_struct_0(C_374)
      | ~ m1_pre_topc(B_373,A_372)
      | v2_struct_0(B_373)
      | ~ l1_pre_topc(A_372)
      | ~ v2_pre_topc(A_372)
      | v2_struct_0(A_372) ) ),
    inference(resolution,[status(thm)],[c_30,c_440])).

tff(c_449,plain,(
    ! [A_11,B_39,C_53] :
      ( ~ v5_pre_topc('#skF_2'(A_11,B_39,C_53),k1_tsep_1(A_11,B_39,C_53),'#skF_1'(A_11,B_39,C_53))
      | ~ v1_funct_1('#skF_2'(A_11,B_39,C_53))
      | r3_tsep_1(A_11,B_39,C_53)
      | ~ r1_tsep_1(B_39,C_53)
      | ~ m1_pre_topc(C_53,A_11)
      | v2_struct_0(C_53)
      | ~ m1_pre_topc(B_39,A_11)
      | v2_struct_0(B_39)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(resolution,[status(thm)],[c_32,c_445])).

tff(c_1446,plain,
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
    inference(resolution,[status(thm)],[c_1402,c_449])).

tff(c_1449,plain,
    ( r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_68,c_237,c_1187,c_1446])).

tff(c_1451,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_70,c_240,c_1449])).

tff(c_1453,plain,(
    r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_239])).

tff(c_64,plain,(
    ! [A_158,B_162,C_164] :
      ( r4_tsep_1(A_158,B_162,C_164)
      | ~ r3_tsep_1(A_158,B_162,C_164)
      | ~ m1_pre_topc(C_164,A_158)
      | v2_struct_0(C_164)
      | ~ m1_pre_topc(B_162,A_158)
      | v2_struct_0(B_162)
      | ~ l1_pre_topc(A_158)
      | ~ v2_pre_topc(A_158)
      | v2_struct_0(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_100,plain,
    ( v1_funct_1('#skF_7')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_321])).

tff(c_1457,plain,(
    v1_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1453,c_237,c_100])).

tff(c_98,plain,
    ( v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_6'))
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_321])).

tff(c_1469,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1453,c_237,c_98])).

tff(c_96,plain,
    ( v5_pre_topc('#skF_7','#skF_4','#skF_6')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_321])).

tff(c_1463,plain,(
    v5_pre_topc('#skF_7','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1453,c_237,c_96])).

tff(c_94,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_6'))))
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_321])).

tff(c_1471,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_6')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1453,c_237,c_94])).

tff(c_106,plain,
    ( ~ v2_struct_0('#skF_6')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_321])).

tff(c_1461,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1453,c_237,c_106])).

tff(c_104,plain,
    ( v2_pre_topc('#skF_6')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_321])).

tff(c_1459,plain,(
    v2_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1453,c_237,c_104])).

tff(c_102,plain,
    ( l1_pre_topc('#skF_6')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_321])).

tff(c_1455,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1453,c_237,c_102])).

tff(c_1452,plain,(
    v1_funct_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_239])).

tff(c_90,plain,
    ( v1_funct_2('#skF_8',u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_321])).

tff(c_1467,plain,(
    v1_funct_2('#skF_8',u1_struct_0('#skF_5'),u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1453,c_237,c_90])).

tff(c_88,plain,
    ( v5_pre_topc('#skF_8','#skF_5','#skF_6')
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_321])).

tff(c_1465,plain,(
    v5_pre_topc('#skF_8','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1453,c_237,c_88])).

tff(c_86,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))))
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_321])).

tff(c_1473,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1453,c_237,c_86])).

tff(c_2106,plain,(
    ! [F_782,D_779,B_784,A_783,E_780,C_781] :
      ( v5_pre_topc(k10_tmap_1(A_783,B_784,C_781,D_779,E_780,F_782),k1_tsep_1(A_783,C_781,D_779),B_784)
      | ~ r4_tsep_1(A_783,C_781,D_779)
      | ~ m1_subset_1(F_782,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_779),u1_struct_0(B_784))))
      | ~ v5_pre_topc(F_782,D_779,B_784)
      | ~ v1_funct_2(F_782,u1_struct_0(D_779),u1_struct_0(B_784))
      | ~ v1_funct_1(F_782)
      | ~ m1_subset_1(E_780,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_781),u1_struct_0(B_784))))
      | ~ v5_pre_topc(E_780,C_781,B_784)
      | ~ v1_funct_2(E_780,u1_struct_0(C_781),u1_struct_0(B_784))
      | ~ v1_funct_1(E_780)
      | ~ r1_tsep_1(C_781,D_779)
      | ~ m1_pre_topc(D_779,A_783)
      | v2_struct_0(D_779)
      | ~ m1_pre_topc(C_781,A_783)
      | v2_struct_0(C_781)
      | ~ l1_pre_topc(B_784)
      | ~ v2_pre_topc(B_784)
      | v2_struct_0(B_784)
      | ~ l1_pre_topc(A_783)
      | ~ v2_pre_topc(A_783)
      | v2_struct_0(A_783) ) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_2118,plain,(
    ! [A_783,C_781,E_780] :
      ( v5_pre_topc(k10_tmap_1(A_783,'#skF_6',C_781,'#skF_5',E_780,'#skF_8'),k1_tsep_1(A_783,C_781,'#skF_5'),'#skF_6')
      | ~ r4_tsep_1(A_783,C_781,'#skF_5')
      | ~ v5_pre_topc('#skF_8','#skF_5','#skF_6')
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_780,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_781),u1_struct_0('#skF_6'))))
      | ~ v5_pre_topc(E_780,C_781,'#skF_6')
      | ~ v1_funct_2(E_780,u1_struct_0(C_781),u1_struct_0('#skF_6'))
      | ~ v1_funct_1(E_780)
      | ~ r1_tsep_1(C_781,'#skF_5')
      | ~ m1_pre_topc('#skF_5',A_783)
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(C_781,A_783)
      | v2_struct_0(C_781)
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc(A_783)
      | ~ v2_pre_topc(A_783)
      | v2_struct_0(A_783) ) ),
    inference(resolution,[status(thm)],[c_1473,c_2106])).

tff(c_2131,plain,(
    ! [A_783,C_781,E_780] :
      ( v5_pre_topc(k10_tmap_1(A_783,'#skF_6',C_781,'#skF_5',E_780,'#skF_8'),k1_tsep_1(A_783,C_781,'#skF_5'),'#skF_6')
      | ~ r4_tsep_1(A_783,C_781,'#skF_5')
      | ~ m1_subset_1(E_780,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_781),u1_struct_0('#skF_6'))))
      | ~ v5_pre_topc(E_780,C_781,'#skF_6')
      | ~ v1_funct_2(E_780,u1_struct_0(C_781),u1_struct_0('#skF_6'))
      | ~ v1_funct_1(E_780)
      | ~ r1_tsep_1(C_781,'#skF_5')
      | ~ m1_pre_topc('#skF_5',A_783)
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(C_781,A_783)
      | v2_struct_0(C_781)
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc(A_783)
      | ~ v2_pre_topc(A_783)
      | v2_struct_0(A_783) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1459,c_1455,c_1452,c_1467,c_1465,c_2118])).

tff(c_2139,plain,(
    ! [A_785,C_786,E_787] :
      ( v5_pre_topc(k10_tmap_1(A_785,'#skF_6',C_786,'#skF_5',E_787,'#skF_8'),k1_tsep_1(A_785,C_786,'#skF_5'),'#skF_6')
      | ~ r4_tsep_1(A_785,C_786,'#skF_5')
      | ~ m1_subset_1(E_787,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_786),u1_struct_0('#skF_6'))))
      | ~ v5_pre_topc(E_787,C_786,'#skF_6')
      | ~ v1_funct_2(E_787,u1_struct_0(C_786),u1_struct_0('#skF_6'))
      | ~ v1_funct_1(E_787)
      | ~ r1_tsep_1(C_786,'#skF_5')
      | ~ m1_pre_topc('#skF_5',A_785)
      | ~ m1_pre_topc(C_786,A_785)
      | v2_struct_0(C_786)
      | ~ l1_pre_topc(A_785)
      | ~ v2_pre_topc(A_785)
      | v2_struct_0(A_785) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1461,c_70,c_2131])).

tff(c_2148,plain,(
    ! [A_785] :
      ( v5_pre_topc(k10_tmap_1(A_785,'#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),k1_tsep_1(A_785,'#skF_4','#skF_5'),'#skF_6')
      | ~ r4_tsep_1(A_785,'#skF_4','#skF_5')
      | ~ v5_pre_topc('#skF_7','#skF_4','#skF_6')
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_6'))
      | ~ v1_funct_1('#skF_7')
      | ~ r1_tsep_1('#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5',A_785)
      | ~ m1_pre_topc('#skF_4',A_785)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_785)
      | ~ v2_pre_topc(A_785)
      | v2_struct_0(A_785) ) ),
    inference(resolution,[status(thm)],[c_1471,c_2139])).

tff(c_2162,plain,(
    ! [A_785] :
      ( v5_pre_topc(k10_tmap_1(A_785,'#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),k1_tsep_1(A_785,'#skF_4','#skF_5'),'#skF_6')
      | ~ r4_tsep_1(A_785,'#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5',A_785)
      | ~ m1_pre_topc('#skF_4',A_785)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_785)
      | ~ v2_pre_topc(A_785)
      | v2_struct_0(A_785) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_1457,c_1469,c_1463,c_2148])).

tff(c_2165,plain,(
    ! [A_788] :
      ( v5_pre_topc(k10_tmap_1(A_788,'#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),k1_tsep_1(A_788,'#skF_4','#skF_5'),'#skF_6')
      | ~ r4_tsep_1(A_788,'#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5',A_788)
      | ~ m1_pre_topc('#skF_4',A_788)
      | ~ l1_pre_topc(A_788)
      | ~ v2_pre_topc(A_788)
      | v2_struct_0(A_788) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2162])).

tff(c_1894,plain,(
    ! [C_731,F_729,E_733,A_732,B_730,D_728] :
      ( v1_funct_2(k10_tmap_1(A_732,B_730,C_731,D_728,E_733,F_729),u1_struct_0(k1_tsep_1(A_732,C_731,D_728)),u1_struct_0(B_730))
      | ~ m1_subset_1(F_729,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_728),u1_struct_0(B_730))))
      | ~ v1_funct_2(F_729,u1_struct_0(D_728),u1_struct_0(B_730))
      | ~ v1_funct_1(F_729)
      | ~ m1_subset_1(E_733,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_731),u1_struct_0(B_730))))
      | ~ v1_funct_2(E_733,u1_struct_0(C_731),u1_struct_0(B_730))
      | ~ v1_funct_1(E_733)
      | ~ m1_pre_topc(D_728,A_732)
      | v2_struct_0(D_728)
      | ~ m1_pre_topc(C_731,A_732)
      | v2_struct_0(C_731)
      | ~ l1_pre_topc(B_730)
      | ~ v2_pre_topc(B_730)
      | v2_struct_0(B_730)
      | ~ l1_pre_topc(A_732)
      | ~ v2_pre_topc(A_732)
      | v2_struct_0(A_732) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1728,plain,(
    ! [C_706,F_704,E_708,D_703,A_707,B_705] :
      ( m1_subset_1(k10_tmap_1(A_707,B_705,C_706,D_703,E_708,F_704),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_707,C_706,D_703)),u1_struct_0(B_705))))
      | ~ m1_subset_1(F_704,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_703),u1_struct_0(B_705))))
      | ~ v1_funct_2(F_704,u1_struct_0(D_703),u1_struct_0(B_705))
      | ~ v1_funct_1(F_704)
      | ~ m1_subset_1(E_708,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_706),u1_struct_0(B_705))))
      | ~ v1_funct_2(E_708,u1_struct_0(C_706),u1_struct_0(B_705))
      | ~ v1_funct_1(E_708)
      | ~ m1_pre_topc(D_703,A_707)
      | v2_struct_0(D_703)
      | ~ m1_pre_topc(C_706,A_707)
      | v2_struct_0(C_706)
      | ~ l1_pre_topc(B_705)
      | ~ v2_pre_topc(B_705)
      | v2_struct_0(B_705)
      | ~ l1_pre_topc(A_707)
      | ~ v2_pre_topc(A_707)
      | v2_struct_0(A_707) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1553,plain,(
    ! [D_667,E_672,C_670,A_671,B_669,F_668] :
      ( v1_funct_1(k10_tmap_1(A_671,B_669,C_670,D_667,E_672,F_668))
      | ~ m1_subset_1(F_668,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_667),u1_struct_0(B_669))))
      | ~ v1_funct_2(F_668,u1_struct_0(D_667),u1_struct_0(B_669))
      | ~ v1_funct_1(F_668)
      | ~ m1_subset_1(E_672,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_670),u1_struct_0(B_669))))
      | ~ v1_funct_2(E_672,u1_struct_0(C_670),u1_struct_0(B_669))
      | ~ v1_funct_1(E_672)
      | ~ m1_pre_topc(D_667,A_671)
      | v2_struct_0(D_667)
      | ~ m1_pre_topc(C_670,A_671)
      | v2_struct_0(C_670)
      | ~ l1_pre_topc(B_669)
      | ~ v2_pre_topc(B_669)
      | v2_struct_0(B_669)
      | ~ l1_pre_topc(A_671)
      | ~ v2_pre_topc(A_671)
      | v2_struct_0(A_671) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1561,plain,(
    ! [A_671,C_670,E_672] :
      ( v1_funct_1(k10_tmap_1(A_671,'#skF_6',C_670,'#skF_5',E_672,'#skF_8'))
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(E_672,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_670),u1_struct_0('#skF_6'))))
      | ~ v1_funct_2(E_672,u1_struct_0(C_670),u1_struct_0('#skF_6'))
      | ~ v1_funct_1(E_672)
      | ~ m1_pre_topc('#skF_5',A_671)
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(C_670,A_671)
      | v2_struct_0(C_670)
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc(A_671)
      | ~ v2_pre_topc(A_671)
      | v2_struct_0(A_671) ) ),
    inference(resolution,[status(thm)],[c_1473,c_1553])).

tff(c_1569,plain,(
    ! [A_671,C_670,E_672] :
      ( v1_funct_1(k10_tmap_1(A_671,'#skF_6',C_670,'#skF_5',E_672,'#skF_8'))
      | ~ m1_subset_1(E_672,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_670),u1_struct_0('#skF_6'))))
      | ~ v1_funct_2(E_672,u1_struct_0(C_670),u1_struct_0('#skF_6'))
      | ~ v1_funct_1(E_672)
      | ~ m1_pre_topc('#skF_5',A_671)
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(C_670,A_671)
      | v2_struct_0(C_670)
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc(A_671)
      | ~ v2_pre_topc(A_671)
      | v2_struct_0(A_671) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1459,c_1455,c_1452,c_1467,c_1561])).

tff(c_1575,plain,(
    ! [A_673,C_674,E_675] :
      ( v1_funct_1(k10_tmap_1(A_673,'#skF_6',C_674,'#skF_5',E_675,'#skF_8'))
      | ~ m1_subset_1(E_675,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_674),u1_struct_0('#skF_6'))))
      | ~ v1_funct_2(E_675,u1_struct_0(C_674),u1_struct_0('#skF_6'))
      | ~ v1_funct_1(E_675)
      | ~ m1_pre_topc('#skF_5',A_673)
      | ~ m1_pre_topc(C_674,A_673)
      | v2_struct_0(C_674)
      | ~ l1_pre_topc(A_673)
      | ~ v2_pre_topc(A_673)
      | v2_struct_0(A_673) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1461,c_70,c_1569])).

tff(c_1579,plain,(
    ! [A_673] :
      ( v1_funct_1(k10_tmap_1(A_673,'#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'))
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_6'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_pre_topc('#skF_5',A_673)
      | ~ m1_pre_topc('#skF_4',A_673)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_673)
      | ~ v2_pre_topc(A_673)
      | v2_struct_0(A_673) ) ),
    inference(resolution,[status(thm)],[c_1471,c_1575])).

tff(c_1586,plain,(
    ! [A_673] :
      ( v1_funct_1(k10_tmap_1(A_673,'#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'))
      | ~ m1_pre_topc('#skF_5',A_673)
      | ~ m1_pre_topc('#skF_4',A_673)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_673)
      | ~ v2_pre_topc(A_673)
      | v2_struct_0(A_673) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1457,c_1469,c_1579])).

tff(c_1589,plain,(
    ! [A_677] :
      ( v1_funct_1(k10_tmap_1(A_677,'#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'))
      | ~ m1_pre_topc('#skF_5',A_677)
      | ~ m1_pre_topc('#skF_4',A_677)
      | ~ l1_pre_topc(A_677)
      | ~ v2_pre_topc(A_677)
      | v2_struct_0(A_677) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1586])).

tff(c_84,plain,
    ( ~ m1_subset_1(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_6'))))
    | ~ v5_pre_topc(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_6')
    | ~ v1_funct_2(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_6'))
    | ~ v1_funct_1(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'))
    | ~ r1_tsep_1('#skF_4','#skF_5')
    | ~ r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_321])).

tff(c_1547,plain,
    ( ~ m1_subset_1(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_6'))))
    | ~ v5_pre_topc(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_6')
    | ~ v1_funct_2(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_6'))
    | ~ v1_funct_1(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1453,c_237,c_84])).

tff(c_1548,plain,(
    ~ v1_funct_1(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_1547])).

tff(c_1592,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1589,c_1548])).

tff(c_1595,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_68,c_1592])).

tff(c_1597,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1595])).

tff(c_1598,plain,
    ( ~ v1_funct_2(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_6'))
    | ~ v5_pre_topc(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_6')
    | ~ m1_subset_1(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_6')))) ),
    inference(splitRight,[status(thm)],[c_1547])).

tff(c_1600,plain,(
    ~ m1_subset_1(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_6')))) ),
    inference(splitLeft,[status(thm)],[c_1598])).

tff(c_1739,plain,
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
    inference(resolution,[status(thm)],[c_1728,c_1600])).

tff(c_1753,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1459,c_1455,c_72,c_68,c_1457,c_1469,c_1471,c_1452,c_1467,c_1473,c_1739])).

tff(c_1755,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1461,c_74,c_70,c_1753])).

tff(c_1756,plain,
    ( ~ v5_pre_topc(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_6')
    | ~ v1_funct_2(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1598])).

tff(c_1763,plain,(
    ~ v1_funct_2(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1756])).

tff(c_1897,plain,
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
    inference(resolution,[status(thm)],[c_1894,c_1763])).

tff(c_1900,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1459,c_1455,c_72,c_68,c_1457,c_1469,c_1471,c_1452,c_1467,c_1473,c_1897])).

tff(c_1902,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1461,c_74,c_70,c_1900])).

tff(c_1903,plain,(
    ~ v5_pre_topc(k10_tmap_1('#skF_3','#skF_6','#skF_4','#skF_5','#skF_7','#skF_8'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1756])).

tff(c_2168,plain,
    ( ~ r4_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2165,c_1903])).

tff(c_2171,plain,
    ( ~ r4_tsep_1('#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_68,c_2168])).

tff(c_2172,plain,(
    ~ r4_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2171])).

tff(c_2175,plain,
    ( ~ r3_tsep_1('#skF_3','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_2172])).

tff(c_2178,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_68,c_1453,c_2175])).

tff(c_2180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_70,c_2178])).

tff(c_2182,plain,(
    ~ r1_tsep_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_212])).

tff(c_2181,plain,(
    r3_tsep_1('#skF_3','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_212])).

tff(c_2207,plain,(
    ! [B_792,C_793,A_794] :
      ( r1_tsep_1(B_792,C_793)
      | ~ r3_tsep_1(A_794,B_792,C_793)
      | ~ m1_pre_topc(C_793,A_794)
      | v2_struct_0(C_793)
      | ~ m1_pre_topc(B_792,A_794)
      | v2_struct_0(B_792)
      | ~ l1_pre_topc(A_794)
      | ~ v2_pre_topc(A_794)
      | v2_struct_0(A_794) ) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_2210,plain,
    ( r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2181,c_2207])).

tff(c_2213,plain,
    ( r1_tsep_1('#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_68,c_2210])).

tff(c_2215,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_70,c_2182,c_2213])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:43:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.69/2.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.69/2.53  
% 7.69/2.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.69/2.53  %$ r2_funct_2 > v5_pre_topc > v1_funct_2 > r4_tsep_1 > r3_tsep_1 > r1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_8 > #skF_4
% 7.69/2.53  
% 7.69/2.53  %Foreground sorts:
% 7.69/2.53  
% 7.69/2.53  
% 7.69/2.53  %Background operators:
% 7.69/2.53  
% 7.69/2.53  
% 7.69/2.53  %Foreground operators:
% 7.69/2.53  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.69/2.53  tff(k10_tmap_1, type, k10_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.69/2.53  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 7.69/2.53  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 7.69/2.53  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.69/2.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.69/2.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.69/2.53  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.69/2.53  tff('#skF_7', type, '#skF_7': $i).
% 7.69/2.53  tff(r4_tsep_1, type, r4_tsep_1: ($i * $i * $i) > $o).
% 7.69/2.53  tff('#skF_5', type, '#skF_5': $i).
% 7.69/2.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.69/2.53  tff('#skF_6', type, '#skF_6': $i).
% 7.69/2.53  tff('#skF_3', type, '#skF_3': $i).
% 7.69/2.53  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.69/2.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.69/2.53  tff('#skF_8', type, '#skF_8': $i).
% 7.69/2.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.69/2.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.69/2.53  tff('#skF_4', type, '#skF_4': $i).
% 7.69/2.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.69/2.53  tff(r3_tsep_1, type, r3_tsep_1: ($i * $i * $i) > $o).
% 7.69/2.53  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 7.69/2.53  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.69/2.53  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.69/2.53  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 7.69/2.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.69/2.53  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 7.69/2.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.69/2.53  
% 8.10/2.59  tff(f_321, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (r3_tsep_1(A, B, C) <=> (r1_tsep_1(B, C) & (![D]: (((~v2_struct_0(D) & v2_pre_topc(D)) & l1_pre_topc(D)) => (![E]: ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(B), u1_struct_0(D))) & v5_pre_topc(E, B, D)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(D))))) => (![F]: ((((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(D))) & v5_pre_topc(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(D))))) => (((v1_funct_1(k10_tmap_1(A, D, B, C, E, F)) & v1_funct_2(k10_tmap_1(A, D, B, C, E, F), u1_struct_0(k1_tsep_1(A, B, C)), u1_struct_0(D))) & v5_pre_topc(k10_tmap_1(A, D, B, C, E, F), k1_tsep_1(A, B, C), D)) & m1_subset_1(k10_tmap_1(A, D, B, C, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, B, C)), u1_struct_0(D))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_tmap_1)).
% 8.10/2.59  tff(f_145, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (r3_tsep_1(A, B, C) <=> (r1_tsep_1(B, C) & (![D]: (((~v2_struct_0(D) & v2_pre_topc(D)) & l1_pre_topc(D)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, B, C)), u1_struct_0(D))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, B, C)), u1_struct_0(D))))) => ((((((((v1_funct_1(k3_tmap_1(A, D, k1_tsep_1(A, B, C), B, E)) & v1_funct_2(k3_tmap_1(A, D, k1_tsep_1(A, B, C), B, E), u1_struct_0(B), u1_struct_0(D))) & v5_pre_topc(k3_tmap_1(A, D, k1_tsep_1(A, B, C), B, E), B, D)) & m1_subset_1(k3_tmap_1(A, D, k1_tsep_1(A, B, C), B, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(D))))) & v1_funct_1(k3_tmap_1(A, D, k1_tsep_1(A, B, C), C, E))) & v1_funct_2(k3_tmap_1(A, D, k1_tsep_1(A, B, C), C, E), u1_struct_0(C), u1_struct_0(D))) & v5_pre_topc(k3_tmap_1(A, D, k1_tsep_1(A, B, C), C, E), C, D)) & m1_subset_1(k3_tmap_1(A, D, k1_tsep_1(A, B, C), C, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(D))))) => (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, B, C)), u1_struct_0(D))) & v5_pre_topc(E, k1_tsep_1(A, B, C), D)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, B, C)), u1_struct_0(D)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t135_tmap_1)).
% 8.10/2.59  tff(f_83, axiom, (![A, B, C, D, E, F]: ((((((((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) & ~v2_struct_0(D)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(F)) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_tmap_1)).
% 8.10/2.59  tff(f_181, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B), E, k10_tmap_1(A, B, C, D, k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_tmap_1)).
% 8.10/2.59  tff(f_41, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 8.10/2.59  tff(f_238, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (r1_tsep_1(C, D) => (![E]: ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: ((((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (r4_tsep_1(A, C, D) => (((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & v5_pre_topc(k10_tmap_1(A, B, C, D, E, F), k1_tsep_1(A, C, D), B)) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_tmap_1)).
% 8.10/2.59  tff(f_263, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => ((r1_tsep_1(B, C) & r4_tsep_1(A, B, C)) <=> r3_tsep_1(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_tsep_1)).
% 8.10/2.59  tff(c_80, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_321])).
% 8.10/2.59  tff(c_74, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_321])).
% 8.10/2.59  tff(c_70, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_321])).
% 8.10/2.59  tff(c_78, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_321])).
% 8.10/2.59  tff(c_76, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_321])).
% 8.10/2.59  tff(c_72, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_321])).
% 8.10/2.59  tff(c_68, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_321])).
% 8.10/2.59  tff(c_212, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | r1_tsep_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_321])).
% 8.10/2.59  tff(c_237, plain, (r1_tsep_1('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_212])).
% 8.10/2.59  tff(c_92, plain, (v1_funct_1('#skF_8') | ~r1_tsep_1('#skF_4', '#skF_5') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_321])).
% 8.10/2.59  tff(c_239, plain, (v1_funct_1('#skF_8') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_237, c_92])).
% 8.10/2.59  tff(c_240, plain, (~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_239])).
% 8.10/2.59  tff(c_34, plain, (![A_11, B_39, C_53]: (v1_funct_1('#skF_2'(A_11, B_39, C_53)) | r3_tsep_1(A_11, B_39, C_53) | ~r1_tsep_1(B_39, C_53) | ~m1_pre_topc(C_53, A_11) | v2_struct_0(C_53) | ~m1_pre_topc(B_39, A_11) | v2_struct_0(B_39) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.10/2.59  tff(c_30, plain, (![A_11, B_39, C_53]: (m1_subset_1('#skF_2'(A_11, B_39, C_53), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_11, B_39, C_53)), u1_struct_0('#skF_1'(A_11, B_39, C_53))))) | r3_tsep_1(A_11, B_39, C_53) | ~r1_tsep_1(B_39, C_53) | ~m1_pre_topc(C_53, A_11) | v2_struct_0(C_53) | ~m1_pre_topc(B_39, A_11) | v2_struct_0(B_39) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.10/2.59  tff(c_26, plain, (![A_11, B_39, C_53]: (v1_funct_2(k3_tmap_1(A_11, '#skF_1'(A_11, B_39, C_53), k1_tsep_1(A_11, B_39, C_53), B_39, '#skF_2'(A_11, B_39, C_53)), u1_struct_0(B_39), u1_struct_0('#skF_1'(A_11, B_39, C_53))) | r3_tsep_1(A_11, B_39, C_53) | ~r1_tsep_1(B_39, C_53) | ~m1_pre_topc(C_53, A_11) | v2_struct_0(C_53) | ~m1_pre_topc(B_39, A_11) | v2_struct_0(B_39) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.10/2.59  tff(c_38, plain, (![A_11, B_39, C_53]: (v2_pre_topc('#skF_1'(A_11, B_39, C_53)) | r3_tsep_1(A_11, B_39, C_53) | ~r1_tsep_1(B_39, C_53) | ~m1_pre_topc(C_53, A_11) | v2_struct_0(C_53) | ~m1_pre_topc(B_39, A_11) | v2_struct_0(B_39) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.10/2.59  tff(c_18, plain, (![A_11, B_39, C_53]: (v1_funct_2(k3_tmap_1(A_11, '#skF_1'(A_11, B_39, C_53), k1_tsep_1(A_11, B_39, C_53), C_53, '#skF_2'(A_11, B_39, C_53)), u1_struct_0(C_53), u1_struct_0('#skF_1'(A_11, B_39, C_53))) | r3_tsep_1(A_11, B_39, C_53) | ~r1_tsep_1(B_39, C_53) | ~m1_pre_topc(C_53, A_11) | v2_struct_0(C_53) | ~m1_pre_topc(B_39, A_11) | v2_struct_0(B_39) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.10/2.59  tff(c_299, plain, (![A_336, B_337, C_338]: (m1_subset_1(k3_tmap_1(A_336, '#skF_1'(A_336, B_337, C_338), k1_tsep_1(A_336, B_337, C_338), C_338, '#skF_2'(A_336, B_337, C_338)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_338), u1_struct_0('#skF_1'(A_336, B_337, C_338))))) | r3_tsep_1(A_336, B_337, C_338) | ~r1_tsep_1(B_337, C_338) | ~m1_pre_topc(C_338, A_336) | v2_struct_0(C_338) | ~m1_pre_topc(B_337, A_336) | v2_struct_0(B_337) | ~l1_pre_topc(A_336) | ~v2_pre_topc(A_336) | v2_struct_0(A_336))), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.10/2.59  tff(c_186, plain, (![D_271, E_275, F_277]: (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v1_funct_1(k10_tmap_1('#skF_3', D_271, '#skF_4', '#skF_5', E_275, F_277)) | ~m1_subset_1(F_277, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(D_271)))) | ~v5_pre_topc(F_277, '#skF_5', D_271) | ~v1_funct_2(F_277, u1_struct_0('#skF_5'), u1_struct_0(D_271)) | ~v1_funct_1(F_277) | ~m1_subset_1(E_275, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(D_271)))) | ~v5_pre_topc(E_275, '#skF_4', D_271) | ~v1_funct_2(E_275, u1_struct_0('#skF_4'), u1_struct_0(D_271)) | ~v1_funct_1(E_275) | ~l1_pre_topc(D_271) | ~v2_pre_topc(D_271) | v2_struct_0(D_271))), inference(cnfTransformation, [status(thm)], [f_321])).
% 8.10/2.59  tff(c_273, plain, (![D_271, E_275, F_277]: (v1_funct_1(k10_tmap_1('#skF_3', D_271, '#skF_4', '#skF_5', E_275, F_277)) | ~m1_subset_1(F_277, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(D_271)))) | ~v5_pre_topc(F_277, '#skF_5', D_271) | ~v1_funct_2(F_277, u1_struct_0('#skF_5'), u1_struct_0(D_271)) | ~v1_funct_1(F_277) | ~m1_subset_1(E_275, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(D_271)))) | ~v5_pre_topc(E_275, '#skF_4', D_271) | ~v1_funct_2(E_275, u1_struct_0('#skF_4'), u1_struct_0(D_271)) | ~v1_funct_1(E_275) | ~l1_pre_topc(D_271) | ~v2_pre_topc(D_271) | v2_struct_0(D_271))), inference(negUnitSimplification, [status(thm)], [c_240, c_186])).
% 8.10/2.59  tff(c_302, plain, (![A_336, B_337, E_275]: (v1_funct_1(k10_tmap_1('#skF_3', '#skF_1'(A_336, B_337, '#skF_5'), '#skF_4', '#skF_5', E_275, k3_tmap_1(A_336, '#skF_1'(A_336, B_337, '#skF_5'), k1_tsep_1(A_336, B_337, '#skF_5'), '#skF_5', '#skF_2'(A_336, B_337, '#skF_5')))) | ~v5_pre_topc(k3_tmap_1(A_336, '#skF_1'(A_336, B_337, '#skF_5'), k1_tsep_1(A_336, B_337, '#skF_5'), '#skF_5', '#skF_2'(A_336, B_337, '#skF_5')), '#skF_5', '#skF_1'(A_336, B_337, '#skF_5')) | ~v1_funct_2(k3_tmap_1(A_336, '#skF_1'(A_336, B_337, '#skF_5'), k1_tsep_1(A_336, B_337, '#skF_5'), '#skF_5', '#skF_2'(A_336, B_337, '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'(A_336, B_337, '#skF_5'))) | ~v1_funct_1(k3_tmap_1(A_336, '#skF_1'(A_336, B_337, '#skF_5'), k1_tsep_1(A_336, B_337, '#skF_5'), '#skF_5', '#skF_2'(A_336, B_337, '#skF_5'))) | ~m1_subset_1(E_275, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'(A_336, B_337, '#skF_5'))))) | ~v5_pre_topc(E_275, '#skF_4', '#skF_1'(A_336, B_337, '#skF_5')) | ~v1_funct_2(E_275, u1_struct_0('#skF_4'), u1_struct_0('#skF_1'(A_336, B_337, '#skF_5'))) | ~v1_funct_1(E_275) | ~l1_pre_topc('#skF_1'(A_336, B_337, '#skF_5')) | ~v2_pre_topc('#skF_1'(A_336, B_337, '#skF_5')) | v2_struct_0('#skF_1'(A_336, B_337, '#skF_5')) | r3_tsep_1(A_336, B_337, '#skF_5') | ~r1_tsep_1(B_337, '#skF_5') | ~m1_pre_topc('#skF_5', A_336) | v2_struct_0('#skF_5') | ~m1_pre_topc(B_337, A_336) | v2_struct_0(B_337) | ~l1_pre_topc(A_336) | ~v2_pre_topc(A_336) | v2_struct_0(A_336))), inference(resolution, [status(thm)], [c_299, c_273])).
% 8.10/2.59  tff(c_578, plain, (![A_453, B_454, E_455]: (v1_funct_1(k10_tmap_1('#skF_3', '#skF_1'(A_453, B_454, '#skF_5'), '#skF_4', '#skF_5', E_455, k3_tmap_1(A_453, '#skF_1'(A_453, B_454, '#skF_5'), k1_tsep_1(A_453, B_454, '#skF_5'), '#skF_5', '#skF_2'(A_453, B_454, '#skF_5')))) | ~v5_pre_topc(k3_tmap_1(A_453, '#skF_1'(A_453, B_454, '#skF_5'), k1_tsep_1(A_453, B_454, '#skF_5'), '#skF_5', '#skF_2'(A_453, B_454, '#skF_5')), '#skF_5', '#skF_1'(A_453, B_454, '#skF_5')) | ~v1_funct_2(k3_tmap_1(A_453, '#skF_1'(A_453, B_454, '#skF_5'), k1_tsep_1(A_453, B_454, '#skF_5'), '#skF_5', '#skF_2'(A_453, B_454, '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'(A_453, B_454, '#skF_5'))) | ~v1_funct_1(k3_tmap_1(A_453, '#skF_1'(A_453, B_454, '#skF_5'), k1_tsep_1(A_453, B_454, '#skF_5'), '#skF_5', '#skF_2'(A_453, B_454, '#skF_5'))) | ~m1_subset_1(E_455, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'(A_453, B_454, '#skF_5'))))) | ~v5_pre_topc(E_455, '#skF_4', '#skF_1'(A_453, B_454, '#skF_5')) | ~v1_funct_2(E_455, u1_struct_0('#skF_4'), u1_struct_0('#skF_1'(A_453, B_454, '#skF_5'))) | ~v1_funct_1(E_455) | ~l1_pre_topc('#skF_1'(A_453, B_454, '#skF_5')) | ~v2_pre_topc('#skF_1'(A_453, B_454, '#skF_5')) | v2_struct_0('#skF_1'(A_453, B_454, '#skF_5')) | r3_tsep_1(A_453, B_454, '#skF_5') | ~r1_tsep_1(B_454, '#skF_5') | ~m1_pre_topc('#skF_5', A_453) | ~m1_pre_topc(B_454, A_453) | v2_struct_0(B_454) | ~l1_pre_topc(A_453) | ~v2_pre_topc(A_453) | v2_struct_0(A_453))), inference(negUnitSimplification, [status(thm)], [c_70, c_302])).
% 8.10/2.59  tff(c_584, plain, (![A_11, B_39, E_455]: (v1_funct_1(k10_tmap_1('#skF_3', '#skF_1'(A_11, B_39, '#skF_5'), '#skF_4', '#skF_5', E_455, k3_tmap_1(A_11, '#skF_1'(A_11, B_39, '#skF_5'), k1_tsep_1(A_11, B_39, '#skF_5'), '#skF_5', '#skF_2'(A_11, B_39, '#skF_5')))) | ~v5_pre_topc(k3_tmap_1(A_11, '#skF_1'(A_11, B_39, '#skF_5'), k1_tsep_1(A_11, B_39, '#skF_5'), '#skF_5', '#skF_2'(A_11, B_39, '#skF_5')), '#skF_5', '#skF_1'(A_11, B_39, '#skF_5')) | ~v1_funct_1(k3_tmap_1(A_11, '#skF_1'(A_11, B_39, '#skF_5'), k1_tsep_1(A_11, B_39, '#skF_5'), '#skF_5', '#skF_2'(A_11, B_39, '#skF_5'))) | ~m1_subset_1(E_455, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'(A_11, B_39, '#skF_5'))))) | ~v5_pre_topc(E_455, '#skF_4', '#skF_1'(A_11, B_39, '#skF_5')) | ~v1_funct_2(E_455, u1_struct_0('#skF_4'), u1_struct_0('#skF_1'(A_11, B_39, '#skF_5'))) | ~v1_funct_1(E_455) | ~l1_pre_topc('#skF_1'(A_11, B_39, '#skF_5')) | ~v2_pre_topc('#skF_1'(A_11, B_39, '#skF_5')) | v2_struct_0('#skF_1'(A_11, B_39, '#skF_5')) | r3_tsep_1(A_11, B_39, '#skF_5') | ~r1_tsep_1(B_39, '#skF_5') | ~m1_pre_topc('#skF_5', A_11) | v2_struct_0('#skF_5') | ~m1_pre_topc(B_39, A_11) | v2_struct_0(B_39) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(resolution, [status(thm)], [c_18, c_578])).
% 8.10/2.59  tff(c_589, plain, (![A_11, B_39, E_455]: (v1_funct_1(k10_tmap_1('#skF_3', '#skF_1'(A_11, B_39, '#skF_5'), '#skF_4', '#skF_5', E_455, k3_tmap_1(A_11, '#skF_1'(A_11, B_39, '#skF_5'), k1_tsep_1(A_11, B_39, '#skF_5'), '#skF_5', '#skF_2'(A_11, B_39, '#skF_5')))) | ~v5_pre_topc(k3_tmap_1(A_11, '#skF_1'(A_11, B_39, '#skF_5'), k1_tsep_1(A_11, B_39, '#skF_5'), '#skF_5', '#skF_2'(A_11, B_39, '#skF_5')), '#skF_5', '#skF_1'(A_11, B_39, '#skF_5')) | ~v1_funct_1(k3_tmap_1(A_11, '#skF_1'(A_11, B_39, '#skF_5'), k1_tsep_1(A_11, B_39, '#skF_5'), '#skF_5', '#skF_2'(A_11, B_39, '#skF_5'))) | ~m1_subset_1(E_455, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'(A_11, B_39, '#skF_5'))))) | ~v5_pre_topc(E_455, '#skF_4', '#skF_1'(A_11, B_39, '#skF_5')) | ~v1_funct_2(E_455, u1_struct_0('#skF_4'), u1_struct_0('#skF_1'(A_11, B_39, '#skF_5'))) | ~v1_funct_1(E_455) | ~l1_pre_topc('#skF_1'(A_11, B_39, '#skF_5')) | ~v2_pre_topc('#skF_1'(A_11, B_39, '#skF_5')) | v2_struct_0('#skF_1'(A_11, B_39, '#skF_5')) | r3_tsep_1(A_11, B_39, '#skF_5') | ~r1_tsep_1(B_39, '#skF_5') | ~m1_pre_topc('#skF_5', A_11) | ~m1_pre_topc(B_39, A_11) | v2_struct_0(B_39) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(negUnitSimplification, [status(thm)], [c_70, c_584])).
% 8.10/2.59  tff(c_160, plain, (![D_271, E_275, F_277]: (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v1_funct_2(k10_tmap_1('#skF_3', D_271, '#skF_4', '#skF_5', E_275, F_277), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0(D_271)) | ~m1_subset_1(F_277, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(D_271)))) | ~v5_pre_topc(F_277, '#skF_5', D_271) | ~v1_funct_2(F_277, u1_struct_0('#skF_5'), u1_struct_0(D_271)) | ~v1_funct_1(F_277) | ~m1_subset_1(E_275, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(D_271)))) | ~v5_pre_topc(E_275, '#skF_4', D_271) | ~v1_funct_2(E_275, u1_struct_0('#skF_4'), u1_struct_0(D_271)) | ~v1_funct_1(E_275) | ~l1_pre_topc(D_271) | ~v2_pre_topc(D_271) | v2_struct_0(D_271))), inference(cnfTransformation, [status(thm)], [f_321])).
% 8.10/2.59  tff(c_366, plain, (![D_271, E_275, F_277]: (v1_funct_2(k10_tmap_1('#skF_3', D_271, '#skF_4', '#skF_5', E_275, F_277), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0(D_271)) | ~m1_subset_1(F_277, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(D_271)))) | ~v5_pre_topc(F_277, '#skF_5', D_271) | ~v1_funct_2(F_277, u1_struct_0('#skF_5'), u1_struct_0(D_271)) | ~v1_funct_1(F_277) | ~m1_subset_1(E_275, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(D_271)))) | ~v5_pre_topc(E_275, '#skF_4', D_271) | ~v1_funct_2(E_275, u1_struct_0('#skF_4'), u1_struct_0(D_271)) | ~v1_funct_1(E_275) | ~l1_pre_topc(D_271) | ~v2_pre_topc(D_271) | v2_struct_0(D_271))), inference(negUnitSimplification, [status(thm)], [c_240, c_160])).
% 8.10/2.59  tff(c_6, plain, (![B_6, C_7, E_9, D_8, A_5, F_10]: (m1_subset_1(k10_tmap_1(A_5, B_6, C_7, D_8, E_9, F_10), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_5, C_7, D_8)), u1_struct_0(B_6)))) | ~m1_subset_1(F_10, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_8), u1_struct_0(B_6)))) | ~v1_funct_2(F_10, u1_struct_0(D_8), u1_struct_0(B_6)) | ~v1_funct_1(F_10) | ~m1_subset_1(E_9, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_7), u1_struct_0(B_6)))) | ~v1_funct_2(E_9, u1_struct_0(C_7), u1_struct_0(B_6)) | ~v1_funct_1(E_9) | ~m1_pre_topc(D_8, A_5) | v2_struct_0(D_8) | ~m1_pre_topc(C_7, A_5) | v2_struct_0(C_7) | ~l1_pre_topc(B_6) | ~v2_pre_topc(B_6) | v2_struct_0(B_6) | ~l1_pre_topc(A_5) | ~v2_pre_topc(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.10/2.59  tff(c_455, plain, (![B_380, C_379, A_381, E_378, D_382]: (r2_funct_2(u1_struct_0(k1_tsep_1(A_381, C_379, D_382)), u1_struct_0(B_380), E_378, k10_tmap_1(A_381, B_380, C_379, D_382, k3_tmap_1(A_381, B_380, k1_tsep_1(A_381, C_379, D_382), C_379, E_378), k3_tmap_1(A_381, B_380, k1_tsep_1(A_381, C_379, D_382), D_382, E_378))) | ~m1_subset_1(E_378, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_381, C_379, D_382)), u1_struct_0(B_380)))) | ~v1_funct_2(E_378, u1_struct_0(k1_tsep_1(A_381, C_379, D_382)), u1_struct_0(B_380)) | ~v1_funct_1(E_378) | ~m1_pre_topc(D_382, A_381) | v2_struct_0(D_382) | ~m1_pre_topc(C_379, A_381) | v2_struct_0(C_379) | ~l1_pre_topc(B_380) | ~v2_pre_topc(B_380) | v2_struct_0(B_380) | ~l1_pre_topc(A_381) | ~v2_pre_topc(A_381) | v2_struct_0(A_381))), inference(cnfTransformation, [status(thm)], [f_181])).
% 8.10/2.59  tff(c_4, plain, (![D_4, C_3, A_1, B_2]: (D_4=C_3 | ~r2_funct_2(A_1, B_2, C_3, D_4) | ~m1_subset_1(D_4, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(D_4, A_1, B_2) | ~v1_funct_1(D_4) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(C_3, A_1, B_2) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.10/2.59  tff(c_611, plain, (![C_493, B_494, D_496, A_492, E_495]: (k10_tmap_1(A_492, B_494, C_493, D_496, k3_tmap_1(A_492, B_494, k1_tsep_1(A_492, C_493, D_496), C_493, E_495), k3_tmap_1(A_492, B_494, k1_tsep_1(A_492, C_493, D_496), D_496, E_495))=E_495 | ~m1_subset_1(k10_tmap_1(A_492, B_494, C_493, D_496, k3_tmap_1(A_492, B_494, k1_tsep_1(A_492, C_493, D_496), C_493, E_495), k3_tmap_1(A_492, B_494, k1_tsep_1(A_492, C_493, D_496), D_496, E_495)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_492, C_493, D_496)), u1_struct_0(B_494)))) | ~v1_funct_2(k10_tmap_1(A_492, B_494, C_493, D_496, k3_tmap_1(A_492, B_494, k1_tsep_1(A_492, C_493, D_496), C_493, E_495), k3_tmap_1(A_492, B_494, k1_tsep_1(A_492, C_493, D_496), D_496, E_495)), u1_struct_0(k1_tsep_1(A_492, C_493, D_496)), u1_struct_0(B_494)) | ~v1_funct_1(k10_tmap_1(A_492, B_494, C_493, D_496, k3_tmap_1(A_492, B_494, k1_tsep_1(A_492, C_493, D_496), C_493, E_495), k3_tmap_1(A_492, B_494, k1_tsep_1(A_492, C_493, D_496), D_496, E_495))) | ~m1_subset_1(E_495, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_492, C_493, D_496)), u1_struct_0(B_494)))) | ~v1_funct_2(E_495, u1_struct_0(k1_tsep_1(A_492, C_493, D_496)), u1_struct_0(B_494)) | ~v1_funct_1(E_495) | ~m1_pre_topc(D_496, A_492) | v2_struct_0(D_496) | ~m1_pre_topc(C_493, A_492) | v2_struct_0(C_493) | ~l1_pre_topc(B_494) | ~v2_pre_topc(B_494) | v2_struct_0(B_494) | ~l1_pre_topc(A_492) | ~v2_pre_topc(A_492) | v2_struct_0(A_492))), inference(resolution, [status(thm)], [c_455, c_4])).
% 8.10/2.59  tff(c_632, plain, (![D_533, C_535, E_537, A_536, B_534]: (k10_tmap_1(A_536, B_534, C_535, D_533, k3_tmap_1(A_536, B_534, k1_tsep_1(A_536, C_535, D_533), C_535, E_537), k3_tmap_1(A_536, B_534, k1_tsep_1(A_536, C_535, D_533), D_533, E_537))=E_537 | ~v1_funct_2(k10_tmap_1(A_536, B_534, C_535, D_533, k3_tmap_1(A_536, B_534, k1_tsep_1(A_536, C_535, D_533), C_535, E_537), k3_tmap_1(A_536, B_534, k1_tsep_1(A_536, C_535, D_533), D_533, E_537)), u1_struct_0(k1_tsep_1(A_536, C_535, D_533)), u1_struct_0(B_534)) | ~v1_funct_1(k10_tmap_1(A_536, B_534, C_535, D_533, k3_tmap_1(A_536, B_534, k1_tsep_1(A_536, C_535, D_533), C_535, E_537), k3_tmap_1(A_536, B_534, k1_tsep_1(A_536, C_535, D_533), D_533, E_537))) | ~m1_subset_1(E_537, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_536, C_535, D_533)), u1_struct_0(B_534)))) | ~v1_funct_2(E_537, u1_struct_0(k1_tsep_1(A_536, C_535, D_533)), u1_struct_0(B_534)) | ~v1_funct_1(E_537) | ~m1_subset_1(k3_tmap_1(A_536, B_534, k1_tsep_1(A_536, C_535, D_533), D_533, E_537), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_533), u1_struct_0(B_534)))) | ~v1_funct_2(k3_tmap_1(A_536, B_534, k1_tsep_1(A_536, C_535, D_533), D_533, E_537), u1_struct_0(D_533), u1_struct_0(B_534)) | ~v1_funct_1(k3_tmap_1(A_536, B_534, k1_tsep_1(A_536, C_535, D_533), D_533, E_537)) | ~m1_subset_1(k3_tmap_1(A_536, B_534, k1_tsep_1(A_536, C_535, D_533), C_535, E_537), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_535), u1_struct_0(B_534)))) | ~v1_funct_2(k3_tmap_1(A_536, B_534, k1_tsep_1(A_536, C_535, D_533), C_535, E_537), u1_struct_0(C_535), u1_struct_0(B_534)) | ~v1_funct_1(k3_tmap_1(A_536, B_534, k1_tsep_1(A_536, C_535, D_533), C_535, E_537)) | ~m1_pre_topc(D_533, A_536) | v2_struct_0(D_533) | ~m1_pre_topc(C_535, A_536) | v2_struct_0(C_535) | ~l1_pre_topc(B_534) | ~v2_pre_topc(B_534) | v2_struct_0(B_534) | ~l1_pre_topc(A_536) | ~v2_pre_topc(A_536) | v2_struct_0(A_536))), inference(resolution, [status(thm)], [c_6, c_611])).
% 8.10/2.59  tff(c_640, plain, (![D_271, E_537]: (k10_tmap_1('#skF_3', D_271, '#skF_4', '#skF_5', k3_tmap_1('#skF_3', D_271, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', E_537), k3_tmap_1('#skF_3', D_271, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', E_537))=E_537 | ~v1_funct_1(k10_tmap_1('#skF_3', D_271, '#skF_4', '#skF_5', k3_tmap_1('#skF_3', D_271, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', E_537), k3_tmap_1('#skF_3', D_271, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', E_537))) | ~m1_subset_1(E_537, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0(D_271)))) | ~v1_funct_2(E_537, u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0(D_271)) | ~v1_funct_1(E_537) | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_subset_1(k3_tmap_1('#skF_3', D_271, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', E_537), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(D_271)))) | ~v5_pre_topc(k3_tmap_1('#skF_3', D_271, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', E_537), '#skF_5', D_271) | ~v1_funct_2(k3_tmap_1('#skF_3', D_271, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', E_537), u1_struct_0('#skF_5'), u1_struct_0(D_271)) | ~v1_funct_1(k3_tmap_1('#skF_3', D_271, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', E_537)) | ~m1_subset_1(k3_tmap_1('#skF_3', D_271, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', E_537), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(D_271)))) | ~v5_pre_topc(k3_tmap_1('#skF_3', D_271, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', E_537), '#skF_4', D_271) | ~v1_funct_2(k3_tmap_1('#skF_3', D_271, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', E_537), u1_struct_0('#skF_4'), u1_struct_0(D_271)) | ~v1_funct_1(k3_tmap_1('#skF_3', D_271, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', E_537)) | ~l1_pre_topc(D_271) | ~v2_pre_topc(D_271) | v2_struct_0(D_271))), inference(resolution, [status(thm)], [c_366, c_632])).
% 8.10/2.59  tff(c_644, plain, (![D_271, E_537]: (k10_tmap_1('#skF_3', D_271, '#skF_4', '#skF_5', k3_tmap_1('#skF_3', D_271, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', E_537), k3_tmap_1('#skF_3', D_271, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', E_537))=E_537 | ~v1_funct_1(k10_tmap_1('#skF_3', D_271, '#skF_4', '#skF_5', k3_tmap_1('#skF_3', D_271, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', E_537), k3_tmap_1('#skF_3', D_271, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', E_537))) | ~m1_subset_1(E_537, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0(D_271)))) | ~v1_funct_2(E_537, u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0(D_271)) | ~v1_funct_1(E_537) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~m1_subset_1(k3_tmap_1('#skF_3', D_271, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', E_537), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(D_271)))) | ~v5_pre_topc(k3_tmap_1('#skF_3', D_271, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', E_537), '#skF_5', D_271) | ~v1_funct_2(k3_tmap_1('#skF_3', D_271, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', E_537), u1_struct_0('#skF_5'), u1_struct_0(D_271)) | ~v1_funct_1(k3_tmap_1('#skF_3', D_271, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', E_537)) | ~m1_subset_1(k3_tmap_1('#skF_3', D_271, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', E_537), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(D_271)))) | ~v5_pre_topc(k3_tmap_1('#skF_3', D_271, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', E_537), '#skF_4', D_271) | ~v1_funct_2(k3_tmap_1('#skF_3', D_271, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', E_537), u1_struct_0('#skF_4'), u1_struct_0(D_271)) | ~v1_funct_1(k3_tmap_1('#skF_3', D_271, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', E_537)) | ~l1_pre_topc(D_271) | ~v2_pre_topc(D_271) | v2_struct_0(D_271))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_68, c_640])).
% 8.10/2.59  tff(c_725, plain, (![D_547, E_548]: (k10_tmap_1('#skF_3', D_547, '#skF_4', '#skF_5', k3_tmap_1('#skF_3', D_547, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', E_548), k3_tmap_1('#skF_3', D_547, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', E_548))=E_548 | ~v1_funct_1(k10_tmap_1('#skF_3', D_547, '#skF_4', '#skF_5', k3_tmap_1('#skF_3', D_547, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', E_548), k3_tmap_1('#skF_3', D_547, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', E_548))) | ~m1_subset_1(E_548, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0(D_547)))) | ~v1_funct_2(E_548, u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0(D_547)) | ~v1_funct_1(E_548) | ~m1_subset_1(k3_tmap_1('#skF_3', D_547, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', E_548), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(D_547)))) | ~v5_pre_topc(k3_tmap_1('#skF_3', D_547, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', E_548), '#skF_5', D_547) | ~v1_funct_2(k3_tmap_1('#skF_3', D_547, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', E_548), u1_struct_0('#skF_5'), u1_struct_0(D_547)) | ~v1_funct_1(k3_tmap_1('#skF_3', D_547, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', E_548)) | ~m1_subset_1(k3_tmap_1('#skF_3', D_547, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', E_548), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(D_547)))) | ~v5_pre_topc(k3_tmap_1('#skF_3', D_547, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', E_548), '#skF_4', D_547) | ~v1_funct_2(k3_tmap_1('#skF_3', D_547, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', E_548), u1_struct_0('#skF_4'), u1_struct_0(D_547)) | ~v1_funct_1(k3_tmap_1('#skF_3', D_547, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', E_548)) | ~l1_pre_topc(D_547) | ~v2_pre_topc(D_547) | v2_struct_0(D_547))), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_70, c_644])).
% 8.10/2.59  tff(c_731, plain, (k10_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_5', k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))='#skF_2'('#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_589, c_725])).
% 8.10/2.59  tff(c_738, plain, (k10_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_5', k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))='#skF_2'('#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_68, c_237, c_731])).
% 8.10/2.59  tff(c_739, plain, (k10_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_5', k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))='#skF_2'('#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_240, c_738])).
% 8.10/2.59  tff(c_768, plain, (~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_739])).
% 8.10/2.59  tff(c_771, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_768])).
% 8.10/2.59  tff(c_774, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_68, c_237, c_771])).
% 8.10/2.59  tff(c_776, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_70, c_240, c_774])).
% 8.10/2.59  tff(c_778, plain, (v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_739])).
% 8.10/2.59  tff(c_36, plain, (![A_11, B_39, C_53]: (l1_pre_topc('#skF_1'(A_11, B_39, C_53)) | r3_tsep_1(A_11, B_39, C_53) | ~r1_tsep_1(B_39, C_53) | ~m1_pre_topc(C_53, A_11) | v2_struct_0(C_53) | ~m1_pre_topc(B_39, A_11) | v2_struct_0(B_39) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.10/2.59  tff(c_22, plain, (![A_11, B_39, C_53]: (m1_subset_1(k3_tmap_1(A_11, '#skF_1'(A_11, B_39, C_53), k1_tsep_1(A_11, B_39, C_53), B_39, '#skF_2'(A_11, B_39, C_53)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_39), u1_struct_0('#skF_1'(A_11, B_39, C_53))))) | r3_tsep_1(A_11, B_39, C_53) | ~r1_tsep_1(B_39, C_53) | ~m1_pre_topc(C_53, A_11) | v2_struct_0(C_53) | ~m1_pre_topc(B_39, A_11) | v2_struct_0(B_39) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.10/2.59  tff(c_14, plain, (![A_11, B_39, C_53]: (m1_subset_1(k3_tmap_1(A_11, '#skF_1'(A_11, B_39, C_53), k1_tsep_1(A_11, B_39, C_53), C_53, '#skF_2'(A_11, B_39, C_53)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_53), u1_struct_0('#skF_1'(A_11, B_39, C_53))))) | r3_tsep_1(A_11, B_39, C_53) | ~r1_tsep_1(B_39, C_53) | ~m1_pre_topc(C_53, A_11) | v2_struct_0(C_53) | ~m1_pre_topc(B_39, A_11) | v2_struct_0(B_39) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.10/2.59  tff(c_325, plain, (![C_342, B_341, D_339, F_340, A_343, E_344]: (v1_funct_1(k10_tmap_1(A_343, B_341, C_342, D_339, E_344, F_340)) | ~m1_subset_1(F_340, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_339), u1_struct_0(B_341)))) | ~v1_funct_2(F_340, u1_struct_0(D_339), u1_struct_0(B_341)) | ~v1_funct_1(F_340) | ~m1_subset_1(E_344, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_342), u1_struct_0(B_341)))) | ~v1_funct_2(E_344, u1_struct_0(C_342), u1_struct_0(B_341)) | ~v1_funct_1(E_344) | ~m1_pre_topc(D_339, A_343) | v2_struct_0(D_339) | ~m1_pre_topc(C_342, A_343) | v2_struct_0(C_342) | ~l1_pre_topc(B_341) | ~v2_pre_topc(B_341) | v2_struct_0(B_341) | ~l1_pre_topc(A_343) | ~v2_pre_topc(A_343) | v2_struct_0(A_343))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.10/2.59  tff(c_592, plain, (![B_464, C_465, E_468, C_466, A_467, A_463]: (v1_funct_1(k10_tmap_1(A_463, '#skF_1'(A_467, B_464, C_465), C_466, C_465, E_468, k3_tmap_1(A_467, '#skF_1'(A_467, B_464, C_465), k1_tsep_1(A_467, B_464, C_465), C_465, '#skF_2'(A_467, B_464, C_465)))) | ~v1_funct_2(k3_tmap_1(A_467, '#skF_1'(A_467, B_464, C_465), k1_tsep_1(A_467, B_464, C_465), C_465, '#skF_2'(A_467, B_464, C_465)), u1_struct_0(C_465), u1_struct_0('#skF_1'(A_467, B_464, C_465))) | ~v1_funct_1(k3_tmap_1(A_467, '#skF_1'(A_467, B_464, C_465), k1_tsep_1(A_467, B_464, C_465), C_465, '#skF_2'(A_467, B_464, C_465))) | ~m1_subset_1(E_468, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_466), u1_struct_0('#skF_1'(A_467, B_464, C_465))))) | ~v1_funct_2(E_468, u1_struct_0(C_466), u1_struct_0('#skF_1'(A_467, B_464, C_465))) | ~v1_funct_1(E_468) | ~m1_pre_topc(C_465, A_463) | ~m1_pre_topc(C_466, A_463) | v2_struct_0(C_466) | ~l1_pre_topc('#skF_1'(A_467, B_464, C_465)) | ~v2_pre_topc('#skF_1'(A_467, B_464, C_465)) | v2_struct_0('#skF_1'(A_467, B_464, C_465)) | ~l1_pre_topc(A_463) | ~v2_pre_topc(A_463) | v2_struct_0(A_463) | r3_tsep_1(A_467, B_464, C_465) | ~r1_tsep_1(B_464, C_465) | ~m1_pre_topc(C_465, A_467) | v2_struct_0(C_465) | ~m1_pre_topc(B_464, A_467) | v2_struct_0(B_464) | ~l1_pre_topc(A_467) | ~v2_pre_topc(A_467) | v2_struct_0(A_467))), inference(resolution, [status(thm)], [c_14, c_325])).
% 8.10/2.59  tff(c_599, plain, (![E_468, B_39, C_466, C_53, A_463, A_11]: (v1_funct_1(k10_tmap_1(A_463, '#skF_1'(A_11, B_39, C_53), C_466, C_53, E_468, k3_tmap_1(A_11, '#skF_1'(A_11, B_39, C_53), k1_tsep_1(A_11, B_39, C_53), C_53, '#skF_2'(A_11, B_39, C_53)))) | ~v1_funct_1(k3_tmap_1(A_11, '#skF_1'(A_11, B_39, C_53), k1_tsep_1(A_11, B_39, C_53), C_53, '#skF_2'(A_11, B_39, C_53))) | ~m1_subset_1(E_468, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_466), u1_struct_0('#skF_1'(A_11, B_39, C_53))))) | ~v1_funct_2(E_468, u1_struct_0(C_466), u1_struct_0('#skF_1'(A_11, B_39, C_53))) | ~v1_funct_1(E_468) | ~m1_pre_topc(C_53, A_463) | ~m1_pre_topc(C_466, A_463) | v2_struct_0(C_466) | ~l1_pre_topc('#skF_1'(A_11, B_39, C_53)) | ~v2_pre_topc('#skF_1'(A_11, B_39, C_53)) | v2_struct_0('#skF_1'(A_11, B_39, C_53)) | ~l1_pre_topc(A_463) | ~v2_pre_topc(A_463) | v2_struct_0(A_463) | r3_tsep_1(A_11, B_39, C_53) | ~r1_tsep_1(B_39, C_53) | ~m1_pre_topc(C_53, A_11) | v2_struct_0(C_53) | ~m1_pre_topc(B_39, A_11) | v2_struct_0(B_39) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(resolution, [status(thm)], [c_18, c_592])).
% 8.10/2.59  tff(c_8, plain, (![B_6, C_7, E_9, D_8, A_5, F_10]: (v1_funct_2(k10_tmap_1(A_5, B_6, C_7, D_8, E_9, F_10), u1_struct_0(k1_tsep_1(A_5, C_7, D_8)), u1_struct_0(B_6)) | ~m1_subset_1(F_10, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_8), u1_struct_0(B_6)))) | ~v1_funct_2(F_10, u1_struct_0(D_8), u1_struct_0(B_6)) | ~v1_funct_1(F_10) | ~m1_subset_1(E_9, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_7), u1_struct_0(B_6)))) | ~v1_funct_2(E_9, u1_struct_0(C_7), u1_struct_0(B_6)) | ~v1_funct_1(E_9) | ~m1_pre_topc(D_8, A_5) | v2_struct_0(D_8) | ~m1_pre_topc(C_7, A_5) | v2_struct_0(C_7) | ~l1_pre_topc(B_6) | ~v2_pre_topc(B_6) | v2_struct_0(B_6) | ~l1_pre_topc(A_5) | ~v2_pre_topc(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.10/2.59  tff(c_646, plain, (![E_540, D_538, C_541, B_539, A_542]: (k10_tmap_1(A_542, B_539, C_541, D_538, k3_tmap_1(A_542, B_539, k1_tsep_1(A_542, C_541, D_538), C_541, E_540), k3_tmap_1(A_542, B_539, k1_tsep_1(A_542, C_541, D_538), D_538, E_540))=E_540 | ~v1_funct_1(k10_tmap_1(A_542, B_539, C_541, D_538, k3_tmap_1(A_542, B_539, k1_tsep_1(A_542, C_541, D_538), C_541, E_540), k3_tmap_1(A_542, B_539, k1_tsep_1(A_542, C_541, D_538), D_538, E_540))) | ~m1_subset_1(E_540, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_542, C_541, D_538)), u1_struct_0(B_539)))) | ~v1_funct_2(E_540, u1_struct_0(k1_tsep_1(A_542, C_541, D_538)), u1_struct_0(B_539)) | ~v1_funct_1(E_540) | ~m1_subset_1(k3_tmap_1(A_542, B_539, k1_tsep_1(A_542, C_541, D_538), D_538, E_540), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_538), u1_struct_0(B_539)))) | ~v1_funct_2(k3_tmap_1(A_542, B_539, k1_tsep_1(A_542, C_541, D_538), D_538, E_540), u1_struct_0(D_538), u1_struct_0(B_539)) | ~v1_funct_1(k3_tmap_1(A_542, B_539, k1_tsep_1(A_542, C_541, D_538), D_538, E_540)) | ~m1_subset_1(k3_tmap_1(A_542, B_539, k1_tsep_1(A_542, C_541, D_538), C_541, E_540), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_541), u1_struct_0(B_539)))) | ~v1_funct_2(k3_tmap_1(A_542, B_539, k1_tsep_1(A_542, C_541, D_538), C_541, E_540), u1_struct_0(C_541), u1_struct_0(B_539)) | ~v1_funct_1(k3_tmap_1(A_542, B_539, k1_tsep_1(A_542, C_541, D_538), C_541, E_540)) | ~m1_pre_topc(D_538, A_542) | v2_struct_0(D_538) | ~m1_pre_topc(C_541, A_542) | v2_struct_0(C_541) | ~l1_pre_topc(B_539) | ~v2_pre_topc(B_539) | v2_struct_0(B_539) | ~l1_pre_topc(A_542) | ~v2_pre_topc(A_542) | v2_struct_0(A_542))), inference(resolution, [status(thm)], [c_8, c_632])).
% 8.10/2.59  tff(c_760, plain, (![A_588, B_589, C_590]: (k10_tmap_1(A_588, '#skF_1'(A_588, B_589, C_590), B_589, C_590, k3_tmap_1(A_588, '#skF_1'(A_588, B_589, C_590), k1_tsep_1(A_588, B_589, C_590), B_589, '#skF_2'(A_588, B_589, C_590)), k3_tmap_1(A_588, '#skF_1'(A_588, B_589, C_590), k1_tsep_1(A_588, B_589, C_590), C_590, '#skF_2'(A_588, B_589, C_590)))='#skF_2'(A_588, B_589, C_590) | ~m1_subset_1('#skF_2'(A_588, B_589, C_590), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_588, B_589, C_590)), u1_struct_0('#skF_1'(A_588, B_589, C_590))))) | ~v1_funct_2('#skF_2'(A_588, B_589, C_590), u1_struct_0(k1_tsep_1(A_588, B_589, C_590)), u1_struct_0('#skF_1'(A_588, B_589, C_590))) | ~v1_funct_1('#skF_2'(A_588, B_589, C_590)) | ~m1_subset_1(k3_tmap_1(A_588, '#skF_1'(A_588, B_589, C_590), k1_tsep_1(A_588, B_589, C_590), C_590, '#skF_2'(A_588, B_589, C_590)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_590), u1_struct_0('#skF_1'(A_588, B_589, C_590))))) | ~v1_funct_2(k3_tmap_1(A_588, '#skF_1'(A_588, B_589, C_590), k1_tsep_1(A_588, B_589, C_590), C_590, '#skF_2'(A_588, B_589, C_590)), u1_struct_0(C_590), u1_struct_0('#skF_1'(A_588, B_589, C_590))) | ~v1_funct_1(k3_tmap_1(A_588, '#skF_1'(A_588, B_589, C_590), k1_tsep_1(A_588, B_589, C_590), C_590, '#skF_2'(A_588, B_589, C_590))) | ~m1_subset_1(k3_tmap_1(A_588, '#skF_1'(A_588, B_589, C_590), k1_tsep_1(A_588, B_589, C_590), B_589, '#skF_2'(A_588, B_589, C_590)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_589), u1_struct_0('#skF_1'(A_588, B_589, C_590))))) | ~v1_funct_2(k3_tmap_1(A_588, '#skF_1'(A_588, B_589, C_590), k1_tsep_1(A_588, B_589, C_590), B_589, '#skF_2'(A_588, B_589, C_590)), u1_struct_0(B_589), u1_struct_0('#skF_1'(A_588, B_589, C_590))) | ~v1_funct_1(k3_tmap_1(A_588, '#skF_1'(A_588, B_589, C_590), k1_tsep_1(A_588, B_589, C_590), B_589, '#skF_2'(A_588, B_589, C_590))) | ~l1_pre_topc('#skF_1'(A_588, B_589, C_590)) | ~v2_pre_topc('#skF_1'(A_588, B_589, C_590)) | v2_struct_0('#skF_1'(A_588, B_589, C_590)) | r3_tsep_1(A_588, B_589, C_590) | ~r1_tsep_1(B_589, C_590) | ~m1_pre_topc(C_590, A_588) | v2_struct_0(C_590) | ~m1_pre_topc(B_589, A_588) | v2_struct_0(B_589) | ~l1_pre_topc(A_588) | ~v2_pre_topc(A_588) | v2_struct_0(A_588))), inference(resolution, [status(thm)], [c_599, c_646])).
% 8.10/2.59  tff(c_779, plain, (![A_591, B_592, C_593]: (k10_tmap_1(A_591, '#skF_1'(A_591, B_592, C_593), B_592, C_593, k3_tmap_1(A_591, '#skF_1'(A_591, B_592, C_593), k1_tsep_1(A_591, B_592, C_593), B_592, '#skF_2'(A_591, B_592, C_593)), k3_tmap_1(A_591, '#skF_1'(A_591, B_592, C_593), k1_tsep_1(A_591, B_592, C_593), C_593, '#skF_2'(A_591, B_592, C_593)))='#skF_2'(A_591, B_592, C_593) | ~m1_subset_1('#skF_2'(A_591, B_592, C_593), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_591, B_592, C_593)), u1_struct_0('#skF_1'(A_591, B_592, C_593))))) | ~v1_funct_2('#skF_2'(A_591, B_592, C_593), u1_struct_0(k1_tsep_1(A_591, B_592, C_593)), u1_struct_0('#skF_1'(A_591, B_592, C_593))) | ~v1_funct_1('#skF_2'(A_591, B_592, C_593)) | ~v1_funct_2(k3_tmap_1(A_591, '#skF_1'(A_591, B_592, C_593), k1_tsep_1(A_591, B_592, C_593), C_593, '#skF_2'(A_591, B_592, C_593)), u1_struct_0(C_593), u1_struct_0('#skF_1'(A_591, B_592, C_593))) | ~v1_funct_1(k3_tmap_1(A_591, '#skF_1'(A_591, B_592, C_593), k1_tsep_1(A_591, B_592, C_593), C_593, '#skF_2'(A_591, B_592, C_593))) | ~m1_subset_1(k3_tmap_1(A_591, '#skF_1'(A_591, B_592, C_593), k1_tsep_1(A_591, B_592, C_593), B_592, '#skF_2'(A_591, B_592, C_593)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_592), u1_struct_0('#skF_1'(A_591, B_592, C_593))))) | ~v1_funct_2(k3_tmap_1(A_591, '#skF_1'(A_591, B_592, C_593), k1_tsep_1(A_591, B_592, C_593), B_592, '#skF_2'(A_591, B_592, C_593)), u1_struct_0(B_592), u1_struct_0('#skF_1'(A_591, B_592, C_593))) | ~v1_funct_1(k3_tmap_1(A_591, '#skF_1'(A_591, B_592, C_593), k1_tsep_1(A_591, B_592, C_593), B_592, '#skF_2'(A_591, B_592, C_593))) | ~l1_pre_topc('#skF_1'(A_591, B_592, C_593)) | ~v2_pre_topc('#skF_1'(A_591, B_592, C_593)) | v2_struct_0('#skF_1'(A_591, B_592, C_593)) | r3_tsep_1(A_591, B_592, C_593) | ~r1_tsep_1(B_592, C_593) | ~m1_pre_topc(C_593, A_591) | v2_struct_0(C_593) | ~m1_pre_topc(B_592, A_591) | v2_struct_0(B_592) | ~l1_pre_topc(A_591) | ~v2_pre_topc(A_591) | v2_struct_0(A_591))), inference(resolution, [status(thm)], [c_14, c_760])).
% 8.10/2.59  tff(c_787, plain, (![A_594, B_595, C_596]: (k10_tmap_1(A_594, '#skF_1'(A_594, B_595, C_596), B_595, C_596, k3_tmap_1(A_594, '#skF_1'(A_594, B_595, C_596), k1_tsep_1(A_594, B_595, C_596), B_595, '#skF_2'(A_594, B_595, C_596)), k3_tmap_1(A_594, '#skF_1'(A_594, B_595, C_596), k1_tsep_1(A_594, B_595, C_596), C_596, '#skF_2'(A_594, B_595, C_596)))='#skF_2'(A_594, B_595, C_596) | ~m1_subset_1('#skF_2'(A_594, B_595, C_596), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_594, B_595, C_596)), u1_struct_0('#skF_1'(A_594, B_595, C_596))))) | ~v1_funct_2('#skF_2'(A_594, B_595, C_596), u1_struct_0(k1_tsep_1(A_594, B_595, C_596)), u1_struct_0('#skF_1'(A_594, B_595, C_596))) | ~v1_funct_1('#skF_2'(A_594, B_595, C_596)) | ~v1_funct_2(k3_tmap_1(A_594, '#skF_1'(A_594, B_595, C_596), k1_tsep_1(A_594, B_595, C_596), C_596, '#skF_2'(A_594, B_595, C_596)), u1_struct_0(C_596), u1_struct_0('#skF_1'(A_594, B_595, C_596))) | ~v1_funct_1(k3_tmap_1(A_594, '#skF_1'(A_594, B_595, C_596), k1_tsep_1(A_594, B_595, C_596), C_596, '#skF_2'(A_594, B_595, C_596))) | ~v1_funct_2(k3_tmap_1(A_594, '#skF_1'(A_594, B_595, C_596), k1_tsep_1(A_594, B_595, C_596), B_595, '#skF_2'(A_594, B_595, C_596)), u1_struct_0(B_595), u1_struct_0('#skF_1'(A_594, B_595, C_596))) | ~v1_funct_1(k3_tmap_1(A_594, '#skF_1'(A_594, B_595, C_596), k1_tsep_1(A_594, B_595, C_596), B_595, '#skF_2'(A_594, B_595, C_596))) | ~l1_pre_topc('#skF_1'(A_594, B_595, C_596)) | ~v2_pre_topc('#skF_1'(A_594, B_595, C_596)) | v2_struct_0('#skF_1'(A_594, B_595, C_596)) | r3_tsep_1(A_594, B_595, C_596) | ~r1_tsep_1(B_595, C_596) | ~m1_pre_topc(C_596, A_594) | v2_struct_0(C_596) | ~m1_pre_topc(B_595, A_594) | v2_struct_0(B_595) | ~l1_pre_topc(A_594) | ~v2_pre_topc(A_594) | v2_struct_0(A_594))), inference(resolution, [status(thm)], [c_22, c_779])).
% 8.10/2.59  tff(c_134, plain, (![D_271, E_275, F_277]: (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v5_pre_topc(k10_tmap_1('#skF_3', D_271, '#skF_4', '#skF_5', E_275, F_277), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), D_271) | ~m1_subset_1(F_277, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(D_271)))) | ~v5_pre_topc(F_277, '#skF_5', D_271) | ~v1_funct_2(F_277, u1_struct_0('#skF_5'), u1_struct_0(D_271)) | ~v1_funct_1(F_277) | ~m1_subset_1(E_275, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(D_271)))) | ~v5_pre_topc(E_275, '#skF_4', D_271) | ~v1_funct_2(E_275, u1_struct_0('#skF_4'), u1_struct_0(D_271)) | ~v1_funct_1(E_275) | ~l1_pre_topc(D_271) | ~v2_pre_topc(D_271) | v2_struct_0(D_271))), inference(cnfTransformation, [status(thm)], [f_321])).
% 8.10/2.59  tff(c_343, plain, (![D_348, E_349, F_350]: (v5_pre_topc(k10_tmap_1('#skF_3', D_348, '#skF_4', '#skF_5', E_349, F_350), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), D_348) | ~m1_subset_1(F_350, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(D_348)))) | ~v5_pre_topc(F_350, '#skF_5', D_348) | ~v1_funct_2(F_350, u1_struct_0('#skF_5'), u1_struct_0(D_348)) | ~v1_funct_1(F_350) | ~m1_subset_1(E_349, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(D_348)))) | ~v5_pre_topc(E_349, '#skF_4', D_348) | ~v1_funct_2(E_349, u1_struct_0('#skF_4'), u1_struct_0(D_348)) | ~v1_funct_1(E_349) | ~l1_pre_topc(D_348) | ~v2_pre_topc(D_348) | v2_struct_0(D_348))), inference(negUnitSimplification, [status(thm)], [c_240, c_134])).
% 8.10/2.59  tff(c_346, plain, (![A_11, B_39, E_349]: (v5_pre_topc(k10_tmap_1('#skF_3', '#skF_1'(A_11, B_39, '#skF_5'), '#skF_4', '#skF_5', E_349, k3_tmap_1(A_11, '#skF_1'(A_11, B_39, '#skF_5'), k1_tsep_1(A_11, B_39, '#skF_5'), '#skF_5', '#skF_2'(A_11, B_39, '#skF_5'))), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_1'(A_11, B_39, '#skF_5')) | ~v5_pre_topc(k3_tmap_1(A_11, '#skF_1'(A_11, B_39, '#skF_5'), k1_tsep_1(A_11, B_39, '#skF_5'), '#skF_5', '#skF_2'(A_11, B_39, '#skF_5')), '#skF_5', '#skF_1'(A_11, B_39, '#skF_5')) | ~v1_funct_2(k3_tmap_1(A_11, '#skF_1'(A_11, B_39, '#skF_5'), k1_tsep_1(A_11, B_39, '#skF_5'), '#skF_5', '#skF_2'(A_11, B_39, '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'(A_11, B_39, '#skF_5'))) | ~v1_funct_1(k3_tmap_1(A_11, '#skF_1'(A_11, B_39, '#skF_5'), k1_tsep_1(A_11, B_39, '#skF_5'), '#skF_5', '#skF_2'(A_11, B_39, '#skF_5'))) | ~m1_subset_1(E_349, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'(A_11, B_39, '#skF_5'))))) | ~v5_pre_topc(E_349, '#skF_4', '#skF_1'(A_11, B_39, '#skF_5')) | ~v1_funct_2(E_349, u1_struct_0('#skF_4'), u1_struct_0('#skF_1'(A_11, B_39, '#skF_5'))) | ~v1_funct_1(E_349) | ~l1_pre_topc('#skF_1'(A_11, B_39, '#skF_5')) | ~v2_pre_topc('#skF_1'(A_11, B_39, '#skF_5')) | v2_struct_0('#skF_1'(A_11, B_39, '#skF_5')) | r3_tsep_1(A_11, B_39, '#skF_5') | ~r1_tsep_1(B_39, '#skF_5') | ~m1_pre_topc('#skF_5', A_11) | v2_struct_0('#skF_5') | ~m1_pre_topc(B_39, A_11) | v2_struct_0(B_39) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(resolution, [status(thm)], [c_14, c_343])).
% 8.10/2.59  tff(c_352, plain, (![A_11, B_39, E_349]: (v5_pre_topc(k10_tmap_1('#skF_3', '#skF_1'(A_11, B_39, '#skF_5'), '#skF_4', '#skF_5', E_349, k3_tmap_1(A_11, '#skF_1'(A_11, B_39, '#skF_5'), k1_tsep_1(A_11, B_39, '#skF_5'), '#skF_5', '#skF_2'(A_11, B_39, '#skF_5'))), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_1'(A_11, B_39, '#skF_5')) | ~v5_pre_topc(k3_tmap_1(A_11, '#skF_1'(A_11, B_39, '#skF_5'), k1_tsep_1(A_11, B_39, '#skF_5'), '#skF_5', '#skF_2'(A_11, B_39, '#skF_5')), '#skF_5', '#skF_1'(A_11, B_39, '#skF_5')) | ~v1_funct_2(k3_tmap_1(A_11, '#skF_1'(A_11, B_39, '#skF_5'), k1_tsep_1(A_11, B_39, '#skF_5'), '#skF_5', '#skF_2'(A_11, B_39, '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'(A_11, B_39, '#skF_5'))) | ~v1_funct_1(k3_tmap_1(A_11, '#skF_1'(A_11, B_39, '#skF_5'), k1_tsep_1(A_11, B_39, '#skF_5'), '#skF_5', '#skF_2'(A_11, B_39, '#skF_5'))) | ~m1_subset_1(E_349, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'(A_11, B_39, '#skF_5'))))) | ~v5_pre_topc(E_349, '#skF_4', '#skF_1'(A_11, B_39, '#skF_5')) | ~v1_funct_2(E_349, u1_struct_0('#skF_4'), u1_struct_0('#skF_1'(A_11, B_39, '#skF_5'))) | ~v1_funct_1(E_349) | ~l1_pre_topc('#skF_1'(A_11, B_39, '#skF_5')) | ~v2_pre_topc('#skF_1'(A_11, B_39, '#skF_5')) | v2_struct_0('#skF_1'(A_11, B_39, '#skF_5')) | r3_tsep_1(A_11, B_39, '#skF_5') | ~r1_tsep_1(B_39, '#skF_5') | ~m1_pre_topc('#skF_5', A_11) | ~m1_pre_topc(B_39, A_11) | v2_struct_0(B_39) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(negUnitSimplification, [status(thm)], [c_70, c_346])).
% 8.10/2.59  tff(c_831, plain, (v5_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_787, c_352])).
% 8.10/2.59  tff(c_893, plain, (v5_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_68, c_237, c_778, c_78, c_76, c_72, c_68, c_237, c_778, c_831])).
% 8.10/2.59  tff(c_894, plain, (v5_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_70, c_240, c_893])).
% 8.10/2.59  tff(c_912, plain, (~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_894])).
% 8.10/2.59  tff(c_916, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_912])).
% 8.10/2.59  tff(c_919, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_68, c_237, c_916])).
% 8.10/2.59  tff(c_921, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_70, c_240, c_919])).
% 8.10/2.59  tff(c_923, plain, (l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_894])).
% 8.10/2.59  tff(c_28, plain, (![A_11, B_39, C_53]: (v1_funct_1(k3_tmap_1(A_11, '#skF_1'(A_11, B_39, C_53), k1_tsep_1(A_11, B_39, C_53), B_39, '#skF_2'(A_11, B_39, C_53))) | r3_tsep_1(A_11, B_39, C_53) | ~r1_tsep_1(B_39, C_53) | ~m1_pre_topc(C_53, A_11) | v2_struct_0(C_53) | ~m1_pre_topc(B_39, A_11) | v2_struct_0(B_39) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.10/2.59  tff(c_16, plain, (![A_11, B_39, C_53]: (v5_pre_topc(k3_tmap_1(A_11, '#skF_1'(A_11, B_39, C_53), k1_tsep_1(A_11, B_39, C_53), C_53, '#skF_2'(A_11, B_39, C_53)), C_53, '#skF_1'(A_11, B_39, C_53)) | r3_tsep_1(A_11, B_39, C_53) | ~r1_tsep_1(B_39, C_53) | ~m1_pre_topc(C_53, A_11) | v2_struct_0(C_53) | ~m1_pre_topc(B_39, A_11) | v2_struct_0(B_39) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.10/2.59  tff(c_922, plain, (~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v5_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_894])).
% 8.10/2.59  tff(c_924, plain, (~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_922])).
% 8.10/2.59  tff(c_940, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_16, c_924])).
% 8.10/2.59  tff(c_943, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_68, c_237, c_940])).
% 8.10/2.59  tff(c_945, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_70, c_240, c_943])).
% 8.10/2.59  tff(c_946, plain, (~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | v5_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_922])).
% 8.10/2.59  tff(c_948, plain, (~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_946])).
% 8.10/2.59  tff(c_954, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_28, c_948])).
% 8.10/2.59  tff(c_957, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_68, c_237, c_954])).
% 8.10/2.59  tff(c_959, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_70, c_240, c_957])).
% 8.10/2.59  tff(c_961, plain, (v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_946])).
% 8.10/2.59  tff(c_960, plain, (~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v5_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_946])).
% 8.10/2.59  tff(c_962, plain, (~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')))))), inference(splitLeft, [status(thm)], [c_960])).
% 8.10/2.59  tff(c_978, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_22, c_962])).
% 8.10/2.59  tff(c_981, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_68, c_237, c_978])).
% 8.10/2.59  tff(c_983, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_70, c_240, c_981])).
% 8.10/2.59  tff(c_985, plain, (m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')))))), inference(splitRight, [status(thm)], [c_960])).
% 8.10/2.59  tff(c_10, plain, (![B_6, C_7, E_9, D_8, A_5, F_10]: (v1_funct_1(k10_tmap_1(A_5, B_6, C_7, D_8, E_9, F_10)) | ~m1_subset_1(F_10, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_8), u1_struct_0(B_6)))) | ~v1_funct_2(F_10, u1_struct_0(D_8), u1_struct_0(B_6)) | ~v1_funct_1(F_10) | ~m1_subset_1(E_9, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_7), u1_struct_0(B_6)))) | ~v1_funct_2(E_9, u1_struct_0(C_7), u1_struct_0(B_6)) | ~v1_funct_1(E_9) | ~m1_pre_topc(D_8, A_5) | v2_struct_0(D_8) | ~m1_pre_topc(C_7, A_5) | v2_struct_0(C_7) | ~l1_pre_topc(B_6) | ~v2_pre_topc(B_6) | v2_struct_0(B_6) | ~l1_pre_topc(A_5) | ~v2_pre_topc(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.10/2.59  tff(c_993, plain, (![A_5, C_7, E_9]: (v1_funct_1(k10_tmap_1(A_5, '#skF_1'('#skF_3', '#skF_4', '#skF_5'), C_7, '#skF_4', E_9, k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(E_9, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_7), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2(E_9, u1_struct_0(C_7), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(E_9) | ~m1_pre_topc('#skF_4', A_5) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_7, A_5) | v2_struct_0(C_7) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~l1_pre_topc(A_5) | ~v2_pre_topc(A_5) | v2_struct_0(A_5))), inference(resolution, [status(thm)], [c_985, c_10])).
% 8.10/2.59  tff(c_1010, plain, (![A_5, C_7, E_9]: (v1_funct_1(k10_tmap_1(A_5, '#skF_1'('#skF_3', '#skF_4', '#skF_5'), C_7, '#skF_4', E_9, k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(E_9, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_7), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2(E_9, u1_struct_0(C_7), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(E_9) | ~m1_pre_topc('#skF_4', A_5) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_7, A_5) | v2_struct_0(C_7) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~l1_pre_topc(A_5) | ~v2_pre_topc(A_5) | v2_struct_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_778, c_923, c_961, c_993])).
% 8.10/2.59  tff(c_1011, plain, (![A_5, C_7, E_9]: (v1_funct_1(k10_tmap_1(A_5, '#skF_1'('#skF_3', '#skF_4', '#skF_5'), C_7, '#skF_4', E_9, k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(E_9, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_7), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2(E_9, u1_struct_0(C_7), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(E_9) | ~m1_pre_topc('#skF_4', A_5) | ~m1_pre_topc(C_7, A_5) | v2_struct_0(C_7) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~l1_pre_topc(A_5) | ~v2_pre_topc(A_5) | v2_struct_0(A_5))), inference(negUnitSimplification, [status(thm)], [c_74, c_1010])).
% 8.10/2.59  tff(c_1063, plain, (~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_1011])).
% 8.10/2.59  tff(c_1066, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_26, c_1063])).
% 8.10/2.59  tff(c_1069, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_68, c_237, c_1066])).
% 8.10/2.59  tff(c_1071, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_70, c_240, c_1069])).
% 8.10/2.59  tff(c_1072, plain, (![A_5, C_7, E_9]: (v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v1_funct_1(k10_tmap_1(A_5, '#skF_1'('#skF_3', '#skF_4', '#skF_5'), C_7, '#skF_4', E_9, k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))) | ~m1_subset_1(E_9, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_7), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2(E_9, u1_struct_0(C_7), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(E_9) | ~m1_pre_topc('#skF_4', A_5) | ~m1_pre_topc(C_7, A_5) | v2_struct_0(C_7) | ~l1_pre_topc(A_5) | ~v2_pre_topc(A_5) | v2_struct_0(A_5))), inference(splitRight, [status(thm)], [c_1011])).
% 8.10/2.59  tff(c_1081, plain, (v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_1072])).
% 8.10/2.59  tff(c_40, plain, (![A_11, B_39, C_53]: (~v2_struct_0('#skF_1'(A_11, B_39, C_53)) | r3_tsep_1(A_11, B_39, C_53) | ~r1_tsep_1(B_39, C_53) | ~m1_pre_topc(C_53, A_11) | v2_struct_0(C_53) | ~m1_pre_topc(B_39, A_11) | v2_struct_0(B_39) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.10/2.59  tff(c_1087, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1081, c_40])).
% 8.10/2.59  tff(c_1090, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_68, c_237, c_1087])).
% 8.10/2.59  tff(c_1092, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_70, c_240, c_1090])).
% 8.10/2.59  tff(c_1094, plain, (~v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_1072])).
% 8.10/2.59  tff(c_947, plain, (v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_922])).
% 8.10/2.59  tff(c_24, plain, (![A_11, B_39, C_53]: (v5_pre_topc(k3_tmap_1(A_11, '#skF_1'(A_11, B_39, C_53), k1_tsep_1(A_11, B_39, C_53), B_39, '#skF_2'(A_11, B_39, C_53)), B_39, '#skF_1'(A_11, B_39, C_53)) | r3_tsep_1(A_11, B_39, C_53) | ~r1_tsep_1(B_39, C_53) | ~m1_pre_topc(C_53, A_11) | v2_struct_0(C_53) | ~m1_pre_topc(B_39, A_11) | v2_struct_0(B_39) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.10/2.59  tff(c_2, plain, (![A_1, B_2, D_4]: (r2_funct_2(A_1, B_2, D_4, D_4) | ~m1_subset_1(D_4, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(D_4, A_1, B_2) | ~v1_funct_1(D_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.10/2.59  tff(c_995, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_985, c_2])).
% 8.10/2.59  tff(c_1014, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_961, c_995])).
% 8.10/2.59  tff(c_1015, plain, (~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_1014])).
% 8.10/2.59  tff(c_1055, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_26, c_1015])).
% 8.10/2.59  tff(c_1058, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_68, c_237, c_1055])).
% 8.10/2.59  tff(c_1060, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_70, c_240, c_1058])).
% 8.10/2.59  tff(c_1062, plain, (v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_1014])).
% 8.10/2.59  tff(c_56, plain, (![A_95, C_143, E_155, F_157, D_151, B_127]: (v5_pre_topc(k10_tmap_1(A_95, B_127, C_143, D_151, E_155, F_157), k1_tsep_1(A_95, C_143, D_151), B_127) | ~r4_tsep_1(A_95, C_143, D_151) | ~m1_subset_1(F_157, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_151), u1_struct_0(B_127)))) | ~v5_pre_topc(F_157, D_151, B_127) | ~v1_funct_2(F_157, u1_struct_0(D_151), u1_struct_0(B_127)) | ~v1_funct_1(F_157) | ~m1_subset_1(E_155, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_143), u1_struct_0(B_127)))) | ~v5_pre_topc(E_155, C_143, B_127) | ~v1_funct_2(E_155, u1_struct_0(C_143), u1_struct_0(B_127)) | ~v1_funct_1(E_155) | ~r1_tsep_1(C_143, D_151) | ~m1_pre_topc(D_151, A_95) | v2_struct_0(D_151) | ~m1_pre_topc(C_143, A_95) | v2_struct_0(C_143) | ~l1_pre_topc(B_127) | ~v2_pre_topc(B_127) | v2_struct_0(B_127) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_238])).
% 8.10/2.59  tff(c_991, plain, (![A_95, C_143, E_155]: (v5_pre_topc(k10_tmap_1(A_95, '#skF_1'('#skF_3', '#skF_4', '#skF_5'), C_143, '#skF_4', E_155, k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))), k1_tsep_1(A_95, C_143, '#skF_4'), '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~r4_tsep_1(A_95, C_143, '#skF_4') | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(E_155, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_143), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(E_155, C_143, '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(E_155, u1_struct_0(C_143), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(E_155) | ~r1_tsep_1(C_143, '#skF_4') | ~m1_pre_topc('#skF_4', A_95) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_143, A_95) | v2_struct_0(C_143) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95) | v2_struct_0(A_95))), inference(resolution, [status(thm)], [c_985, c_56])).
% 8.10/2.59  tff(c_1006, plain, (![A_95, C_143, E_155]: (v5_pre_topc(k10_tmap_1(A_95, '#skF_1'('#skF_3', '#skF_4', '#skF_5'), C_143, '#skF_4', E_155, k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))), k1_tsep_1(A_95, C_143, '#skF_4'), '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~r4_tsep_1(A_95, C_143, '#skF_4') | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(E_155, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_143), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(E_155, C_143, '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(E_155, u1_struct_0(C_143), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(E_155) | ~r1_tsep_1(C_143, '#skF_4') | ~m1_pre_topc('#skF_4', A_95) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_143, A_95) | v2_struct_0(C_143) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95) | v2_struct_0(A_95))), inference(demodulation, [status(thm), theory('equality')], [c_778, c_923, c_961, c_991])).
% 8.10/2.59  tff(c_1007, plain, (![A_95, C_143, E_155]: (v5_pre_topc(k10_tmap_1(A_95, '#skF_1'('#skF_3', '#skF_4', '#skF_5'), C_143, '#skF_4', E_155, k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))), k1_tsep_1(A_95, C_143, '#skF_4'), '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~r4_tsep_1(A_95, C_143, '#skF_4') | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(E_155, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_143), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(E_155, C_143, '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(E_155, u1_struct_0(C_143), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(E_155) | ~r1_tsep_1(C_143, '#skF_4') | ~m1_pre_topc('#skF_4', A_95) | ~m1_pre_topc(C_143, A_95) | v2_struct_0(C_143) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95) | v2_struct_0(A_95))), inference(negUnitSimplification, [status(thm)], [c_74, c_1006])).
% 8.10/2.59  tff(c_1097, plain, (![A_95, C_143, E_155]: (v5_pre_topc(k10_tmap_1(A_95, '#skF_1'('#skF_3', '#skF_4', '#skF_5'), C_143, '#skF_4', E_155, k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))), k1_tsep_1(A_95, C_143, '#skF_4'), '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~r4_tsep_1(A_95, C_143, '#skF_4') | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(E_155, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_143), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(E_155, C_143, '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(E_155, u1_struct_0(C_143), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(E_155) | ~r1_tsep_1(C_143, '#skF_4') | ~m1_pre_topc('#skF_4', A_95) | ~m1_pre_topc(C_143, A_95) | v2_struct_0(C_143) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95) | v2_struct_0(A_95))), inference(demodulation, [status(thm), theory('equality')], [c_1062, c_1007])).
% 8.10/2.59  tff(c_1098, plain, (![A_95, C_143, E_155]: (v5_pre_topc(k10_tmap_1(A_95, '#skF_1'('#skF_3', '#skF_4', '#skF_5'), C_143, '#skF_4', E_155, k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))), k1_tsep_1(A_95, C_143, '#skF_4'), '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~r4_tsep_1(A_95, C_143, '#skF_4') | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(E_155, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_143), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(E_155, C_143, '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(E_155, u1_struct_0(C_143), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(E_155) | ~r1_tsep_1(C_143, '#skF_4') | ~m1_pre_topc('#skF_4', A_95) | ~m1_pre_topc(C_143, A_95) | v2_struct_0(C_143) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95) | v2_struct_0(A_95))), inference(negUnitSimplification, [status(thm)], [c_1094, c_1097])).
% 8.10/2.59  tff(c_1099, plain, (~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_1098])).
% 8.10/2.59  tff(c_1102, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_24, c_1099])).
% 8.10/2.59  tff(c_1105, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_68, c_237, c_1102])).
% 8.10/2.59  tff(c_1107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_70, c_240, c_1105])).
% 8.10/2.59  tff(c_1109, plain, (v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_1098])).
% 8.10/2.59  tff(c_777, plain, (~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | k10_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_5', k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))='#skF_2'('#skF_3', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_739])).
% 8.10/2.59  tff(c_1126, plain, (~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | k10_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_5', k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))='#skF_2'('#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_947, c_985, c_1109, c_1062, c_961, c_923, c_777])).
% 8.10/2.59  tff(c_1127, plain, (~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | k10_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_5', k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))='#skF_2'('#skF_3', '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_1094, c_1126])).
% 8.10/2.59  tff(c_1128, plain, (~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')))))), inference(splitLeft, [status(thm)], [c_1127])).
% 8.10/2.59  tff(c_1131, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_30, c_1128])).
% 8.10/2.59  tff(c_1134, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_68, c_237, c_1131])).
% 8.10/2.59  tff(c_1136, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_70, c_240, c_1134])).
% 8.10/2.59  tff(c_1138, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')))))), inference(splitRight, [status(thm)], [c_1127])).
% 8.10/2.59  tff(c_1176, plain, (r2_funct_2(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_1138, c_2])).
% 8.10/2.59  tff(c_1177, plain, (~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_1176])).
% 8.10/2.59  tff(c_1180, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_1177])).
% 8.10/2.59  tff(c_1183, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_68, c_237, c_1180])).
% 8.10/2.59  tff(c_1185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_70, c_240, c_1183])).
% 8.10/2.59  tff(c_1187, plain, (v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_1176])).
% 8.10/2.59  tff(c_20, plain, (![A_11, B_39, C_53]: (v1_funct_1(k3_tmap_1(A_11, '#skF_1'(A_11, B_39, C_53), k1_tsep_1(A_11, B_39, C_53), C_53, '#skF_2'(A_11, B_39, C_53))) | r3_tsep_1(A_11, B_39, C_53) | ~r1_tsep_1(B_39, C_53) | ~m1_pre_topc(C_53, A_11) | v2_struct_0(C_53) | ~m1_pre_topc(B_39, A_11) | v2_struct_0(B_39) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.10/2.59  tff(c_984, plain, (~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | v5_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_960])).
% 8.10/2.59  tff(c_1112, plain, (~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | v5_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1062, c_1109, c_984])).
% 8.10/2.59  tff(c_1113, plain, (~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | v5_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_1094, c_1112])).
% 8.10/2.59  tff(c_1114, plain, (~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_1113])).
% 8.10/2.59  tff(c_1117, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_20, c_1114])).
% 8.10/2.59  tff(c_1120, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_68, c_237, c_1117])).
% 8.10/2.59  tff(c_1122, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_70, c_240, c_1120])).
% 8.10/2.59  tff(c_1124, plain, (v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_1113])).
% 8.10/2.59  tff(c_32, plain, (![A_11, B_39, C_53]: (v1_funct_2('#skF_2'(A_11, B_39, C_53), u1_struct_0(k1_tsep_1(A_11, B_39, C_53)), u1_struct_0('#skF_1'(A_11, B_39, C_53))) | r3_tsep_1(A_11, B_39, C_53) | ~r1_tsep_1(B_39, C_53) | ~m1_pre_topc(C_53, A_11) | v2_struct_0(C_53) | ~m1_pre_topc(B_39, A_11) | v2_struct_0(B_39) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.10/2.59  tff(c_1186, plain, (~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | r2_funct_2(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')), '#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_2'('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_1176])).
% 8.10/2.59  tff(c_1188, plain, (~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_1186])).
% 8.10/2.59  tff(c_1195, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_1188])).
% 8.10/2.59  tff(c_1198, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_68, c_237, c_1195])).
% 8.10/2.59  tff(c_1200, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_70, c_240, c_1198])).
% 8.10/2.59  tff(c_1202, plain, (v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_1186])).
% 8.10/2.59  tff(c_645, plain, (![D_271, E_537]: (k10_tmap_1('#skF_3', D_271, '#skF_4', '#skF_5', k3_tmap_1('#skF_3', D_271, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', E_537), k3_tmap_1('#skF_3', D_271, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', E_537))=E_537 | ~v1_funct_1(k10_tmap_1('#skF_3', D_271, '#skF_4', '#skF_5', k3_tmap_1('#skF_3', D_271, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', E_537), k3_tmap_1('#skF_3', D_271, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', E_537))) | ~m1_subset_1(E_537, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0(D_271)))) | ~v1_funct_2(E_537, u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0(D_271)) | ~v1_funct_1(E_537) | ~m1_subset_1(k3_tmap_1('#skF_3', D_271, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', E_537), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(D_271)))) | ~v5_pre_topc(k3_tmap_1('#skF_3', D_271, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', E_537), '#skF_5', D_271) | ~v1_funct_2(k3_tmap_1('#skF_3', D_271, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', E_537), u1_struct_0('#skF_5'), u1_struct_0(D_271)) | ~v1_funct_1(k3_tmap_1('#skF_3', D_271, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', E_537)) | ~m1_subset_1(k3_tmap_1('#skF_3', D_271, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', E_537), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(D_271)))) | ~v5_pre_topc(k3_tmap_1('#skF_3', D_271, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', E_537), '#skF_4', D_271) | ~v1_funct_2(k3_tmap_1('#skF_3', D_271, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', E_537), u1_struct_0('#skF_4'), u1_struct_0(D_271)) | ~v1_funct_1(k3_tmap_1('#skF_3', D_271, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', E_537)) | ~l1_pre_topc(D_271) | ~v2_pre_topc(D_271) | v2_struct_0(D_271))), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_70, c_644])).
% 8.10/2.59  tff(c_808, plain, (k10_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_5', k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))='#skF_2'('#skF_3', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_787, c_645])).
% 8.10/2.59  tff(c_889, plain, (k10_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_5', k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))='#skF_2'('#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_68, c_237, c_778, c_778, c_808])).
% 8.10/2.59  tff(c_890, plain, (k10_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_5', k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))='#skF_2'('#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_70, c_240, c_889])).
% 8.10/2.59  tff(c_1210, plain, (k10_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_5', k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))='#skF_2'('#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_923, c_961, c_1062, c_1124, c_1187, c_1202, c_1138, c_1109, c_985, c_947, c_890])).
% 8.10/2.59  tff(c_1211, plain, (k10_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_5', k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))='#skF_2'('#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_1094, c_1210])).
% 8.10/2.59  tff(c_1212, plain, (~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_1211])).
% 8.10/2.59  tff(c_1215, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_18, c_1212])).
% 8.10/2.59  tff(c_1218, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_68, c_237, c_1215])).
% 8.10/2.59  tff(c_1220, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_70, c_240, c_1218])).
% 8.10/2.59  tff(c_1222, plain, (v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_1211])).
% 8.10/2.59  tff(c_1221, plain, (~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | k10_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_5', k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))='#skF_2'('#skF_3', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_1211])).
% 8.10/2.59  tff(c_1223, plain, (~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')))))), inference(splitLeft, [status(thm)], [c_1221])).
% 8.10/2.59  tff(c_1226, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_14, c_1223])).
% 8.10/2.59  tff(c_1229, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_68, c_237, c_1226])).
% 8.10/2.59  tff(c_1231, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_70, c_240, c_1229])).
% 8.10/2.59  tff(c_1233, plain, (m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')))))), inference(splitRight, [status(thm)], [c_1221])).
% 8.10/2.59  tff(c_728, plain, (k10_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_5', k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))='#skF_2'('#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_599, c_725])).
% 8.10/2.59  tff(c_734, plain, (k10_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_5', k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))='#skF_2'('#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_68, c_237, c_728])).
% 8.10/2.59  tff(c_735, plain, (k10_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_5', k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))='#skF_2'('#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2('#skF_2'('#skF_3', '#skF_4', '#skF_5'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_70, c_240, c_734])).
% 8.10/2.59  tff(c_1282, plain, (k10_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_5', k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))='#skF_2'('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_778, c_923, c_961, c_1062, c_985, c_1124, c_1109, c_1222, c_947, c_1233, c_1187, c_1202, c_1138, c_735])).
% 8.10/2.59  tff(c_1283, plain, (k10_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_5', k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))='#skF_2'('#skF_3', '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_1094, c_1282])).
% 8.10/2.59  tff(c_1321, plain, (v5_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_5', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_5'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))))) | ~v5_pre_topc(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'), u1_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5'))) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_5'))) | ~l1_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1283, c_352])).
% 8.10/2.59  tff(c_1401, plain, (v5_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_1'('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4', '#skF_5')) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_68, c_237, c_778, c_923, c_961, c_1062, c_1109, c_985, c_1124, c_1222, c_947, c_1321])).
% 8.10/2.59  tff(c_1402, plain, (v5_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_240, c_1094, c_1401])).
% 8.10/2.59  tff(c_440, plain, (![A_369, B_370, C_371]: (~m1_subset_1('#skF_2'(A_369, B_370, C_371), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_369, B_370, C_371)), u1_struct_0('#skF_1'(A_369, B_370, C_371))))) | ~v5_pre_topc('#skF_2'(A_369, B_370, C_371), k1_tsep_1(A_369, B_370, C_371), '#skF_1'(A_369, B_370, C_371)) | ~v1_funct_2('#skF_2'(A_369, B_370, C_371), u1_struct_0(k1_tsep_1(A_369, B_370, C_371)), u1_struct_0('#skF_1'(A_369, B_370, C_371))) | ~v1_funct_1('#skF_2'(A_369, B_370, C_371)) | r3_tsep_1(A_369, B_370, C_371) | ~r1_tsep_1(B_370, C_371) | ~m1_pre_topc(C_371, A_369) | v2_struct_0(C_371) | ~m1_pre_topc(B_370, A_369) | v2_struct_0(B_370) | ~l1_pre_topc(A_369) | ~v2_pre_topc(A_369) | v2_struct_0(A_369))), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.10/2.59  tff(c_445, plain, (![A_372, B_373, C_374]: (~v5_pre_topc('#skF_2'(A_372, B_373, C_374), k1_tsep_1(A_372, B_373, C_374), '#skF_1'(A_372, B_373, C_374)) | ~v1_funct_2('#skF_2'(A_372, B_373, C_374), u1_struct_0(k1_tsep_1(A_372, B_373, C_374)), u1_struct_0('#skF_1'(A_372, B_373, C_374))) | ~v1_funct_1('#skF_2'(A_372, B_373, C_374)) | r3_tsep_1(A_372, B_373, C_374) | ~r1_tsep_1(B_373, C_374) | ~m1_pre_topc(C_374, A_372) | v2_struct_0(C_374) | ~m1_pre_topc(B_373, A_372) | v2_struct_0(B_373) | ~l1_pre_topc(A_372) | ~v2_pre_topc(A_372) | v2_struct_0(A_372))), inference(resolution, [status(thm)], [c_30, c_440])).
% 8.10/2.59  tff(c_449, plain, (![A_11, B_39, C_53]: (~v5_pre_topc('#skF_2'(A_11, B_39, C_53), k1_tsep_1(A_11, B_39, C_53), '#skF_1'(A_11, B_39, C_53)) | ~v1_funct_1('#skF_2'(A_11, B_39, C_53)) | r3_tsep_1(A_11, B_39, C_53) | ~r1_tsep_1(B_39, C_53) | ~m1_pre_topc(C_53, A_11) | v2_struct_0(C_53) | ~m1_pre_topc(B_39, A_11) | v2_struct_0(B_39) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(resolution, [status(thm)], [c_32, c_445])).
% 8.10/2.59  tff(c_1446, plain, (~v1_funct_1('#skF_2'('#skF_3', '#skF_4', '#skF_5')) | r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1402, c_449])).
% 8.10/2.59  tff(c_1449, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_68, c_237, c_1187, c_1446])).
% 8.10/2.59  tff(c_1451, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_70, c_240, c_1449])).
% 8.10/2.59  tff(c_1453, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_239])).
% 8.10/2.59  tff(c_64, plain, (![A_158, B_162, C_164]: (r4_tsep_1(A_158, B_162, C_164) | ~r3_tsep_1(A_158, B_162, C_164) | ~m1_pre_topc(C_164, A_158) | v2_struct_0(C_164) | ~m1_pre_topc(B_162, A_158) | v2_struct_0(B_162) | ~l1_pre_topc(A_158) | ~v2_pre_topc(A_158) | v2_struct_0(A_158))), inference(cnfTransformation, [status(thm)], [f_263])).
% 8.10/2.59  tff(c_100, plain, (v1_funct_1('#skF_7') | ~r1_tsep_1('#skF_4', '#skF_5') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_321])).
% 8.10/2.59  tff(c_1457, plain, (v1_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1453, c_237, c_100])).
% 8.10/2.59  tff(c_98, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_6')) | ~r1_tsep_1('#skF_4', '#skF_5') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_321])).
% 8.10/2.59  tff(c_1469, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1453, c_237, c_98])).
% 8.10/2.59  tff(c_96, plain, (v5_pre_topc('#skF_7', '#skF_4', '#skF_6') | ~r1_tsep_1('#skF_4', '#skF_5') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_321])).
% 8.10/2.59  tff(c_1463, plain, (v5_pre_topc('#skF_7', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1453, c_237, c_96])).
% 8.10/2.59  tff(c_94, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_6')))) | ~r1_tsep_1('#skF_4', '#skF_5') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_321])).
% 8.10/2.59  tff(c_1471, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_1453, c_237, c_94])).
% 8.10/2.59  tff(c_106, plain, (~v2_struct_0('#skF_6') | ~r1_tsep_1('#skF_4', '#skF_5') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_321])).
% 8.10/2.59  tff(c_1461, plain, (~v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1453, c_237, c_106])).
% 8.10/2.59  tff(c_104, plain, (v2_pre_topc('#skF_6') | ~r1_tsep_1('#skF_4', '#skF_5') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_321])).
% 8.10/2.59  tff(c_1459, plain, (v2_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1453, c_237, c_104])).
% 8.10/2.59  tff(c_102, plain, (l1_pre_topc('#skF_6') | ~r1_tsep_1('#skF_4', '#skF_5') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_321])).
% 8.10/2.59  tff(c_1455, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1453, c_237, c_102])).
% 8.10/2.59  tff(c_1452, plain, (v1_funct_1('#skF_8')), inference(splitRight, [status(thm)], [c_239])).
% 8.10/2.59  tff(c_90, plain, (v1_funct_2('#skF_8', u1_struct_0('#skF_5'), u1_struct_0('#skF_6')) | ~r1_tsep_1('#skF_4', '#skF_5') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_321])).
% 8.10/2.59  tff(c_1467, plain, (v1_funct_2('#skF_8', u1_struct_0('#skF_5'), u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1453, c_237, c_90])).
% 8.10/2.59  tff(c_88, plain, (v5_pre_topc('#skF_8', '#skF_5', '#skF_6') | ~r1_tsep_1('#skF_4', '#skF_5') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_321])).
% 8.10/2.59  tff(c_1465, plain, (v5_pre_topc('#skF_8', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1453, c_237, c_88])).
% 8.10/2.59  tff(c_86, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_6')))) | ~r1_tsep_1('#skF_4', '#skF_5') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_321])).
% 8.10/2.59  tff(c_1473, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_1453, c_237, c_86])).
% 8.10/2.59  tff(c_2106, plain, (![F_782, D_779, B_784, A_783, E_780, C_781]: (v5_pre_topc(k10_tmap_1(A_783, B_784, C_781, D_779, E_780, F_782), k1_tsep_1(A_783, C_781, D_779), B_784) | ~r4_tsep_1(A_783, C_781, D_779) | ~m1_subset_1(F_782, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_779), u1_struct_0(B_784)))) | ~v5_pre_topc(F_782, D_779, B_784) | ~v1_funct_2(F_782, u1_struct_0(D_779), u1_struct_0(B_784)) | ~v1_funct_1(F_782) | ~m1_subset_1(E_780, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_781), u1_struct_0(B_784)))) | ~v5_pre_topc(E_780, C_781, B_784) | ~v1_funct_2(E_780, u1_struct_0(C_781), u1_struct_0(B_784)) | ~v1_funct_1(E_780) | ~r1_tsep_1(C_781, D_779) | ~m1_pre_topc(D_779, A_783) | v2_struct_0(D_779) | ~m1_pre_topc(C_781, A_783) | v2_struct_0(C_781) | ~l1_pre_topc(B_784) | ~v2_pre_topc(B_784) | v2_struct_0(B_784) | ~l1_pre_topc(A_783) | ~v2_pre_topc(A_783) | v2_struct_0(A_783))), inference(cnfTransformation, [status(thm)], [f_238])).
% 8.10/2.59  tff(c_2118, plain, (![A_783, C_781, E_780]: (v5_pre_topc(k10_tmap_1(A_783, '#skF_6', C_781, '#skF_5', E_780, '#skF_8'), k1_tsep_1(A_783, C_781, '#skF_5'), '#skF_6') | ~r4_tsep_1(A_783, C_781, '#skF_5') | ~v5_pre_topc('#skF_8', '#skF_5', '#skF_6') | ~v1_funct_2('#skF_8', u1_struct_0('#skF_5'), u1_struct_0('#skF_6')) | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_780, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_781), u1_struct_0('#skF_6')))) | ~v5_pre_topc(E_780, C_781, '#skF_6') | ~v1_funct_2(E_780, u1_struct_0(C_781), u1_struct_0('#skF_6')) | ~v1_funct_1(E_780) | ~r1_tsep_1(C_781, '#skF_5') | ~m1_pre_topc('#skF_5', A_783) | v2_struct_0('#skF_5') | ~m1_pre_topc(C_781, A_783) | v2_struct_0(C_781) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~l1_pre_topc(A_783) | ~v2_pre_topc(A_783) | v2_struct_0(A_783))), inference(resolution, [status(thm)], [c_1473, c_2106])).
% 8.10/2.59  tff(c_2131, plain, (![A_783, C_781, E_780]: (v5_pre_topc(k10_tmap_1(A_783, '#skF_6', C_781, '#skF_5', E_780, '#skF_8'), k1_tsep_1(A_783, C_781, '#skF_5'), '#skF_6') | ~r4_tsep_1(A_783, C_781, '#skF_5') | ~m1_subset_1(E_780, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_781), u1_struct_0('#skF_6')))) | ~v5_pre_topc(E_780, C_781, '#skF_6') | ~v1_funct_2(E_780, u1_struct_0(C_781), u1_struct_0('#skF_6')) | ~v1_funct_1(E_780) | ~r1_tsep_1(C_781, '#skF_5') | ~m1_pre_topc('#skF_5', A_783) | v2_struct_0('#skF_5') | ~m1_pre_topc(C_781, A_783) | v2_struct_0(C_781) | v2_struct_0('#skF_6') | ~l1_pre_topc(A_783) | ~v2_pre_topc(A_783) | v2_struct_0(A_783))), inference(demodulation, [status(thm), theory('equality')], [c_1459, c_1455, c_1452, c_1467, c_1465, c_2118])).
% 8.10/2.59  tff(c_2139, plain, (![A_785, C_786, E_787]: (v5_pre_topc(k10_tmap_1(A_785, '#skF_6', C_786, '#skF_5', E_787, '#skF_8'), k1_tsep_1(A_785, C_786, '#skF_5'), '#skF_6') | ~r4_tsep_1(A_785, C_786, '#skF_5') | ~m1_subset_1(E_787, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_786), u1_struct_0('#skF_6')))) | ~v5_pre_topc(E_787, C_786, '#skF_6') | ~v1_funct_2(E_787, u1_struct_0(C_786), u1_struct_0('#skF_6')) | ~v1_funct_1(E_787) | ~r1_tsep_1(C_786, '#skF_5') | ~m1_pre_topc('#skF_5', A_785) | ~m1_pre_topc(C_786, A_785) | v2_struct_0(C_786) | ~l1_pre_topc(A_785) | ~v2_pre_topc(A_785) | v2_struct_0(A_785))), inference(negUnitSimplification, [status(thm)], [c_1461, c_70, c_2131])).
% 8.10/2.59  tff(c_2148, plain, (![A_785]: (v5_pre_topc(k10_tmap_1(A_785, '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8'), k1_tsep_1(A_785, '#skF_4', '#skF_5'), '#skF_6') | ~r4_tsep_1(A_785, '#skF_4', '#skF_5') | ~v5_pre_topc('#skF_7', '#skF_4', '#skF_6') | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_6')) | ~v1_funct_1('#skF_7') | ~r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', A_785) | ~m1_pre_topc('#skF_4', A_785) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_785) | ~v2_pre_topc(A_785) | v2_struct_0(A_785))), inference(resolution, [status(thm)], [c_1471, c_2139])).
% 8.10/2.59  tff(c_2162, plain, (![A_785]: (v5_pre_topc(k10_tmap_1(A_785, '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8'), k1_tsep_1(A_785, '#skF_4', '#skF_5'), '#skF_6') | ~r4_tsep_1(A_785, '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', A_785) | ~m1_pre_topc('#skF_4', A_785) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_785) | ~v2_pre_topc(A_785) | v2_struct_0(A_785))), inference(demodulation, [status(thm), theory('equality')], [c_237, c_1457, c_1469, c_1463, c_2148])).
% 8.10/2.59  tff(c_2165, plain, (![A_788]: (v5_pre_topc(k10_tmap_1(A_788, '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8'), k1_tsep_1(A_788, '#skF_4', '#skF_5'), '#skF_6') | ~r4_tsep_1(A_788, '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', A_788) | ~m1_pre_topc('#skF_4', A_788) | ~l1_pre_topc(A_788) | ~v2_pre_topc(A_788) | v2_struct_0(A_788))), inference(negUnitSimplification, [status(thm)], [c_74, c_2162])).
% 8.10/2.59  tff(c_1894, plain, (![C_731, F_729, E_733, A_732, B_730, D_728]: (v1_funct_2(k10_tmap_1(A_732, B_730, C_731, D_728, E_733, F_729), u1_struct_0(k1_tsep_1(A_732, C_731, D_728)), u1_struct_0(B_730)) | ~m1_subset_1(F_729, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_728), u1_struct_0(B_730)))) | ~v1_funct_2(F_729, u1_struct_0(D_728), u1_struct_0(B_730)) | ~v1_funct_1(F_729) | ~m1_subset_1(E_733, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_731), u1_struct_0(B_730)))) | ~v1_funct_2(E_733, u1_struct_0(C_731), u1_struct_0(B_730)) | ~v1_funct_1(E_733) | ~m1_pre_topc(D_728, A_732) | v2_struct_0(D_728) | ~m1_pre_topc(C_731, A_732) | v2_struct_0(C_731) | ~l1_pre_topc(B_730) | ~v2_pre_topc(B_730) | v2_struct_0(B_730) | ~l1_pre_topc(A_732) | ~v2_pre_topc(A_732) | v2_struct_0(A_732))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.10/2.59  tff(c_1728, plain, (![C_706, F_704, E_708, D_703, A_707, B_705]: (m1_subset_1(k10_tmap_1(A_707, B_705, C_706, D_703, E_708, F_704), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_707, C_706, D_703)), u1_struct_0(B_705)))) | ~m1_subset_1(F_704, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_703), u1_struct_0(B_705)))) | ~v1_funct_2(F_704, u1_struct_0(D_703), u1_struct_0(B_705)) | ~v1_funct_1(F_704) | ~m1_subset_1(E_708, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_706), u1_struct_0(B_705)))) | ~v1_funct_2(E_708, u1_struct_0(C_706), u1_struct_0(B_705)) | ~v1_funct_1(E_708) | ~m1_pre_topc(D_703, A_707) | v2_struct_0(D_703) | ~m1_pre_topc(C_706, A_707) | v2_struct_0(C_706) | ~l1_pre_topc(B_705) | ~v2_pre_topc(B_705) | v2_struct_0(B_705) | ~l1_pre_topc(A_707) | ~v2_pre_topc(A_707) | v2_struct_0(A_707))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.10/2.59  tff(c_1553, plain, (![D_667, E_672, C_670, A_671, B_669, F_668]: (v1_funct_1(k10_tmap_1(A_671, B_669, C_670, D_667, E_672, F_668)) | ~m1_subset_1(F_668, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_667), u1_struct_0(B_669)))) | ~v1_funct_2(F_668, u1_struct_0(D_667), u1_struct_0(B_669)) | ~v1_funct_1(F_668) | ~m1_subset_1(E_672, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_670), u1_struct_0(B_669)))) | ~v1_funct_2(E_672, u1_struct_0(C_670), u1_struct_0(B_669)) | ~v1_funct_1(E_672) | ~m1_pre_topc(D_667, A_671) | v2_struct_0(D_667) | ~m1_pre_topc(C_670, A_671) | v2_struct_0(C_670) | ~l1_pre_topc(B_669) | ~v2_pre_topc(B_669) | v2_struct_0(B_669) | ~l1_pre_topc(A_671) | ~v2_pre_topc(A_671) | v2_struct_0(A_671))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.10/2.59  tff(c_1561, plain, (![A_671, C_670, E_672]: (v1_funct_1(k10_tmap_1(A_671, '#skF_6', C_670, '#skF_5', E_672, '#skF_8')) | ~v1_funct_2('#skF_8', u1_struct_0('#skF_5'), u1_struct_0('#skF_6')) | ~v1_funct_1('#skF_8') | ~m1_subset_1(E_672, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_670), u1_struct_0('#skF_6')))) | ~v1_funct_2(E_672, u1_struct_0(C_670), u1_struct_0('#skF_6')) | ~v1_funct_1(E_672) | ~m1_pre_topc('#skF_5', A_671) | v2_struct_0('#skF_5') | ~m1_pre_topc(C_670, A_671) | v2_struct_0(C_670) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~l1_pre_topc(A_671) | ~v2_pre_topc(A_671) | v2_struct_0(A_671))), inference(resolution, [status(thm)], [c_1473, c_1553])).
% 8.10/2.59  tff(c_1569, plain, (![A_671, C_670, E_672]: (v1_funct_1(k10_tmap_1(A_671, '#skF_6', C_670, '#skF_5', E_672, '#skF_8')) | ~m1_subset_1(E_672, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_670), u1_struct_0('#skF_6')))) | ~v1_funct_2(E_672, u1_struct_0(C_670), u1_struct_0('#skF_6')) | ~v1_funct_1(E_672) | ~m1_pre_topc('#skF_5', A_671) | v2_struct_0('#skF_5') | ~m1_pre_topc(C_670, A_671) | v2_struct_0(C_670) | v2_struct_0('#skF_6') | ~l1_pre_topc(A_671) | ~v2_pre_topc(A_671) | v2_struct_0(A_671))), inference(demodulation, [status(thm), theory('equality')], [c_1459, c_1455, c_1452, c_1467, c_1561])).
% 8.10/2.59  tff(c_1575, plain, (![A_673, C_674, E_675]: (v1_funct_1(k10_tmap_1(A_673, '#skF_6', C_674, '#skF_5', E_675, '#skF_8')) | ~m1_subset_1(E_675, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_674), u1_struct_0('#skF_6')))) | ~v1_funct_2(E_675, u1_struct_0(C_674), u1_struct_0('#skF_6')) | ~v1_funct_1(E_675) | ~m1_pre_topc('#skF_5', A_673) | ~m1_pre_topc(C_674, A_673) | v2_struct_0(C_674) | ~l1_pre_topc(A_673) | ~v2_pre_topc(A_673) | v2_struct_0(A_673))), inference(negUnitSimplification, [status(thm)], [c_1461, c_70, c_1569])).
% 8.10/2.59  tff(c_1579, plain, (![A_673]: (v1_funct_1(k10_tmap_1(A_673, '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8')) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_6')) | ~v1_funct_1('#skF_7') | ~m1_pre_topc('#skF_5', A_673) | ~m1_pre_topc('#skF_4', A_673) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_673) | ~v2_pre_topc(A_673) | v2_struct_0(A_673))), inference(resolution, [status(thm)], [c_1471, c_1575])).
% 8.10/2.59  tff(c_1586, plain, (![A_673]: (v1_funct_1(k10_tmap_1(A_673, '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8')) | ~m1_pre_topc('#skF_5', A_673) | ~m1_pre_topc('#skF_4', A_673) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_673) | ~v2_pre_topc(A_673) | v2_struct_0(A_673))), inference(demodulation, [status(thm), theory('equality')], [c_1457, c_1469, c_1579])).
% 8.10/2.59  tff(c_1589, plain, (![A_677]: (v1_funct_1(k10_tmap_1(A_677, '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8')) | ~m1_pre_topc('#skF_5', A_677) | ~m1_pre_topc('#skF_4', A_677) | ~l1_pre_topc(A_677) | ~v2_pre_topc(A_677) | v2_struct_0(A_677))), inference(negUnitSimplification, [status(thm)], [c_74, c_1586])).
% 8.10/2.59  tff(c_84, plain, (~m1_subset_1(k10_tmap_1('#skF_3', '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_6')))) | ~v5_pre_topc(k10_tmap_1('#skF_3', '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_6') | ~v1_funct_2(k10_tmap_1('#skF_3', '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_6')) | ~v1_funct_1(k10_tmap_1('#skF_3', '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8')) | ~r1_tsep_1('#skF_4', '#skF_5') | ~r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_321])).
% 8.10/2.59  tff(c_1547, plain, (~m1_subset_1(k10_tmap_1('#skF_3', '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_6')))) | ~v5_pre_topc(k10_tmap_1('#skF_3', '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_6') | ~v1_funct_2(k10_tmap_1('#skF_3', '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_6')) | ~v1_funct_1(k10_tmap_1('#skF_3', '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1453, c_237, c_84])).
% 8.10/2.59  tff(c_1548, plain, (~v1_funct_1(k10_tmap_1('#skF_3', '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8'))), inference(splitLeft, [status(thm)], [c_1547])).
% 8.10/2.59  tff(c_1592, plain, (~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1589, c_1548])).
% 8.10/2.59  tff(c_1595, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_68, c_1592])).
% 8.10/2.59  tff(c_1597, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_1595])).
% 8.10/2.59  tff(c_1598, plain, (~v1_funct_2(k10_tmap_1('#skF_3', '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_6')) | ~v5_pre_topc(k10_tmap_1('#skF_3', '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_6') | ~m1_subset_1(k10_tmap_1('#skF_3', '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_6'))))), inference(splitRight, [status(thm)], [c_1547])).
% 8.10/2.59  tff(c_1600, plain, (~m1_subset_1(k10_tmap_1('#skF_3', '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_6'))))), inference(splitLeft, [status(thm)], [c_1598])).
% 8.10/2.59  tff(c_1739, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_6')))) | ~v1_funct_2('#skF_8', u1_struct_0('#skF_5'), u1_struct_0('#skF_6')) | ~v1_funct_1('#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_6')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_6')) | ~v1_funct_1('#skF_7') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1728, c_1600])).
% 8.10/2.59  tff(c_1753, plain, (v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_6') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1459, c_1455, c_72, c_68, c_1457, c_1469, c_1471, c_1452, c_1467, c_1473, c_1739])).
% 8.10/2.59  tff(c_1755, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_1461, c_74, c_70, c_1753])).
% 8.10/2.59  tff(c_1756, plain, (~v5_pre_topc(k10_tmap_1('#skF_3', '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_6') | ~v1_funct_2(k10_tmap_1('#skF_3', '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_1598])).
% 8.10/2.59  tff(c_1763, plain, (~v1_funct_2(k10_tmap_1('#skF_3', '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8'), u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_1756])).
% 8.10/2.59  tff(c_1897, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_6')))) | ~v1_funct_2('#skF_8', u1_struct_0('#skF_5'), u1_struct_0('#skF_6')) | ~v1_funct_1('#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_6')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_6')) | ~v1_funct_1('#skF_7') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1894, c_1763])).
% 8.10/2.59  tff(c_1900, plain, (v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_6') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1459, c_1455, c_72, c_68, c_1457, c_1469, c_1471, c_1452, c_1467, c_1473, c_1897])).
% 8.10/2.59  tff(c_1902, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_1461, c_74, c_70, c_1900])).
% 8.10/2.59  tff(c_1903, plain, (~v5_pre_topc(k10_tmap_1('#skF_3', '#skF_6', '#skF_4', '#skF_5', '#skF_7', '#skF_8'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_1756])).
% 8.10/2.59  tff(c_2168, plain, (~r4_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_2165, c_1903])).
% 8.10/2.59  tff(c_2171, plain, (~r4_tsep_1('#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_68, c_2168])).
% 8.10/2.59  tff(c_2172, plain, (~r4_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_80, c_2171])).
% 8.10/2.59  tff(c_2175, plain, (~r3_tsep_1('#skF_3', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_2172])).
% 8.10/2.59  tff(c_2178, plain, (v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_68, c_1453, c_2175])).
% 8.10/2.59  tff(c_2180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_70, c_2178])).
% 8.10/2.59  tff(c_2182, plain, (~r1_tsep_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_212])).
% 8.10/2.59  tff(c_2181, plain, (r3_tsep_1('#skF_3', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_212])).
% 8.10/2.59  tff(c_2207, plain, (![B_792, C_793, A_794]: (r1_tsep_1(B_792, C_793) | ~r3_tsep_1(A_794, B_792, C_793) | ~m1_pre_topc(C_793, A_794) | v2_struct_0(C_793) | ~m1_pre_topc(B_792, A_794) | v2_struct_0(B_792) | ~l1_pre_topc(A_794) | ~v2_pre_topc(A_794) | v2_struct_0(A_794))), inference(cnfTransformation, [status(thm)], [f_263])).
% 8.10/2.59  tff(c_2210, plain, (r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_2181, c_2207])).
% 8.10/2.59  tff(c_2213, plain, (r1_tsep_1('#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_68, c_2210])).
% 8.10/2.59  tff(c_2215, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_70, c_2182, c_2213])).
% 8.10/2.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.10/2.59  
% 8.10/2.59  Inference rules
% 8.10/2.59  ----------------------
% 8.10/2.59  #Ref     : 0
% 8.10/2.59  #Sup     : 273
% 8.10/2.59  #Fact    : 0
% 8.10/2.59  #Define  : 0
% 8.10/2.59  #Split   : 31
% 8.10/2.59  #Chain   : 0
% 8.10/2.59  #Close   : 0
% 8.10/2.59  
% 8.10/2.59  Ordering : KBO
% 8.10/2.59  
% 8.10/2.59  Simplification rules
% 8.10/2.59  ----------------------
% 8.10/2.59  #Subsume      : 148
% 8.10/2.59  #Demod        : 1274
% 8.10/2.59  #Tautology    : 194
% 8.10/2.59  #SimpNegUnit  : 135
% 8.10/2.59  #BackRed      : 0
% 8.10/2.59  
% 8.10/2.59  #Partial instantiations: 0
% 8.10/2.59  #Strategies tried      : 1
% 8.10/2.59  
% 8.10/2.59  Timing (in seconds)
% 8.10/2.59  ----------------------
% 8.10/2.60  Preprocessing        : 0.50
% 8.10/2.60  Parsing              : 0.22
% 8.10/2.60  CNF conversion       : 0.08
% 8.10/2.60  Main loop            : 1.26
% 8.10/2.60  Inferencing          : 0.41
% 8.28/2.60  Reduction            : 0.37
% 8.28/2.60  Demodulation         : 0.26
% 8.28/2.60  BG Simplification    : 0.08
% 8.28/2.60  Subsumption          : 0.38
% 8.28/2.60  Abstraction          : 0.05
% 8.28/2.60  MUC search           : 0.00
% 8.28/2.60  Cooper               : 0.00
% 8.28/2.60  Total                : 1.87
% 8.28/2.60  Index Insertion      : 0.00
% 8.28/2.60  Index Deletion       : 0.00
% 8.28/2.60  Index Matching       : 0.00
% 8.28/2.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
