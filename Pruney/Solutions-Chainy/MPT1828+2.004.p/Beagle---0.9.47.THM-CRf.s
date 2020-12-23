%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:11 EST 2020

% Result     : Theorem 7.85s
% Output     : CNFRefutation 7.85s
% Verified   : 
% Statistics : Number of formulae       :  173 (1409 expanded)
%              Number of leaves         :   35 ( 587 expanded)
%              Depth                    :   17
%              Number of atoms          :  769 (15850 expanded)
%              Number of equality atoms :   12 (  86 expanded)
%              Maximal formula depth    :   29 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v5_pre_topc > v1_funct_2 > r4_tsep_1 > r1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k2_tsep_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r4_tsep_1,type,(
    r4_tsep_1: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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

tff(f_331,negated_conjecture,(
    ~ ! [A] :
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
                   => ( ~ r1_tsep_1(C,D)
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
                             => ( ( r2_funct_2(u1_struct_0(k2_tsep_1(A,C,D)),u1_struct_0(B),k3_tmap_1(A,B,C,k2_tsep_1(A,C,D),E),k3_tmap_1(A,B,D,k2_tsep_1(A,C,D),F))
                                  & r4_tsep_1(A,C,D) )
                               => ( v1_funct_1(k10_tmap_1(A,B,C,D,E,F))
                                  & v1_funct_2(k10_tmap_1(A,B,C,D,E,F),u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
                                  & v5_pre_topc(k10_tmap_1(A,B,C,D,E,F),k1_tsep_1(A,C,D),B)
                                  & m1_subset_1(k10_tmap_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_tmap_1)).

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

tff(f_113,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).

tff(f_258,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_254,axiom,(
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
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ( ( m1_pre_topc(B,C)
                      & m1_pre_topc(D,C) )
                   => m1_pre_topc(k1_tsep_1(A,B,D),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tmap_1)).

tff(f_223,axiom,(
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
                 => ( ~ r1_tsep_1(C,D)
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                       => ! [F] :
                            ( ( v1_funct_1(F)
                              & v1_funct_2(F,u1_struct_0(D),u1_struct_0(B))
                              & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                           => ( ( r2_funct_2(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,k1_tsep_1(A,C,D),C,k10_tmap_1(A,B,C,D,E,F)),E)
                                & r2_funct_2(u1_struct_0(D),u1_struct_0(B),k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,k10_tmap_1(A,B,C,D,E,F)),F) )
                            <=> r2_funct_2(u1_struct_0(k2_tsep_1(A,C,D)),u1_struct_0(B),k3_tmap_1(A,B,C,k2_tsep_1(A,C,D),E),k3_tmap_1(A,B,D,k2_tsep_1(A,C,D),F)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_tmap_1)).

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

tff(f_173,axiom,(
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
                 => ( r4_tsep_1(A,C,D)
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) )
                       => ( ( v1_funct_1(E)
                            & v1_funct_2(E,u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
                            & v5_pre_topc(E,k1_tsep_1(A,C,D),B)
                            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) )
                        <=> ( v1_funct_1(k3_tmap_1(A,B,k1_tsep_1(A,C,D),C,E))
                            & v1_funct_2(k3_tmap_1(A,B,k1_tsep_1(A,C,D),C,E),u1_struct_0(C),u1_struct_0(B))
                            & v5_pre_topc(k3_tmap_1(A,B,k1_tsep_1(A,C,D),C,E),C,B)
                            & m1_subset_1(k3_tmap_1(A,B,k1_tsep_1(A,C,D),C,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B))))
                            & v1_funct_1(k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,E))
                            & v1_funct_2(k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,E),u1_struct_0(D),u1_struct_0(B))
                            & v5_pre_topc(k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,E),D,B)
                            & m1_subset_1(k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_tmap_1)).

tff(c_96,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_90,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_84,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_94,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_92,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_88,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_86,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_82,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_78,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_74,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_72,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_68,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_66,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_64,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_60,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_1230,plain,(
    ! [B_527,D_525,E_530,F_526,C_528,A_529] :
      ( v1_funct_2(k10_tmap_1(A_529,B_527,C_528,D_525,E_530,F_526),u1_struct_0(k1_tsep_1(A_529,C_528,D_525)),u1_struct_0(B_527))
      | ~ m1_subset_1(F_526,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_525),u1_struct_0(B_527))))
      | ~ v1_funct_2(F_526,u1_struct_0(D_525),u1_struct_0(B_527))
      | ~ v1_funct_1(F_526)
      | ~ m1_subset_1(E_530,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_528),u1_struct_0(B_527))))
      | ~ v1_funct_2(E_530,u1_struct_0(C_528),u1_struct_0(B_527))
      | ~ v1_funct_1(E_530)
      | ~ m1_pre_topc(D_525,A_529)
      | v2_struct_0(D_525)
      | ~ m1_pre_topc(C_528,A_529)
      | v2_struct_0(C_528)
      | ~ l1_pre_topc(B_527)
      | ~ v2_pre_topc(B_527)
      | v2_struct_0(B_527)
      | ~ l1_pre_topc(A_529)
      | ~ v2_pre_topc(A_529)
      | v2_struct_0(A_529) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_365,plain,(
    ! [A_269,B_267,D_265,E_270,C_268,F_266] :
      ( v1_funct_1(k10_tmap_1(A_269,B_267,C_268,D_265,E_270,F_266))
      | ~ m1_subset_1(F_266,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_265),u1_struct_0(B_267))))
      | ~ v1_funct_2(F_266,u1_struct_0(D_265),u1_struct_0(B_267))
      | ~ v1_funct_1(F_266)
      | ~ m1_subset_1(E_270,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_268),u1_struct_0(B_267))))
      | ~ v1_funct_2(E_270,u1_struct_0(C_268),u1_struct_0(B_267))
      | ~ v1_funct_1(E_270)
      | ~ m1_pre_topc(D_265,A_269)
      | v2_struct_0(D_265)
      | ~ m1_pre_topc(C_268,A_269)
      | v2_struct_0(C_268)
      | ~ l1_pre_topc(B_267)
      | ~ v2_pre_topc(B_267)
      | v2_struct_0(B_267)
      | ~ l1_pre_topc(A_269)
      | ~ v2_pre_topc(A_269)
      | v2_struct_0(A_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_371,plain,(
    ! [A_269,C_268,E_270] :
      ( v1_funct_1(k10_tmap_1(A_269,'#skF_2',C_268,'#skF_4',E_270,'#skF_6'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_270,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_268),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_270,u1_struct_0(C_268),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_270)
      | ~ m1_pre_topc('#skF_4',A_269)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_268,A_269)
      | v2_struct_0(C_268)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_269)
      | ~ v2_pre_topc(A_269)
      | v2_struct_0(A_269) ) ),
    inference(resolution,[status(thm)],[c_60,c_365])).

tff(c_379,plain,(
    ! [A_269,C_268,E_270] :
      ( v1_funct_1(k10_tmap_1(A_269,'#skF_2',C_268,'#skF_4',E_270,'#skF_6'))
      | ~ m1_subset_1(E_270,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_268),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_270,u1_struct_0(C_268),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_270)
      | ~ m1_pre_topc('#skF_4',A_269)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_268,A_269)
      | v2_struct_0(C_268)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_269)
      | ~ v2_pre_topc(A_269)
      | v2_struct_0(A_269) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_66,c_64,c_371])).

tff(c_408,plain,(
    ! [A_281,C_282,E_283] :
      ( v1_funct_1(k10_tmap_1(A_281,'#skF_2',C_282,'#skF_4',E_283,'#skF_6'))
      | ~ m1_subset_1(E_283,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_282),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_283,u1_struct_0(C_282),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_283)
      | ~ m1_pre_topc('#skF_4',A_281)
      | ~ m1_pre_topc(C_282,A_281)
      | v2_struct_0(C_282)
      | ~ l1_pre_topc(A_281)
      | ~ v2_pre_topc(A_281)
      | v2_struct_0(A_281) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_80,c_379])).

tff(c_413,plain,(
    ! [A_281] :
      ( v1_funct_1(k10_tmap_1(A_281,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_281)
      | ~ m1_pre_topc('#skF_3',A_281)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_281)
      | ~ v2_pre_topc(A_281)
      | v2_struct_0(A_281) ) ),
    inference(resolution,[status(thm)],[c_68,c_408])).

tff(c_422,plain,(
    ! [A_281] :
      ( v1_funct_1(k10_tmap_1(A_281,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc('#skF_4',A_281)
      | ~ m1_pre_topc('#skF_3',A_281)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_281)
      | ~ v2_pre_topc(A_281)
      | v2_struct_0(A_281) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_413])).

tff(c_429,plain,(
    ! [A_285] :
      ( v1_funct_1(k10_tmap_1(A_285,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc('#skF_4',A_285)
      | ~ m1_pre_topc('#skF_3',A_285)
      | ~ l1_pre_topc(A_285)
      | ~ v2_pre_topc(A_285)
      | v2_struct_0(A_285) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_422])).

tff(c_54,plain,
    ( ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_148,plain,(
    ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_432,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_429,c_148])).

tff(c_435,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_82,c_78,c_432])).

tff(c_437,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_435])).

tff(c_439,plain,(
    v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_911,plain,(
    ! [F_446,A_449,D_445,C_448,B_447,E_450] :
      ( m1_subset_1(k10_tmap_1(A_449,B_447,C_448,D_445,E_450,F_446),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_449,C_448,D_445)),u1_struct_0(B_447))))
      | ~ m1_subset_1(F_446,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_445),u1_struct_0(B_447))))
      | ~ v1_funct_2(F_446,u1_struct_0(D_445),u1_struct_0(B_447))
      | ~ v1_funct_1(F_446)
      | ~ m1_subset_1(E_450,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_448),u1_struct_0(B_447))))
      | ~ v1_funct_2(E_450,u1_struct_0(C_448),u1_struct_0(B_447))
      | ~ v1_funct_1(E_450)
      | ~ m1_pre_topc(D_445,A_449)
      | v2_struct_0(D_445)
      | ~ m1_pre_topc(C_448,A_449)
      | v2_struct_0(C_448)
      | ~ l1_pre_topc(B_447)
      | ~ v2_pre_topc(B_447)
      | v2_struct_0(B_447)
      | ~ l1_pre_topc(A_449)
      | ~ v2_pre_topc(A_449)
      | v2_struct_0(A_449) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_438,plain,
    ( ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_550,plain,(
    ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_438])).

tff(c_936,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_911,c_550])).

tff(c_959,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_88,c_86,c_82,c_78,c_74,c_72,c_68,c_66,c_64,c_60,c_936])).

tff(c_961,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_90,c_84,c_80,c_959])).

tff(c_963,plain,(
    m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_438])).

tff(c_16,plain,(
    ! [D_14,E_15,B_12,A_11,C_13] :
      ( v1_funct_1(k3_tmap_1(A_11,B_12,C_13,D_14,E_15))
      | ~ m1_subset_1(E_15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_13),u1_struct_0(B_12))))
      | ~ v1_funct_2(E_15,u1_struct_0(C_13),u1_struct_0(B_12))
      | ~ v1_funct_1(E_15)
      | ~ m1_pre_topc(D_14,A_11)
      | ~ m1_pre_topc(C_13,A_11)
      | ~ l1_pre_topc(B_12)
      | ~ v2_pre_topc(B_12)
      | v2_struct_0(B_12)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_965,plain,(
    ! [A_11,D_14] :
      ( v1_funct_1(k3_tmap_1(A_11,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_14,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc(D_14,A_11)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_11)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(resolution,[status(thm)],[c_963,c_16])).

tff(c_970,plain,(
    ! [A_11,D_14] :
      ( v1_funct_1(k3_tmap_1(A_11,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_14,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_14,A_11)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_11)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_439,c_965])).

tff(c_971,plain,(
    ! [A_11,D_14] :
      ( v1_funct_1(k3_tmap_1(A_11,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_14,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_14,A_11)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_11)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_970])).

tff(c_975,plain,(
    ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_971])).

tff(c_1233,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1230,c_975])).

tff(c_1236,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_88,c_86,c_82,c_78,c_74,c_72,c_68,c_66,c_64,c_60,c_1233])).

tff(c_1238,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_90,c_84,c_80,c_1236])).

tff(c_1240,plain,(
    v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_971])).

tff(c_962,plain,
    ( ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_438])).

tff(c_1242,plain,(
    ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1240,c_962])).

tff(c_56,plain,(
    r4_tsep_1('#skF_1','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_50,plain,(
    ! [A_125] :
      ( m1_pre_topc(A_125,A_125)
      | ~ l1_pre_topc(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_48,plain,(
    ! [A_110,B_118,D_124,C_122] :
      ( m1_pre_topc(k1_tsep_1(A_110,B_118,D_124),C_122)
      | ~ m1_pre_topc(D_124,C_122)
      | ~ m1_pre_topc(B_118,C_122)
      | ~ m1_pre_topc(D_124,A_110)
      | v2_struct_0(D_124)
      | ~ m1_pre_topc(C_122,A_110)
      | v2_struct_0(C_122)
      | ~ m1_pre_topc(B_118,A_110)
      | v2_struct_0(B_118)
      | ~ l1_pre_topc(A_110)
      | ~ v2_pre_topc(A_110)
      | v2_struct_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_1260,plain,(
    ! [E_537,D_536,C_533,A_534,B_535] :
      ( v1_funct_2(k3_tmap_1(A_534,B_535,C_533,D_536,E_537),u1_struct_0(D_536),u1_struct_0(B_535))
      | ~ m1_subset_1(E_537,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_533),u1_struct_0(B_535))))
      | ~ v1_funct_2(E_537,u1_struct_0(C_533),u1_struct_0(B_535))
      | ~ v1_funct_1(E_537)
      | ~ m1_pre_topc(D_536,A_534)
      | ~ m1_pre_topc(C_533,A_534)
      | ~ l1_pre_topc(B_535)
      | ~ v2_pre_topc(B_535)
      | v2_struct_0(B_535)
      | ~ l1_pre_topc(A_534)
      | ~ v2_pre_topc(A_534)
      | v2_struct_0(A_534) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1262,plain,(
    ! [A_534,D_536] :
      ( v1_funct_2(k3_tmap_1(A_534,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_536,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_536),u1_struct_0('#skF_2'))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc(D_536,A_534)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_534)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_534)
      | ~ v2_pre_topc(A_534)
      | v2_struct_0(A_534) ) ),
    inference(resolution,[status(thm)],[c_963,c_1260])).

tff(c_1269,plain,(
    ! [A_534,D_536] :
      ( v1_funct_2(k3_tmap_1(A_534,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_536,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_536),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_536,A_534)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_534)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_534)
      | ~ v2_pre_topc(A_534)
      | v2_struct_0(A_534) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_439,c_1240,c_1262])).

tff(c_1270,plain,(
    ! [A_534,D_536] :
      ( v1_funct_2(k3_tmap_1(A_534,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_536,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_536),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_536,A_534)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_534)
      | ~ l1_pre_topc(A_534)
      | ~ v2_pre_topc(A_534)
      | v2_struct_0(A_534) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_1269])).

tff(c_12,plain,(
    ! [D_14,E_15,B_12,A_11,C_13] :
      ( m1_subset_1(k3_tmap_1(A_11,B_12,C_13,D_14,E_15),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_14),u1_struct_0(B_12))))
      | ~ m1_subset_1(E_15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_13),u1_struct_0(B_12))))
      | ~ v1_funct_2(E_15,u1_struct_0(C_13),u1_struct_0(B_12))
      | ~ v1_funct_1(E_15)
      | ~ m1_pre_topc(D_14,A_11)
      | ~ m1_pre_topc(C_13,A_11)
      | ~ l1_pre_topc(B_12)
      | ~ v2_pre_topc(B_12)
      | v2_struct_0(B_12)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1239,plain,(
    ! [A_11,D_14] :
      ( v1_funct_1(k3_tmap_1(A_11,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_14,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ m1_pre_topc(D_14,A_11)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_11)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(splitRight,[status(thm)],[c_971])).

tff(c_76,plain,(
    ~ r1_tsep_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_58,plain,(
    r2_funct_2(u1_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_3',k2_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_5'),k3_tmap_1('#skF_1','#skF_2','#skF_4',k2_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_2089,plain,(
    ! [C_702,B_703,D_699,A_698,E_700,F_701] :
      ( r2_funct_2(u1_struct_0(C_702),u1_struct_0(B_703),k3_tmap_1(A_698,B_703,k1_tsep_1(A_698,C_702,D_699),C_702,k10_tmap_1(A_698,B_703,C_702,D_699,E_700,F_701)),E_700)
      | ~ r2_funct_2(u1_struct_0(k2_tsep_1(A_698,C_702,D_699)),u1_struct_0(B_703),k3_tmap_1(A_698,B_703,C_702,k2_tsep_1(A_698,C_702,D_699),E_700),k3_tmap_1(A_698,B_703,D_699,k2_tsep_1(A_698,C_702,D_699),F_701))
      | ~ m1_subset_1(F_701,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_699),u1_struct_0(B_703))))
      | ~ v1_funct_2(F_701,u1_struct_0(D_699),u1_struct_0(B_703))
      | ~ v1_funct_1(F_701)
      | ~ m1_subset_1(E_700,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_702),u1_struct_0(B_703))))
      | ~ v1_funct_2(E_700,u1_struct_0(C_702),u1_struct_0(B_703))
      | ~ v1_funct_1(E_700)
      | r1_tsep_1(C_702,D_699)
      | ~ m1_pre_topc(D_699,A_698)
      | v2_struct_0(D_699)
      | ~ m1_pre_topc(C_702,A_698)
      | v2_struct_0(C_702)
      | ~ l1_pre_topc(B_703)
      | ~ v2_pre_topc(B_703)
      | v2_struct_0(B_703)
      | ~ l1_pre_topc(A_698)
      | ~ v2_pre_topc(A_698)
      | v2_struct_0(A_698) ) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_2094,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | r1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_2089])).

tff(c_2098,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5')
    | r1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_88,c_86,c_82,c_78,c_74,c_72,c_68,c_66,c_64,c_60,c_2094])).

tff(c_2099,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_90,c_84,c_80,c_76,c_2098])).

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

tff(c_2101,plain,
    ( k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_2099,c_4])).

tff(c_2104,plain,
    ( k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5'
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_2101])).

tff(c_2117,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_2104])).

tff(c_2120,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1239,c_2117])).

tff(c_2123,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_82,c_2120])).

tff(c_2124,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_2123])).

tff(c_2145,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_2124])).

tff(c_2164,plain,
    ( v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_82,c_78,c_2145])).

tff(c_2165,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_84,c_80,c_2164])).

tff(c_2168,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_2165])).

tff(c_2172,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_2168])).

tff(c_2173,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2104])).

tff(c_2198,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_2173])).

tff(c_2204,plain,
    ( ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_2198])).

tff(c_2211,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_88,c_86,c_82,c_439,c_1240,c_963,c_2204])).

tff(c_2212,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_90,c_2211])).

tff(c_2227,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_2212])).

tff(c_2246,plain,
    ( v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_82,c_78,c_2227])).

tff(c_2247,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_84,c_80,c_2246])).

tff(c_2250,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_2247])).

tff(c_2254,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_2250])).

tff(c_2255,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2173])).

tff(c_2298,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2255])).

tff(c_2301,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1270,c_2298])).

tff(c_2304,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_82,c_2301])).

tff(c_2305,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_2304])).

tff(c_2320,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_2305])).

tff(c_2339,plain,
    ( v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_82,c_78,c_2320])).

tff(c_2340,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_84,c_80,c_2339])).

tff(c_2343,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_2340])).

tff(c_2347,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_2343])).

tff(c_2348,plain,(
    k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2255])).

tff(c_70,plain,(
    v5_pre_topc('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_1794,plain,(
    ! [D_687,E_688,B_691,A_686,C_690,F_689] :
      ( r2_funct_2(u1_struct_0(D_687),u1_struct_0(B_691),k3_tmap_1(A_686,B_691,k1_tsep_1(A_686,C_690,D_687),D_687,k10_tmap_1(A_686,B_691,C_690,D_687,E_688,F_689)),F_689)
      | ~ r2_funct_2(u1_struct_0(k2_tsep_1(A_686,C_690,D_687)),u1_struct_0(B_691),k3_tmap_1(A_686,B_691,C_690,k2_tsep_1(A_686,C_690,D_687),E_688),k3_tmap_1(A_686,B_691,D_687,k2_tsep_1(A_686,C_690,D_687),F_689))
      | ~ m1_subset_1(F_689,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_687),u1_struct_0(B_691))))
      | ~ v1_funct_2(F_689,u1_struct_0(D_687),u1_struct_0(B_691))
      | ~ v1_funct_1(F_689)
      | ~ m1_subset_1(E_688,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_690),u1_struct_0(B_691))))
      | ~ v1_funct_2(E_688,u1_struct_0(C_690),u1_struct_0(B_691))
      | ~ v1_funct_1(E_688)
      | r1_tsep_1(C_690,D_687)
      | ~ m1_pre_topc(D_687,A_686)
      | v2_struct_0(D_687)
      | ~ m1_pre_topc(C_690,A_686)
      | v2_struct_0(C_690)
      | ~ l1_pre_topc(B_691)
      | ~ v2_pre_topc(B_691)
      | v2_struct_0(B_691)
      | ~ l1_pre_topc(A_686)
      | ~ v2_pre_topc(A_686)
      | v2_struct_0(A_686) ) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_1799,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | r1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_1794])).

tff(c_1803,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6')
    | r1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_88,c_86,c_82,c_78,c_74,c_72,c_68,c_66,c_64,c_60,c_1799])).

tff(c_1804,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_90,c_84,c_80,c_76,c_1803])).

tff(c_1806,plain,
    ( k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_1804,c_4])).

tff(c_1809,plain,
    ( k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6'
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_1806])).

tff(c_1810,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_1809])).

tff(c_1813,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1239,c_1810])).

tff(c_1816,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_78,c_1813])).

tff(c_1817,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_1816])).

tff(c_1832,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_1817])).

tff(c_1851,plain,
    ( v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_82,c_78,c_1832])).

tff(c_1852,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_84,c_80,c_1851])).

tff(c_1855,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_1852])).

tff(c_1859,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_1855])).

tff(c_1860,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1809])).

tff(c_1862,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_1860])).

tff(c_1868,plain,
    ( ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_1862])).

tff(c_1875,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_88,c_86,c_78,c_439,c_1240,c_963,c_1868])).

tff(c_1876,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_90,c_1875])).

tff(c_1891,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_1876])).

tff(c_1910,plain,
    ( v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_82,c_78,c_1891])).

tff(c_1911,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_84,c_80,c_1910])).

tff(c_1925,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_1911])).

tff(c_1929,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_1925])).

tff(c_1930,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1860])).

tff(c_1967,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1930])).

tff(c_1971,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1270,c_1967])).

tff(c_1974,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_78,c_1971])).

tff(c_1975,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_1974])).

tff(c_1990,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_1975])).

tff(c_2009,plain,
    ( v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_82,c_78,c_1990])).

tff(c_2010,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_84,c_80,c_2009])).

tff(c_2013,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_2010])).

tff(c_2017,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_2013])).

tff(c_2018,plain,(
    k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1930])).

tff(c_62,plain,(
    v5_pre_topc('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_331])).

tff(c_2425,plain,(
    ! [C_724,B_721,D_723,E_722,A_725] :
      ( v5_pre_topc(E_722,k1_tsep_1(A_725,C_724,D_723),B_721)
      | ~ m1_subset_1(k3_tmap_1(A_725,B_721,k1_tsep_1(A_725,C_724,D_723),D_723,E_722),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_723),u1_struct_0(B_721))))
      | ~ v5_pre_topc(k3_tmap_1(A_725,B_721,k1_tsep_1(A_725,C_724,D_723),D_723,E_722),D_723,B_721)
      | ~ v1_funct_2(k3_tmap_1(A_725,B_721,k1_tsep_1(A_725,C_724,D_723),D_723,E_722),u1_struct_0(D_723),u1_struct_0(B_721))
      | ~ v1_funct_1(k3_tmap_1(A_725,B_721,k1_tsep_1(A_725,C_724,D_723),D_723,E_722))
      | ~ m1_subset_1(k3_tmap_1(A_725,B_721,k1_tsep_1(A_725,C_724,D_723),C_724,E_722),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_724),u1_struct_0(B_721))))
      | ~ v5_pre_topc(k3_tmap_1(A_725,B_721,k1_tsep_1(A_725,C_724,D_723),C_724,E_722),C_724,B_721)
      | ~ v1_funct_2(k3_tmap_1(A_725,B_721,k1_tsep_1(A_725,C_724,D_723),C_724,E_722),u1_struct_0(C_724),u1_struct_0(B_721))
      | ~ v1_funct_1(k3_tmap_1(A_725,B_721,k1_tsep_1(A_725,C_724,D_723),C_724,E_722))
      | ~ m1_subset_1(E_722,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_725,C_724,D_723)),u1_struct_0(B_721))))
      | ~ v1_funct_2(E_722,u1_struct_0(k1_tsep_1(A_725,C_724,D_723)),u1_struct_0(B_721))
      | ~ v1_funct_1(E_722)
      | ~ r4_tsep_1(A_725,C_724,D_723)
      | ~ m1_pre_topc(D_723,A_725)
      | v2_struct_0(D_723)
      | ~ m1_pre_topc(C_724,A_725)
      | v2_struct_0(C_724)
      | ~ l1_pre_topc(B_721)
      | ~ v2_pre_topc(B_721)
      | v2_struct_0(B_721)
      | ~ l1_pre_topc(A_725)
      | ~ v2_pre_topc(A_725)
      | v2_struct_0(A_725) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_2427,plain,
    ( v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_4','#skF_2')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_3','#skF_2')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2018,c_2425])).

tff(c_2437,plain,
    ( v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_88,c_86,c_82,c_78,c_56,c_439,c_1240,c_963,c_74,c_2348,c_72,c_2348,c_70,c_2348,c_68,c_2348,c_66,c_2018,c_64,c_2018,c_62,c_2018,c_60,c_2427])).

tff(c_2439,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_90,c_84,c_80,c_1242,c_2437])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:30:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.85/2.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.85/2.61  
% 7.85/2.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.85/2.61  %$ r2_funct_2 > v5_pre_topc > v1_funct_2 > r4_tsep_1 > r1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k2_tsep_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.85/2.61  
% 7.85/2.61  %Foreground sorts:
% 7.85/2.61  
% 7.85/2.61  
% 7.85/2.61  %Background operators:
% 7.85/2.61  
% 7.85/2.61  
% 7.85/2.61  %Foreground operators:
% 7.85/2.61  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.85/2.61  tff(k10_tmap_1, type, k10_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.85/2.61  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 7.85/2.61  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 7.85/2.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.85/2.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.85/2.61  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.85/2.61  tff(r4_tsep_1, type, r4_tsep_1: ($i * $i * $i) > $o).
% 7.85/2.61  tff('#skF_5', type, '#skF_5': $i).
% 7.85/2.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.85/2.61  tff('#skF_6', type, '#skF_6': $i).
% 7.85/2.61  tff('#skF_2', type, '#skF_2': $i).
% 7.85/2.61  tff('#skF_3', type, '#skF_3': $i).
% 7.85/2.61  tff('#skF_1', type, '#skF_1': $i).
% 7.85/2.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.85/2.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.85/2.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.85/2.61  tff('#skF_4', type, '#skF_4': $i).
% 7.85/2.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.85/2.61  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 7.85/2.61  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.85/2.61  tff(k2_tsep_1, type, k2_tsep_1: ($i * $i * $i) > $i).
% 7.85/2.61  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.85/2.61  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 7.85/2.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.85/2.61  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 7.85/2.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.85/2.61  
% 7.85/2.65  tff(f_331, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (~r1_tsep_1(C, D) => (![E]: ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: ((((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((r2_funct_2(u1_struct_0(k2_tsep_1(A, C, D)), u1_struct_0(B), k3_tmap_1(A, B, C, k2_tsep_1(A, C, D), E), k3_tmap_1(A, B, D, k2_tsep_1(A, C, D), F)) & r4_tsep_1(A, C, D)) => (((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & v5_pre_topc(k10_tmap_1(A, B, C, D, E, F), k1_tsep_1(A, C, D), B)) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_tmap_1)).
% 7.85/2.65  tff(f_83, axiom, (![A, B, C, D, E, F]: ((((((((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) & ~v2_struct_0(D)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(F)) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_tmap_1)).
% 7.85/2.65  tff(f_113, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 7.85/2.65  tff(f_258, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 7.85/2.65  tff(f_254, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => ((m1_pre_topc(B, C) & m1_pre_topc(D, C)) => m1_pre_topc(k1_tsep_1(A, B, D), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tmap_1)).
% 7.85/2.65  tff(f_223, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (~r1_tsep_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, k10_tmap_1(A, B, C, D, E, F)), E) & r2_funct_2(u1_struct_0(D), u1_struct_0(B), k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, k10_tmap_1(A, B, C, D, E, F)), F)) <=> r2_funct_2(u1_struct_0(k2_tsep_1(A, C, D)), u1_struct_0(B), k3_tmap_1(A, B, C, k2_tsep_1(A, C, D), E), k3_tmap_1(A, B, D, k2_tsep_1(A, C, D), F)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_tmap_1)).
% 7.85/2.65  tff(f_41, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 7.85/2.65  tff(f_173, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (r4_tsep_1(A, C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) => ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & v5_pre_topc(E, k1_tsep_1(A, C, D), B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) <=> (((((((v1_funct_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E)) & v1_funct_2(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), C, B)) & m1_subset_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E))) & v1_funct_2(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), D, B)) & m1_subset_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t126_tmap_1)).
% 7.85/2.65  tff(c_96, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.85/2.65  tff(c_90, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.85/2.65  tff(c_84, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.85/2.65  tff(c_80, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.85/2.65  tff(c_94, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.85/2.65  tff(c_92, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.85/2.65  tff(c_88, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.85/2.65  tff(c_86, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.85/2.65  tff(c_82, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.85/2.65  tff(c_78, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.85/2.65  tff(c_74, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.85/2.65  tff(c_72, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.85/2.65  tff(c_68, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.85/2.65  tff(c_66, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.85/2.65  tff(c_64, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.85/2.65  tff(c_60, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.85/2.65  tff(c_1230, plain, (![B_527, D_525, E_530, F_526, C_528, A_529]: (v1_funct_2(k10_tmap_1(A_529, B_527, C_528, D_525, E_530, F_526), u1_struct_0(k1_tsep_1(A_529, C_528, D_525)), u1_struct_0(B_527)) | ~m1_subset_1(F_526, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_525), u1_struct_0(B_527)))) | ~v1_funct_2(F_526, u1_struct_0(D_525), u1_struct_0(B_527)) | ~v1_funct_1(F_526) | ~m1_subset_1(E_530, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_528), u1_struct_0(B_527)))) | ~v1_funct_2(E_530, u1_struct_0(C_528), u1_struct_0(B_527)) | ~v1_funct_1(E_530) | ~m1_pre_topc(D_525, A_529) | v2_struct_0(D_525) | ~m1_pre_topc(C_528, A_529) | v2_struct_0(C_528) | ~l1_pre_topc(B_527) | ~v2_pre_topc(B_527) | v2_struct_0(B_527) | ~l1_pre_topc(A_529) | ~v2_pre_topc(A_529) | v2_struct_0(A_529))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.85/2.65  tff(c_365, plain, (![A_269, B_267, D_265, E_270, C_268, F_266]: (v1_funct_1(k10_tmap_1(A_269, B_267, C_268, D_265, E_270, F_266)) | ~m1_subset_1(F_266, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_265), u1_struct_0(B_267)))) | ~v1_funct_2(F_266, u1_struct_0(D_265), u1_struct_0(B_267)) | ~v1_funct_1(F_266) | ~m1_subset_1(E_270, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_268), u1_struct_0(B_267)))) | ~v1_funct_2(E_270, u1_struct_0(C_268), u1_struct_0(B_267)) | ~v1_funct_1(E_270) | ~m1_pre_topc(D_265, A_269) | v2_struct_0(D_265) | ~m1_pre_topc(C_268, A_269) | v2_struct_0(C_268) | ~l1_pre_topc(B_267) | ~v2_pre_topc(B_267) | v2_struct_0(B_267) | ~l1_pre_topc(A_269) | ~v2_pre_topc(A_269) | v2_struct_0(A_269))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.85/2.65  tff(c_371, plain, (![A_269, C_268, E_270]: (v1_funct_1(k10_tmap_1(A_269, '#skF_2', C_268, '#skF_4', E_270, '#skF_6')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_270, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_268), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_270, u1_struct_0(C_268), u1_struct_0('#skF_2')) | ~v1_funct_1(E_270) | ~m1_pre_topc('#skF_4', A_269) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_268, A_269) | v2_struct_0(C_268) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_269) | ~v2_pre_topc(A_269) | v2_struct_0(A_269))), inference(resolution, [status(thm)], [c_60, c_365])).
% 7.85/2.65  tff(c_379, plain, (![A_269, C_268, E_270]: (v1_funct_1(k10_tmap_1(A_269, '#skF_2', C_268, '#skF_4', E_270, '#skF_6')) | ~m1_subset_1(E_270, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_268), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_270, u1_struct_0(C_268), u1_struct_0('#skF_2')) | ~v1_funct_1(E_270) | ~m1_pre_topc('#skF_4', A_269) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_268, A_269) | v2_struct_0(C_268) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_269) | ~v2_pre_topc(A_269) | v2_struct_0(A_269))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_66, c_64, c_371])).
% 7.85/2.65  tff(c_408, plain, (![A_281, C_282, E_283]: (v1_funct_1(k10_tmap_1(A_281, '#skF_2', C_282, '#skF_4', E_283, '#skF_6')) | ~m1_subset_1(E_283, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_282), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_283, u1_struct_0(C_282), u1_struct_0('#skF_2')) | ~v1_funct_1(E_283) | ~m1_pre_topc('#skF_4', A_281) | ~m1_pre_topc(C_282, A_281) | v2_struct_0(C_282) | ~l1_pre_topc(A_281) | ~v2_pre_topc(A_281) | v2_struct_0(A_281))), inference(negUnitSimplification, [status(thm)], [c_90, c_80, c_379])).
% 7.85/2.65  tff(c_413, plain, (![A_281]: (v1_funct_1(k10_tmap_1(A_281, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_281) | ~m1_pre_topc('#skF_3', A_281) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_281) | ~v2_pre_topc(A_281) | v2_struct_0(A_281))), inference(resolution, [status(thm)], [c_68, c_408])).
% 7.85/2.65  tff(c_422, plain, (![A_281]: (v1_funct_1(k10_tmap_1(A_281, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', A_281) | ~m1_pre_topc('#skF_3', A_281) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_281) | ~v2_pre_topc(A_281) | v2_struct_0(A_281))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_413])).
% 7.85/2.65  tff(c_429, plain, (![A_285]: (v1_funct_1(k10_tmap_1(A_285, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', A_285) | ~m1_pre_topc('#skF_3', A_285) | ~l1_pre_topc(A_285) | ~v2_pre_topc(A_285) | v2_struct_0(A_285))), inference(negUnitSimplification, [status(thm)], [c_84, c_422])).
% 7.85/2.65  tff(c_54, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.85/2.65  tff(c_148, plain, (~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_54])).
% 7.85/2.65  tff(c_432, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_429, c_148])).
% 7.85/2.65  tff(c_435, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_82, c_78, c_432])).
% 7.85/2.65  tff(c_437, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_435])).
% 7.85/2.65  tff(c_439, plain, (v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_54])).
% 7.85/2.65  tff(c_911, plain, (![F_446, A_449, D_445, C_448, B_447, E_450]: (m1_subset_1(k10_tmap_1(A_449, B_447, C_448, D_445, E_450, F_446), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_449, C_448, D_445)), u1_struct_0(B_447)))) | ~m1_subset_1(F_446, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_445), u1_struct_0(B_447)))) | ~v1_funct_2(F_446, u1_struct_0(D_445), u1_struct_0(B_447)) | ~v1_funct_1(F_446) | ~m1_subset_1(E_450, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_448), u1_struct_0(B_447)))) | ~v1_funct_2(E_450, u1_struct_0(C_448), u1_struct_0(B_447)) | ~v1_funct_1(E_450) | ~m1_pre_topc(D_445, A_449) | v2_struct_0(D_445) | ~m1_pre_topc(C_448, A_449) | v2_struct_0(C_448) | ~l1_pre_topc(B_447) | ~v2_pre_topc(B_447) | v2_struct_0(B_447) | ~l1_pre_topc(A_449) | ~v2_pre_topc(A_449) | v2_struct_0(A_449))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.85/2.65  tff(c_438, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_54])).
% 7.85/2.65  tff(c_550, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_438])).
% 7.85/2.65  tff(c_936, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_911, c_550])).
% 7.85/2.65  tff(c_959, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_88, c_86, c_82, c_78, c_74, c_72, c_68, c_66, c_64, c_60, c_936])).
% 7.85/2.65  tff(c_961, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_90, c_84, c_80, c_959])).
% 7.85/2.65  tff(c_963, plain, (m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_438])).
% 7.85/2.65  tff(c_16, plain, (![D_14, E_15, B_12, A_11, C_13]: (v1_funct_1(k3_tmap_1(A_11, B_12, C_13, D_14, E_15)) | ~m1_subset_1(E_15, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_13), u1_struct_0(B_12)))) | ~v1_funct_2(E_15, u1_struct_0(C_13), u1_struct_0(B_12)) | ~v1_funct_1(E_15) | ~m1_pre_topc(D_14, A_11) | ~m1_pre_topc(C_13, A_11) | ~l1_pre_topc(B_12) | ~v2_pre_topc(B_12) | v2_struct_0(B_12) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.85/2.65  tff(c_965, plain, (![A_11, D_14]: (v1_funct_1(k3_tmap_1(A_11, '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), D_14, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc(D_14, A_11) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_11) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(resolution, [status(thm)], [c_963, c_16])).
% 7.85/2.65  tff(c_970, plain, (![A_11, D_14]: (v1_funct_1(k3_tmap_1(A_11, '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), D_14, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_14, A_11) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_11) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_439, c_965])).
% 7.85/2.65  tff(c_971, plain, (![A_11, D_14]: (v1_funct_1(k3_tmap_1(A_11, '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), D_14, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_14, A_11) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_11) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(negUnitSimplification, [status(thm)], [c_90, c_970])).
% 7.85/2.65  tff(c_975, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_971])).
% 7.85/2.65  tff(c_1233, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1230, c_975])).
% 7.85/2.65  tff(c_1236, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_88, c_86, c_82, c_78, c_74, c_72, c_68, c_66, c_64, c_60, c_1233])).
% 7.85/2.65  tff(c_1238, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_90, c_84, c_80, c_1236])).
% 7.85/2.65  tff(c_1240, plain, (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_971])).
% 7.85/2.65  tff(c_962, plain, (~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_438])).
% 7.85/2.65  tff(c_1242, plain, (~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1240, c_962])).
% 7.85/2.65  tff(c_56, plain, (r4_tsep_1('#skF_1', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.85/2.65  tff(c_50, plain, (![A_125]: (m1_pre_topc(A_125, A_125) | ~l1_pre_topc(A_125))), inference(cnfTransformation, [status(thm)], [f_258])).
% 7.85/2.65  tff(c_48, plain, (![A_110, B_118, D_124, C_122]: (m1_pre_topc(k1_tsep_1(A_110, B_118, D_124), C_122) | ~m1_pre_topc(D_124, C_122) | ~m1_pre_topc(B_118, C_122) | ~m1_pre_topc(D_124, A_110) | v2_struct_0(D_124) | ~m1_pre_topc(C_122, A_110) | v2_struct_0(C_122) | ~m1_pre_topc(B_118, A_110) | v2_struct_0(B_118) | ~l1_pre_topc(A_110) | ~v2_pre_topc(A_110) | v2_struct_0(A_110))), inference(cnfTransformation, [status(thm)], [f_254])).
% 7.85/2.65  tff(c_1260, plain, (![E_537, D_536, C_533, A_534, B_535]: (v1_funct_2(k3_tmap_1(A_534, B_535, C_533, D_536, E_537), u1_struct_0(D_536), u1_struct_0(B_535)) | ~m1_subset_1(E_537, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_533), u1_struct_0(B_535)))) | ~v1_funct_2(E_537, u1_struct_0(C_533), u1_struct_0(B_535)) | ~v1_funct_1(E_537) | ~m1_pre_topc(D_536, A_534) | ~m1_pre_topc(C_533, A_534) | ~l1_pre_topc(B_535) | ~v2_pre_topc(B_535) | v2_struct_0(B_535) | ~l1_pre_topc(A_534) | ~v2_pre_topc(A_534) | v2_struct_0(A_534))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.85/2.65  tff(c_1262, plain, (![A_534, D_536]: (v1_funct_2(k3_tmap_1(A_534, '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), D_536, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0(D_536), u1_struct_0('#skF_2')) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc(D_536, A_534) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_534) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_534) | ~v2_pre_topc(A_534) | v2_struct_0(A_534))), inference(resolution, [status(thm)], [c_963, c_1260])).
% 7.85/2.65  tff(c_1269, plain, (![A_534, D_536]: (v1_funct_2(k3_tmap_1(A_534, '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), D_536, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0(D_536), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_536, A_534) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_534) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_534) | ~v2_pre_topc(A_534) | v2_struct_0(A_534))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_439, c_1240, c_1262])).
% 7.85/2.65  tff(c_1270, plain, (![A_534, D_536]: (v1_funct_2(k3_tmap_1(A_534, '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), D_536, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0(D_536), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_536, A_534) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_534) | ~l1_pre_topc(A_534) | ~v2_pre_topc(A_534) | v2_struct_0(A_534))), inference(negUnitSimplification, [status(thm)], [c_90, c_1269])).
% 7.85/2.65  tff(c_12, plain, (![D_14, E_15, B_12, A_11, C_13]: (m1_subset_1(k3_tmap_1(A_11, B_12, C_13, D_14, E_15), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_14), u1_struct_0(B_12)))) | ~m1_subset_1(E_15, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_13), u1_struct_0(B_12)))) | ~v1_funct_2(E_15, u1_struct_0(C_13), u1_struct_0(B_12)) | ~v1_funct_1(E_15) | ~m1_pre_topc(D_14, A_11) | ~m1_pre_topc(C_13, A_11) | ~l1_pre_topc(B_12) | ~v2_pre_topc(B_12) | v2_struct_0(B_12) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.85/2.65  tff(c_1239, plain, (![A_11, D_14]: (v1_funct_1(k3_tmap_1(A_11, '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), D_14, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_pre_topc(D_14, A_11) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_11) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(splitRight, [status(thm)], [c_971])).
% 7.85/2.65  tff(c_76, plain, (~r1_tsep_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.85/2.65  tff(c_58, plain, (r2_funct_2(u1_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_3', k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_5'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.85/2.65  tff(c_2089, plain, (![C_702, B_703, D_699, A_698, E_700, F_701]: (r2_funct_2(u1_struct_0(C_702), u1_struct_0(B_703), k3_tmap_1(A_698, B_703, k1_tsep_1(A_698, C_702, D_699), C_702, k10_tmap_1(A_698, B_703, C_702, D_699, E_700, F_701)), E_700) | ~r2_funct_2(u1_struct_0(k2_tsep_1(A_698, C_702, D_699)), u1_struct_0(B_703), k3_tmap_1(A_698, B_703, C_702, k2_tsep_1(A_698, C_702, D_699), E_700), k3_tmap_1(A_698, B_703, D_699, k2_tsep_1(A_698, C_702, D_699), F_701)) | ~m1_subset_1(F_701, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_699), u1_struct_0(B_703)))) | ~v1_funct_2(F_701, u1_struct_0(D_699), u1_struct_0(B_703)) | ~v1_funct_1(F_701) | ~m1_subset_1(E_700, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_702), u1_struct_0(B_703)))) | ~v1_funct_2(E_700, u1_struct_0(C_702), u1_struct_0(B_703)) | ~v1_funct_1(E_700) | r1_tsep_1(C_702, D_699) | ~m1_pre_topc(D_699, A_698) | v2_struct_0(D_699) | ~m1_pre_topc(C_702, A_698) | v2_struct_0(C_702) | ~l1_pre_topc(B_703) | ~v2_pre_topc(B_703) | v2_struct_0(B_703) | ~l1_pre_topc(A_698) | ~v2_pre_topc(A_698) | v2_struct_0(A_698))), inference(cnfTransformation, [status(thm)], [f_223])).
% 7.85/2.65  tff(c_2094, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | r1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_58, c_2089])).
% 7.85/2.65  tff(c_2098, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5') | r1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_88, c_86, c_82, c_78, c_74, c_72, c_68, c_66, c_64, c_60, c_2094])).
% 7.85/2.65  tff(c_2099, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_96, c_90, c_84, c_80, c_76, c_2098])).
% 7.85/2.65  tff(c_4, plain, (![D_4, C_3, A_1, B_2]: (D_4=C_3 | ~r2_funct_2(A_1, B_2, C_3, D_4) | ~m1_subset_1(D_4, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(D_4, A_1, B_2) | ~v1_funct_1(D_4) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(C_3, A_1, B_2) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.85/2.65  tff(c_2101, plain, (k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_2099, c_4])).
% 7.85/2.65  tff(c_2104, plain, (k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5' | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_68, c_2101])).
% 7.85/2.65  tff(c_2117, plain, (~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_2104])).
% 7.85/2.65  tff(c_2120, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1239, c_2117])).
% 7.85/2.65  tff(c_2123, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_82, c_2120])).
% 7.85/2.65  tff(c_2124, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_96, c_2123])).
% 7.85/2.65  tff(c_2145, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_2124])).
% 7.85/2.65  tff(c_2164, plain, (v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_82, c_78, c_2145])).
% 7.85/2.65  tff(c_2165, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_96, c_84, c_80, c_2164])).
% 7.85/2.65  tff(c_2168, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_2165])).
% 7.85/2.65  tff(c_2172, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_2168])).
% 7.85/2.65  tff(c_2173, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_2104])).
% 7.85/2.65  tff(c_2198, plain, (~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_2173])).
% 7.85/2.65  tff(c_2204, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_12, c_2198])).
% 7.85/2.65  tff(c_2211, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_88, c_86, c_82, c_439, c_1240, c_963, c_2204])).
% 7.85/2.65  tff(c_2212, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_96, c_90, c_2211])).
% 7.85/2.65  tff(c_2227, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_2212])).
% 7.85/2.65  tff(c_2246, plain, (v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_82, c_78, c_2227])).
% 7.85/2.65  tff(c_2247, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_96, c_84, c_80, c_2246])).
% 7.85/2.65  tff(c_2250, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_2247])).
% 7.85/2.65  tff(c_2254, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_2250])).
% 7.85/2.65  tff(c_2255, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_2173])).
% 7.85/2.65  tff(c_2298, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_2255])).
% 7.85/2.65  tff(c_2301, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1270, c_2298])).
% 7.85/2.65  tff(c_2304, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_82, c_2301])).
% 7.85/2.65  tff(c_2305, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_96, c_2304])).
% 7.85/2.65  tff(c_2320, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_2305])).
% 7.85/2.65  tff(c_2339, plain, (v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_82, c_78, c_2320])).
% 7.85/2.65  tff(c_2340, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_96, c_84, c_80, c_2339])).
% 7.85/2.65  tff(c_2343, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_2340])).
% 7.85/2.65  tff(c_2347, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_2343])).
% 7.85/2.65  tff(c_2348, plain, (k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_2255])).
% 7.85/2.65  tff(c_70, plain, (v5_pre_topc('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.85/2.65  tff(c_1794, plain, (![D_687, E_688, B_691, A_686, C_690, F_689]: (r2_funct_2(u1_struct_0(D_687), u1_struct_0(B_691), k3_tmap_1(A_686, B_691, k1_tsep_1(A_686, C_690, D_687), D_687, k10_tmap_1(A_686, B_691, C_690, D_687, E_688, F_689)), F_689) | ~r2_funct_2(u1_struct_0(k2_tsep_1(A_686, C_690, D_687)), u1_struct_0(B_691), k3_tmap_1(A_686, B_691, C_690, k2_tsep_1(A_686, C_690, D_687), E_688), k3_tmap_1(A_686, B_691, D_687, k2_tsep_1(A_686, C_690, D_687), F_689)) | ~m1_subset_1(F_689, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_687), u1_struct_0(B_691)))) | ~v1_funct_2(F_689, u1_struct_0(D_687), u1_struct_0(B_691)) | ~v1_funct_1(F_689) | ~m1_subset_1(E_688, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_690), u1_struct_0(B_691)))) | ~v1_funct_2(E_688, u1_struct_0(C_690), u1_struct_0(B_691)) | ~v1_funct_1(E_688) | r1_tsep_1(C_690, D_687) | ~m1_pre_topc(D_687, A_686) | v2_struct_0(D_687) | ~m1_pre_topc(C_690, A_686) | v2_struct_0(C_690) | ~l1_pre_topc(B_691) | ~v2_pre_topc(B_691) | v2_struct_0(B_691) | ~l1_pre_topc(A_686) | ~v2_pre_topc(A_686) | v2_struct_0(A_686))), inference(cnfTransformation, [status(thm)], [f_223])).
% 7.85/2.65  tff(c_1799, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | r1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_58, c_1794])).
% 7.85/2.65  tff(c_1803, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_6') | r1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_88, c_86, c_82, c_78, c_74, c_72, c_68, c_66, c_64, c_60, c_1799])).
% 7.85/2.65  tff(c_1804, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_96, c_90, c_84, c_80, c_76, c_1803])).
% 7.85/2.65  tff(c_1806, plain, (k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_1804, c_4])).
% 7.85/2.65  tff(c_1809, plain, (k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6' | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_1806])).
% 7.85/2.65  tff(c_1810, plain, (~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_1809])).
% 7.85/2.65  tff(c_1813, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1239, c_1810])).
% 7.85/2.65  tff(c_1816, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_78, c_1813])).
% 7.85/2.65  tff(c_1817, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_96, c_1816])).
% 7.85/2.65  tff(c_1832, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_1817])).
% 7.85/2.65  tff(c_1851, plain, (v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_82, c_78, c_1832])).
% 7.85/2.65  tff(c_1852, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_96, c_84, c_80, c_1851])).
% 7.85/2.65  tff(c_1855, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_1852])).
% 7.85/2.65  tff(c_1859, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_1855])).
% 7.85/2.65  tff(c_1860, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_1809])).
% 7.85/2.65  tff(c_1862, plain, (~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_1860])).
% 7.85/2.65  tff(c_1868, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_12, c_1862])).
% 7.85/2.65  tff(c_1875, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_88, c_86, c_78, c_439, c_1240, c_963, c_1868])).
% 7.85/2.65  tff(c_1876, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_96, c_90, c_1875])).
% 7.85/2.65  tff(c_1891, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_1876])).
% 7.85/2.65  tff(c_1910, plain, (v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_82, c_78, c_1891])).
% 7.85/2.65  tff(c_1911, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_96, c_84, c_80, c_1910])).
% 7.85/2.65  tff(c_1925, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_1911])).
% 7.85/2.65  tff(c_1929, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_1925])).
% 7.85/2.65  tff(c_1930, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_1860])).
% 7.85/2.65  tff(c_1967, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1930])).
% 7.85/2.65  tff(c_1971, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1270, c_1967])).
% 7.85/2.65  tff(c_1974, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_78, c_1971])).
% 7.85/2.65  tff(c_1975, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_96, c_1974])).
% 7.85/2.65  tff(c_1990, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_1975])).
% 7.85/2.65  tff(c_2009, plain, (v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_82, c_78, c_1990])).
% 7.85/2.65  tff(c_2010, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_96, c_84, c_80, c_2009])).
% 7.85/2.65  tff(c_2013, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_2010])).
% 7.85/2.65  tff(c_2017, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_2013])).
% 7.85/2.65  tff(c_2018, plain, (k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_1930])).
% 7.85/2.65  tff(c_62, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_331])).
% 7.85/2.65  tff(c_2425, plain, (![C_724, B_721, D_723, E_722, A_725]: (v5_pre_topc(E_722, k1_tsep_1(A_725, C_724, D_723), B_721) | ~m1_subset_1(k3_tmap_1(A_725, B_721, k1_tsep_1(A_725, C_724, D_723), D_723, E_722), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_723), u1_struct_0(B_721)))) | ~v5_pre_topc(k3_tmap_1(A_725, B_721, k1_tsep_1(A_725, C_724, D_723), D_723, E_722), D_723, B_721) | ~v1_funct_2(k3_tmap_1(A_725, B_721, k1_tsep_1(A_725, C_724, D_723), D_723, E_722), u1_struct_0(D_723), u1_struct_0(B_721)) | ~v1_funct_1(k3_tmap_1(A_725, B_721, k1_tsep_1(A_725, C_724, D_723), D_723, E_722)) | ~m1_subset_1(k3_tmap_1(A_725, B_721, k1_tsep_1(A_725, C_724, D_723), C_724, E_722), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_724), u1_struct_0(B_721)))) | ~v5_pre_topc(k3_tmap_1(A_725, B_721, k1_tsep_1(A_725, C_724, D_723), C_724, E_722), C_724, B_721) | ~v1_funct_2(k3_tmap_1(A_725, B_721, k1_tsep_1(A_725, C_724, D_723), C_724, E_722), u1_struct_0(C_724), u1_struct_0(B_721)) | ~v1_funct_1(k3_tmap_1(A_725, B_721, k1_tsep_1(A_725, C_724, D_723), C_724, E_722)) | ~m1_subset_1(E_722, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_725, C_724, D_723)), u1_struct_0(B_721)))) | ~v1_funct_2(E_722, u1_struct_0(k1_tsep_1(A_725, C_724, D_723)), u1_struct_0(B_721)) | ~v1_funct_1(E_722) | ~r4_tsep_1(A_725, C_724, D_723) | ~m1_pre_topc(D_723, A_725) | v2_struct_0(D_723) | ~m1_pre_topc(C_724, A_725) | v2_struct_0(C_724) | ~l1_pre_topc(B_721) | ~v2_pre_topc(B_721) | v2_struct_0(B_721) | ~l1_pre_topc(A_725) | ~v2_pre_topc(A_725) | v2_struct_0(A_725))), inference(cnfTransformation, [status(thm)], [f_173])).
% 7.85/2.65  tff(c_2427, plain, (v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_4', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_3', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2018, c_2425])).
% 7.85/2.65  tff(c_2437, plain, (v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_88, c_86, c_82, c_78, c_56, c_439, c_1240, c_963, c_74, c_2348, c_72, c_2348, c_70, c_2348, c_68, c_2348, c_66, c_2018, c_64, c_2018, c_62, c_2018, c_60, c_2427])).
% 7.85/2.65  tff(c_2439, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_90, c_84, c_80, c_1242, c_2437])).
% 7.85/2.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.85/2.65  
% 7.85/2.65  Inference rules
% 7.85/2.65  ----------------------
% 7.85/2.65  #Ref     : 0
% 7.85/2.65  #Sup     : 445
% 7.85/2.65  #Fact    : 0
% 7.85/2.65  #Define  : 0
% 7.85/2.65  #Split   : 15
% 7.85/2.65  #Chain   : 0
% 7.85/2.65  #Close   : 0
% 7.85/2.65  
% 7.85/2.65  Ordering : KBO
% 7.85/2.65  
% 7.85/2.65  Simplification rules
% 7.85/2.65  ----------------------
% 7.85/2.65  #Subsume      : 120
% 7.85/2.65  #Demod        : 1010
% 7.85/2.65  #Tautology    : 49
% 7.85/2.65  #SimpNegUnit  : 163
% 7.85/2.65  #BackRed      : 6
% 7.85/2.65  
% 7.85/2.65  #Partial instantiations: 0
% 7.85/2.65  #Strategies tried      : 1
% 7.85/2.65  
% 7.85/2.65  Timing (in seconds)
% 7.85/2.65  ----------------------
% 7.85/2.65  Preprocessing        : 0.49
% 7.85/2.65  Parsing              : 0.24
% 7.85/2.65  CNF conversion       : 0.08
% 7.85/2.65  Main loop            : 1.35
% 7.85/2.65  Inferencing          : 0.39
% 7.85/2.65  Reduction            : 0.37
% 7.85/2.65  Demodulation         : 0.27
% 7.85/2.65  BG Simplification    : 0.05
% 7.85/2.65  Subsumption          : 0.49
% 7.85/2.65  Abstraction          : 0.05
% 7.85/2.65  MUC search           : 0.00
% 7.85/2.65  Cooper               : 0.00
% 7.85/2.65  Total                : 1.91
% 7.85/2.65  Index Insertion      : 0.00
% 7.85/2.65  Index Deletion       : 0.00
% 7.85/2.65  Index Matching       : 0.00
% 7.85/2.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
