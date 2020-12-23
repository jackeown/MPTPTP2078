%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:21 EST 2020

% Result     : Theorem 13.59s
% Output     : CNFRefutation 13.75s
% Verified   : 
% Statistics : Number of formulae       :  287 (49775 expanded)
%              Number of leaves         :   35 (19406 expanded)
%              Depth                    :   47
%              Number of atoms          : 1586 (457269 expanded)
%              Number of equality atoms :   78 (29644 expanded)
%              Maximal formula depth    :   30 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > r1_tmap_1 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_298,negated_conjecture,(
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
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                       => ( m1_pre_topc(C,D)
                         => ! [F] :
                              ( m1_subset_1(F,u1_struct_0(D))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(C))
                                 => ( ( F = G
                                      & r1_tmap_1(D,B,k2_tmap_1(A,B,E,D),F) )
                                   => r1_tmap_1(C,B,k2_tmap_1(A,B,E,C),G) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_tmap_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_150,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_116,axiom,(
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

tff(f_84,axiom,(
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

tff(f_146,axiom,(
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

tff(f_237,axiom,(
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
                        & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,u1_struct_0(C),u1_struct_0(B))
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                         => ( ( r2_funct_2(u1_struct_0(C),u1_struct_0(B),F,k2_tmap_1(A,B,E,C))
                              & m1_pre_topc(D,C) )
                           => r2_funct_2(u1_struct_0(D),u1_struct_0(B),k3_tmap_1(A,B,C,D,F),k2_tmap_1(A,B,E,D)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tmap_1)).

tff(f_190,axiom,(
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
                & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(D))
                         => ( ( E = F
                              & r1_tmap_1(B,A,C,E) )
                           => r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),F) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_32,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_34,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_65,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34])).

tff(c_30,plain,(
    r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_38,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_62,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_60,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_46,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_95,plain,(
    ! [B_319,A_320] :
      ( v2_pre_topc(B_319)
      | ~ m1_pre_topc(B_319,A_320)
      | ~ l1_pre_topc(A_320)
      | ~ v2_pre_topc(A_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_104,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_95])).

tff(c_114,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_104])).

tff(c_72,plain,(
    ! [B_317,A_318] :
      ( l1_pre_topc(B_317)
      | ~ m1_pre_topc(B_317,A_318)
      | ~ l1_pre_topc(A_318) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_81,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_72])).

tff(c_89,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_81])).

tff(c_56,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_54,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_20,plain,(
    ! [A_62] :
      ( m1_pre_topc(A_62,A_62)
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_42,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_285,plain,(
    ! [D_365,C_364,A_362,B_366,E_363] :
      ( k3_tmap_1(A_362,B_366,C_364,D_365,E_363) = k2_partfun1(u1_struct_0(C_364),u1_struct_0(B_366),E_363,u1_struct_0(D_365))
      | ~ m1_pre_topc(D_365,C_364)
      | ~ m1_subset_1(E_363,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_364),u1_struct_0(B_366))))
      | ~ v1_funct_2(E_363,u1_struct_0(C_364),u1_struct_0(B_366))
      | ~ v1_funct_1(E_363)
      | ~ m1_pre_topc(D_365,A_362)
      | ~ m1_pre_topc(C_364,A_362)
      | ~ l1_pre_topc(B_366)
      | ~ v2_pre_topc(B_366)
      | v2_struct_0(B_366)
      | ~ l1_pre_topc(A_362)
      | ~ v2_pre_topc(A_362)
      | v2_struct_0(A_362) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_289,plain,(
    ! [A_362,D_365] :
      ( k3_tmap_1(A_362,'#skF_2','#skF_1',D_365,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_365))
      | ~ m1_pre_topc(D_365,'#skF_1')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_365,A_362)
      | ~ m1_pre_topc('#skF_1',A_362)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_362)
      | ~ v2_pre_topc(A_362)
      | v2_struct_0(A_362) ) ),
    inference(resolution,[status(thm)],[c_40,c_285])).

tff(c_293,plain,(
    ! [A_362,D_365] :
      ( k3_tmap_1(A_362,'#skF_2','#skF_1',D_365,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_365))
      | ~ m1_pre_topc(D_365,'#skF_1')
      | ~ m1_pre_topc(D_365,A_362)
      | ~ m1_pre_topc('#skF_1',A_362)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_362)
      | ~ v2_pre_topc(A_362)
      | v2_struct_0(A_362) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_44,c_42,c_289])).

tff(c_314,plain,(
    ! [A_374,D_375] :
      ( k3_tmap_1(A_374,'#skF_2','#skF_1',D_375,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_375))
      | ~ m1_pre_topc(D_375,'#skF_1')
      | ~ m1_pre_topc(D_375,A_374)
      | ~ m1_pre_topc('#skF_1',A_374)
      | ~ l1_pre_topc(A_374)
      | ~ v2_pre_topc(A_374)
      | v2_struct_0(A_374) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_293])).

tff(c_324,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_314])).

tff(c_340,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_46,c_324])).

tff(c_341,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_340])).

tff(c_347,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_341])).

tff(c_350,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_347])).

tff(c_354,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_350])).

tff(c_356,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_341])).

tff(c_355,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_341])).

tff(c_248,plain,(
    ! [A_345,B_346,C_347,D_348] :
      ( k2_partfun1(u1_struct_0(A_345),u1_struct_0(B_346),C_347,u1_struct_0(D_348)) = k2_tmap_1(A_345,B_346,C_347,D_348)
      | ~ m1_pre_topc(D_348,A_345)
      | ~ m1_subset_1(C_347,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_345),u1_struct_0(B_346))))
      | ~ v1_funct_2(C_347,u1_struct_0(A_345),u1_struct_0(B_346))
      | ~ v1_funct_1(C_347)
      | ~ l1_pre_topc(B_346)
      | ~ v2_pre_topc(B_346)
      | v2_struct_0(B_346)
      | ~ l1_pre_topc(A_345)
      | ~ v2_pre_topc(A_345)
      | v2_struct_0(A_345) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_250,plain,(
    ! [D_348] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_348)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_348)
      | ~ m1_pre_topc(D_348,'#skF_1')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_248])).

tff(c_253,plain,(
    ! [D_348] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_348)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_348)
      | ~ m1_pre_topc(D_348,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_44,c_42,c_250])).

tff(c_254,plain,(
    ! [D_348] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_348)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_348)
      | ~ m1_pre_topc(D_348,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_253])).

tff(c_398,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_355,c_254])).

tff(c_405,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_398])).

tff(c_240,plain,(
    ! [C_342,E_339,B_338,D_341,A_340] :
      ( v1_funct_1(k3_tmap_1(A_340,B_338,C_342,D_341,E_339))
      | ~ m1_subset_1(E_339,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_342),u1_struct_0(B_338))))
      | ~ v1_funct_2(E_339,u1_struct_0(C_342),u1_struct_0(B_338))
      | ~ v1_funct_1(E_339)
      | ~ m1_pre_topc(D_341,A_340)
      | ~ m1_pre_topc(C_342,A_340)
      | ~ l1_pre_topc(B_338)
      | ~ v2_pre_topc(B_338)
      | v2_struct_0(B_338)
      | ~ l1_pre_topc(A_340)
      | ~ v2_pre_topc(A_340)
      | v2_struct_0(A_340) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_242,plain,(
    ! [A_340,D_341] :
      ( v1_funct_1(k3_tmap_1(A_340,'#skF_2','#skF_1',D_341,'#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_341,A_340)
      | ~ m1_pre_topc('#skF_1',A_340)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_340)
      | ~ v2_pre_topc(A_340)
      | v2_struct_0(A_340) ) ),
    inference(resolution,[status(thm)],[c_40,c_240])).

tff(c_245,plain,(
    ! [A_340,D_341] :
      ( v1_funct_1(k3_tmap_1(A_340,'#skF_2','#skF_1',D_341,'#skF_5'))
      | ~ m1_pre_topc(D_341,A_340)
      | ~ m1_pre_topc('#skF_1',A_340)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_340)
      | ~ v2_pre_topc(A_340)
      | v2_struct_0(A_340) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_44,c_42,c_242])).

tff(c_246,plain,(
    ! [A_340,D_341] :
      ( v1_funct_1(k3_tmap_1(A_340,'#skF_2','#skF_1',D_341,'#skF_5'))
      | ~ m1_pre_topc(D_341,A_340)
      | ~ m1_pre_topc('#skF_1',A_340)
      | ~ l1_pre_topc(A_340)
      | ~ v2_pre_topc(A_340)
      | v2_struct_0(A_340) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_245])).

tff(c_419,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_405,c_246])).

tff(c_429,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_356,c_46,c_419])).

tff(c_430,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_429])).

tff(c_264,plain,(
    ! [B_350,C_354,A_352,E_351,D_353] :
      ( v1_funct_2(k3_tmap_1(A_352,B_350,C_354,D_353,E_351),u1_struct_0(D_353),u1_struct_0(B_350))
      | ~ m1_subset_1(E_351,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_354),u1_struct_0(B_350))))
      | ~ v1_funct_2(E_351,u1_struct_0(C_354),u1_struct_0(B_350))
      | ~ v1_funct_1(E_351)
      | ~ m1_pre_topc(D_353,A_352)
      | ~ m1_pre_topc(C_354,A_352)
      | ~ l1_pre_topc(B_350)
      | ~ v2_pre_topc(B_350)
      | v2_struct_0(B_350)
      | ~ l1_pre_topc(A_352)
      | ~ v2_pre_topc(A_352)
      | v2_struct_0(A_352) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_266,plain,(
    ! [A_352,D_353] :
      ( v1_funct_2(k3_tmap_1(A_352,'#skF_2','#skF_1',D_353,'#skF_5'),u1_struct_0(D_353),u1_struct_0('#skF_2'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_353,A_352)
      | ~ m1_pre_topc('#skF_1',A_352)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_352)
      | ~ v2_pre_topc(A_352)
      | v2_struct_0(A_352) ) ),
    inference(resolution,[status(thm)],[c_40,c_264])).

tff(c_269,plain,(
    ! [A_352,D_353] :
      ( v1_funct_2(k3_tmap_1(A_352,'#skF_2','#skF_1',D_353,'#skF_5'),u1_struct_0(D_353),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_353,A_352)
      | ~ m1_pre_topc('#skF_1',A_352)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_352)
      | ~ v2_pre_topc(A_352)
      | v2_struct_0(A_352) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_44,c_42,c_266])).

tff(c_270,plain,(
    ! [A_352,D_353] :
      ( v1_funct_2(k3_tmap_1(A_352,'#skF_2','#skF_1',D_353,'#skF_5'),u1_struct_0(D_353),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_353,A_352)
      | ~ m1_pre_topc('#skF_1',A_352)
      | ~ l1_pre_topc(A_352)
      | ~ v2_pre_topc(A_352)
      | v2_struct_0(A_352) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_269])).

tff(c_416,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_405,c_270])).

tff(c_426,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_356,c_46,c_416])).

tff(c_427,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_426])).

tff(c_14,plain,(
    ! [A_57,E_61,B_58,D_60,C_59] :
      ( m1_subset_1(k3_tmap_1(A_57,B_58,C_59,D_60,E_61),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_60),u1_struct_0(B_58))))
      | ~ m1_subset_1(E_61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_59),u1_struct_0(B_58))))
      | ~ v1_funct_2(E_61,u1_struct_0(C_59),u1_struct_0(B_58))
      | ~ v1_funct_1(E_61)
      | ~ m1_pre_topc(D_60,A_57)
      | ~ m1_pre_topc(C_59,A_57)
      | ~ l1_pre_topc(B_58)
      | ~ v2_pre_topc(B_58)
      | v2_struct_0(B_58)
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_413,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_405,c_14])).

tff(c_423,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_356,c_46,c_44,c_42,c_40,c_413])).

tff(c_424,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_423])).

tff(c_10,plain,(
    ! [A_11,B_19,C_23,D_25] :
      ( k2_partfun1(u1_struct_0(A_11),u1_struct_0(B_19),C_23,u1_struct_0(D_25)) = k2_tmap_1(A_11,B_19,C_23,D_25)
      | ~ m1_pre_topc(D_25,A_11)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_11),u1_struct_0(B_19))))
      | ~ v1_funct_2(C_23,u1_struct_0(A_11),u1_struct_0(B_19))
      | ~ v1_funct_1(C_23)
      | ~ l1_pre_topc(B_19)
      | ~ v2_pre_topc(B_19)
      | v2_struct_0(B_19)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_440,plain,(
    ! [D_25] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_25)) = k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),D_25)
      | ~ m1_pre_topc(D_25,'#skF_4')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_424,c_10])).

tff(c_459,plain,(
    ! [D_25] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_25)) = k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),D_25)
      | ~ m1_pre_topc(D_25,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_89,c_56,c_54,c_430,c_427,c_440])).

tff(c_460,plain,(
    ! [D_25] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_25)) = k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),D_25)
      | ~ m1_pre_topc(D_25,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_58,c_459])).

tff(c_12,plain,(
    ! [A_26,C_50,B_42,D_54,E_56] :
      ( k3_tmap_1(A_26,B_42,C_50,D_54,E_56) = k2_partfun1(u1_struct_0(C_50),u1_struct_0(B_42),E_56,u1_struct_0(D_54))
      | ~ m1_pre_topc(D_54,C_50)
      | ~ m1_subset_1(E_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_50),u1_struct_0(B_42))))
      | ~ v1_funct_2(E_56,u1_struct_0(C_50),u1_struct_0(B_42))
      | ~ v1_funct_1(E_56)
      | ~ m1_pre_topc(D_54,A_26)
      | ~ m1_pre_topc(C_50,A_26)
      | ~ l1_pre_topc(B_42)
      | ~ v2_pre_topc(B_42)
      | v2_struct_0(B_42)
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_436,plain,(
    ! [A_26,D_54] :
      ( k3_tmap_1(A_26,'#skF_2','#skF_4',D_54,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_54))
      | ~ m1_pre_topc(D_54,'#skF_4')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ m1_pre_topc(D_54,A_26)
      | ~ m1_pre_topc('#skF_4',A_26)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(resolution,[status(thm)],[c_424,c_12])).

tff(c_451,plain,(
    ! [A_26,D_54] :
      ( k3_tmap_1(A_26,'#skF_2','#skF_4',D_54,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_54))
      | ~ m1_pre_topc(D_54,'#skF_4')
      | ~ m1_pre_topc(D_54,A_26)
      | ~ m1_pre_topc('#skF_4',A_26)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_430,c_427,c_436])).

tff(c_1361,plain,(
    ! [A_460,D_461] :
      ( k3_tmap_1(A_460,'#skF_2','#skF_4',D_461,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_461))
      | ~ m1_pre_topc(D_461,'#skF_4')
      | ~ m1_pre_topc(D_461,A_460)
      | ~ m1_pre_topc('#skF_4',A_460)
      | ~ l1_pre_topc(A_460)
      | ~ v2_pre_topc(A_460)
      | v2_struct_0(A_460) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_451])).

tff(c_1392,plain,(
    ! [D_461,A_460] :
      ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_461)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_461),u1_struct_0('#skF_2'))))
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ m1_pre_topc(D_461,A_460)
      | ~ m1_pre_topc('#skF_4',A_460)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_460)
      | ~ v2_pre_topc(A_460)
      | v2_struct_0(A_460)
      | ~ m1_pre_topc(D_461,'#skF_4')
      | ~ m1_pre_topc(D_461,A_460)
      | ~ m1_pre_topc('#skF_4',A_460)
      | ~ l1_pre_topc(A_460)
      | ~ v2_pre_topc(A_460)
      | v2_struct_0(A_460) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1361,c_14])).

tff(c_1419,plain,(
    ! [D_461,A_460] :
      ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_461)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_461),u1_struct_0('#skF_2'))))
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(D_461,'#skF_4')
      | ~ m1_pre_topc(D_461,A_460)
      | ~ m1_pre_topc('#skF_4',A_460)
      | ~ l1_pre_topc(A_460)
      | ~ v2_pre_topc(A_460)
      | v2_struct_0(A_460) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_430,c_427,c_424,c_1392])).

tff(c_1422,plain,(
    ! [D_462,A_463] :
      ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_462)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_462),u1_struct_0('#skF_2'))))
      | ~ m1_pre_topc(D_462,'#skF_4')
      | ~ m1_pre_topc(D_462,A_463)
      | ~ m1_pre_topc('#skF_4',A_463)
      | ~ l1_pre_topc(A_463)
      | ~ v2_pre_topc(A_463)
      | v2_struct_0(A_463) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1419])).

tff(c_1434,plain,
    ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_1422])).

tff(c_1454,plain,
    ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_46,c_1434])).

tff(c_1455,plain,
    ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1454])).

tff(c_1590,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1455])).

tff(c_1594,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_1590])).

tff(c_1598,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_1594])).

tff(c_1600,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_1455])).

tff(c_272,plain,(
    ! [B_357,C_361,A_359,E_358,D_360] :
      ( m1_subset_1(k3_tmap_1(A_359,B_357,C_361,D_360,E_358),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_360),u1_struct_0(B_357))))
      | ~ m1_subset_1(E_358,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_361),u1_struct_0(B_357))))
      | ~ v1_funct_2(E_358,u1_struct_0(C_361),u1_struct_0(B_357))
      | ~ v1_funct_1(E_358)
      | ~ m1_pre_topc(D_360,A_359)
      | ~ m1_pre_topc(C_361,A_359)
      | ~ l1_pre_topc(B_357)
      | ~ v2_pre_topc(B_357)
      | v2_struct_0(B_357)
      | ~ l1_pre_topc(A_359)
      | ~ v2_pre_topc(A_359)
      | v2_struct_0(A_359) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_18,plain,(
    ! [A_57,E_61,B_58,D_60,C_59] :
      ( v1_funct_1(k3_tmap_1(A_57,B_58,C_59,D_60,E_61))
      | ~ m1_subset_1(E_61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_59),u1_struct_0(B_58))))
      | ~ v1_funct_2(E_61,u1_struct_0(C_59),u1_struct_0(B_58))
      | ~ v1_funct_1(E_61)
      | ~ m1_pre_topc(D_60,A_57)
      | ~ m1_pre_topc(C_59,A_57)
      | ~ l1_pre_topc(B_58)
      | ~ v2_pre_topc(B_58)
      | v2_struct_0(B_58)
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_628,plain,(
    ! [C_391,A_390,D_388,D_393,B_389,A_392,E_387] :
      ( v1_funct_1(k3_tmap_1(A_392,B_389,D_388,D_393,k3_tmap_1(A_390,B_389,C_391,D_388,E_387)))
      | ~ v1_funct_2(k3_tmap_1(A_390,B_389,C_391,D_388,E_387),u1_struct_0(D_388),u1_struct_0(B_389))
      | ~ v1_funct_1(k3_tmap_1(A_390,B_389,C_391,D_388,E_387))
      | ~ m1_pre_topc(D_393,A_392)
      | ~ m1_pre_topc(D_388,A_392)
      | ~ l1_pre_topc(A_392)
      | ~ v2_pre_topc(A_392)
      | v2_struct_0(A_392)
      | ~ m1_subset_1(E_387,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_391),u1_struct_0(B_389))))
      | ~ v1_funct_2(E_387,u1_struct_0(C_391),u1_struct_0(B_389))
      | ~ v1_funct_1(E_387)
      | ~ m1_pre_topc(D_388,A_390)
      | ~ m1_pre_topc(C_391,A_390)
      | ~ l1_pre_topc(B_389)
      | ~ v2_pre_topc(B_389)
      | v2_struct_0(B_389)
      | ~ l1_pre_topc(A_390)
      | ~ v2_pre_topc(A_390)
      | v2_struct_0(A_390) ) ),
    inference(resolution,[status(thm)],[c_272,c_18])).

tff(c_632,plain,(
    ! [A_392,D_393] :
      ( v1_funct_1(k3_tmap_1(A_392,'#skF_2','#skF_4',D_393,k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5'))
      | ~ m1_pre_topc(D_393,A_392)
      | ~ m1_pre_topc('#skF_4',A_392)
      | ~ l1_pre_topc(A_392)
      | ~ v2_pre_topc(A_392)
      | v2_struct_0(A_392)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ m1_pre_topc('#skF_1','#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_405,c_628])).

tff(c_639,plain,(
    ! [A_392,D_393] :
      ( v1_funct_1(k3_tmap_1(A_392,'#skF_2','#skF_4',D_393,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_pre_topc(D_393,A_392)
      | ~ m1_pre_topc('#skF_4',A_392)
      | ~ l1_pre_topc(A_392)
      | ~ v2_pre_topc(A_392)
      | v2_struct_0(A_392)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_356,c_46,c_44,c_42,c_40,c_430,c_405,c_427,c_405,c_632])).

tff(c_640,plain,(
    ! [A_392,D_393] :
      ( v1_funct_1(k3_tmap_1(A_392,'#skF_2','#skF_4',D_393,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_pre_topc(D_393,A_392)
      | ~ m1_pre_topc('#skF_4',A_392)
      | ~ l1_pre_topc(A_392)
      | ~ v2_pre_topc(A_392)
      | v2_struct_0(A_392) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_639])).

tff(c_4514,plain,(
    ! [D_568,A_569] :
      ( v1_funct_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_568)))
      | ~ m1_pre_topc(D_568,A_569)
      | ~ m1_pre_topc('#skF_4',A_569)
      | ~ l1_pre_topc(A_569)
      | ~ v2_pre_topc(A_569)
      | v2_struct_0(A_569)
      | ~ m1_pre_topc(D_568,'#skF_4')
      | ~ m1_pre_topc(D_568,A_569)
      | ~ m1_pre_topc('#skF_4',A_569)
      | ~ l1_pre_topc(A_569)
      | ~ v2_pre_topc(A_569)
      | v2_struct_0(A_569) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1361,c_640])).

tff(c_4528,plain,
    ( v1_funct_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_4514])).

tff(c_4554,plain,
    ( v1_funct_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_89,c_1600,c_38,c_4528])).

tff(c_4555,plain,(
    v1_funct_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_4554])).

tff(c_4569,plain,
    ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_460,c_4555])).

tff(c_4573,plain,(
    v1_funct_1(k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4569])).

tff(c_16,plain,(
    ! [A_57,E_61,B_58,D_60,C_59] :
      ( v1_funct_2(k3_tmap_1(A_57,B_58,C_59,D_60,E_61),u1_struct_0(D_60),u1_struct_0(B_58))
      | ~ m1_subset_1(E_61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_59),u1_struct_0(B_58))))
      | ~ v1_funct_2(E_61,u1_struct_0(C_59),u1_struct_0(B_58))
      | ~ v1_funct_1(E_61)
      | ~ m1_pre_topc(D_60,A_57)
      | ~ m1_pre_topc(C_59,A_57)
      | ~ l1_pre_topc(B_58)
      | ~ v2_pre_topc(B_58)
      | v2_struct_0(B_58)
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_782,plain,(
    ! [D_396,B_397,A_400,D_401,A_398,E_395,C_399] :
      ( v1_funct_2(k3_tmap_1(A_400,B_397,D_396,D_401,k3_tmap_1(A_398,B_397,C_399,D_396,E_395)),u1_struct_0(D_401),u1_struct_0(B_397))
      | ~ v1_funct_2(k3_tmap_1(A_398,B_397,C_399,D_396,E_395),u1_struct_0(D_396),u1_struct_0(B_397))
      | ~ v1_funct_1(k3_tmap_1(A_398,B_397,C_399,D_396,E_395))
      | ~ m1_pre_topc(D_401,A_400)
      | ~ m1_pre_topc(D_396,A_400)
      | ~ l1_pre_topc(A_400)
      | ~ v2_pre_topc(A_400)
      | v2_struct_0(A_400)
      | ~ m1_subset_1(E_395,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_399),u1_struct_0(B_397))))
      | ~ v1_funct_2(E_395,u1_struct_0(C_399),u1_struct_0(B_397))
      | ~ v1_funct_1(E_395)
      | ~ m1_pre_topc(D_396,A_398)
      | ~ m1_pre_topc(C_399,A_398)
      | ~ l1_pre_topc(B_397)
      | ~ v2_pre_topc(B_397)
      | v2_struct_0(B_397)
      | ~ l1_pre_topc(A_398)
      | ~ v2_pre_topc(A_398)
      | v2_struct_0(A_398) ) ),
    inference(resolution,[status(thm)],[c_272,c_16])).

tff(c_793,plain,(
    ! [A_400,D_401] :
      ( v1_funct_2(k3_tmap_1(A_400,'#skF_2','#skF_4',D_401,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0(D_401),u1_struct_0('#skF_2'))
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5'))
      | ~ m1_pre_topc(D_401,A_400)
      | ~ m1_pre_topc('#skF_4',A_400)
      | ~ l1_pre_topc(A_400)
      | ~ v2_pre_topc(A_400)
      | v2_struct_0(A_400)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ m1_pre_topc('#skF_1','#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_405,c_782])).

tff(c_802,plain,(
    ! [A_400,D_401] :
      ( v1_funct_2(k3_tmap_1(A_400,'#skF_2','#skF_4',D_401,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0(D_401),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_401,A_400)
      | ~ m1_pre_topc('#skF_4',A_400)
      | ~ l1_pre_topc(A_400)
      | ~ v2_pre_topc(A_400)
      | v2_struct_0(A_400)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_356,c_46,c_44,c_42,c_40,c_430,c_405,c_427,c_405,c_793])).

tff(c_803,plain,(
    ! [A_400,D_401] :
      ( v1_funct_2(k3_tmap_1(A_400,'#skF_2','#skF_4',D_401,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0(D_401),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_401,A_400)
      | ~ m1_pre_topc('#skF_4',A_400)
      | ~ l1_pre_topc(A_400)
      | ~ v2_pre_topc(A_400)
      | v2_struct_0(A_400) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_802])).

tff(c_4981,plain,(
    ! [D_597,A_598] :
      ( v1_funct_2(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0(D_597)),u1_struct_0(D_597),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_597,A_598)
      | ~ m1_pre_topc('#skF_4',A_598)
      | ~ l1_pre_topc(A_598)
      | ~ v2_pre_topc(A_598)
      | v2_struct_0(A_598)
      | ~ m1_pre_topc(D_597,'#skF_4')
      | ~ m1_pre_topc(D_597,A_598)
      | ~ m1_pre_topc('#skF_4',A_598)
      | ~ l1_pre_topc(A_598)
      | ~ v2_pre_topc(A_598)
      | v2_struct_0(A_598) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1361,c_803])).

tff(c_4995,plain,
    ( v1_funct_2(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_4981])).

tff(c_5021,plain,
    ( v1_funct_2(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_89,c_1600,c_38,c_4995])).

tff(c_5022,plain,(
    v1_funct_2(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_5021])).

tff(c_5036,plain,
    ( v1_funct_2(k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_460,c_5022])).

tff(c_5040,plain,(
    v1_funct_2(k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_5036])).

tff(c_50,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_1436,plain,
    ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_1422])).

tff(c_1458,plain,
    ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_46,c_38,c_1436])).

tff(c_1459,plain,(
    m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1458])).

tff(c_1511,plain,
    ( m1_subset_1(k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_460,c_1459])).

tff(c_1544,plain,(
    m1_subset_1(k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1511])).

tff(c_326,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_314])).

tff(c_344,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_50,c_326])).

tff(c_345,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_344])).

tff(c_646,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_345])).

tff(c_650,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_646,c_254])).

tff(c_657,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_650])).

tff(c_679,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_657,c_246])).

tff(c_698,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_356,c_50,c_679])).

tff(c_699,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_698])).

tff(c_676,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_657,c_270])).

tff(c_695,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_356,c_50,c_676])).

tff(c_696,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_695])).

tff(c_673,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_657,c_14])).

tff(c_692,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_356,c_50,c_44,c_42,c_40,c_673])).

tff(c_693,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_692])).

tff(c_1016,plain,(
    ! [D_427,E_424,A_426,C_428,A_422,D_425,B_423] :
      ( k3_tmap_1(A_422,B_423,D_427,D_425,k3_tmap_1(A_426,B_423,C_428,D_427,E_424)) = k2_partfun1(u1_struct_0(D_427),u1_struct_0(B_423),k3_tmap_1(A_426,B_423,C_428,D_427,E_424),u1_struct_0(D_425))
      | ~ m1_pre_topc(D_425,D_427)
      | ~ v1_funct_2(k3_tmap_1(A_426,B_423,C_428,D_427,E_424),u1_struct_0(D_427),u1_struct_0(B_423))
      | ~ v1_funct_1(k3_tmap_1(A_426,B_423,C_428,D_427,E_424))
      | ~ m1_pre_topc(D_425,A_422)
      | ~ m1_pre_topc(D_427,A_422)
      | ~ l1_pre_topc(A_422)
      | ~ v2_pre_topc(A_422)
      | v2_struct_0(A_422)
      | ~ m1_subset_1(E_424,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_428),u1_struct_0(B_423))))
      | ~ v1_funct_2(E_424,u1_struct_0(C_428),u1_struct_0(B_423))
      | ~ v1_funct_1(E_424)
      | ~ m1_pre_topc(D_427,A_426)
      | ~ m1_pre_topc(C_428,A_426)
      | ~ l1_pre_topc(B_423)
      | ~ v2_pre_topc(B_423)
      | v2_struct_0(B_423)
      | ~ l1_pre_topc(A_426)
      | ~ v2_pre_topc(A_426)
      | v2_struct_0(A_426) ) ),
    inference(resolution,[status(thm)],[c_14,c_285])).

tff(c_1026,plain,(
    ! [A_422,D_427,D_425,A_426] :
      ( k3_tmap_1(A_422,'#skF_2',D_427,D_425,k3_tmap_1(A_426,'#skF_2','#skF_1',D_427,'#skF_5')) = k2_partfun1(u1_struct_0(D_427),u1_struct_0('#skF_2'),k3_tmap_1(A_426,'#skF_2','#skF_1',D_427,'#skF_5'),u1_struct_0(D_425))
      | ~ m1_pre_topc(D_425,D_427)
      | ~ v1_funct_2(k3_tmap_1(A_426,'#skF_2','#skF_1',D_427,'#skF_5'),u1_struct_0(D_427),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_426,'#skF_2','#skF_1',D_427,'#skF_5'))
      | ~ m1_pre_topc(D_425,A_422)
      | ~ m1_pre_topc(D_427,A_422)
      | ~ l1_pre_topc(A_422)
      | ~ v2_pre_topc(A_422)
      | v2_struct_0(A_422)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_427,A_426)
      | ~ m1_pre_topc('#skF_1',A_426)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_426)
      | ~ v2_pre_topc(A_426)
      | v2_struct_0(A_426) ) ),
    inference(resolution,[status(thm)],[c_40,c_1016])).

tff(c_1042,plain,(
    ! [A_422,D_427,D_425,A_426] :
      ( k3_tmap_1(A_422,'#skF_2',D_427,D_425,k3_tmap_1(A_426,'#skF_2','#skF_1',D_427,'#skF_5')) = k2_partfun1(u1_struct_0(D_427),u1_struct_0('#skF_2'),k3_tmap_1(A_426,'#skF_2','#skF_1',D_427,'#skF_5'),u1_struct_0(D_425))
      | ~ m1_pre_topc(D_425,D_427)
      | ~ v1_funct_2(k3_tmap_1(A_426,'#skF_2','#skF_1',D_427,'#skF_5'),u1_struct_0(D_427),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_426,'#skF_2','#skF_1',D_427,'#skF_5'))
      | ~ m1_pre_topc(D_425,A_422)
      | ~ m1_pre_topc(D_427,A_422)
      | ~ l1_pre_topc(A_422)
      | ~ v2_pre_topc(A_422)
      | v2_struct_0(A_422)
      | ~ m1_pre_topc(D_427,A_426)
      | ~ m1_pre_topc('#skF_1',A_426)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_426)
      | ~ v2_pre_topc(A_426)
      | v2_struct_0(A_426) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_44,c_42,c_1026])).

tff(c_2068,plain,(
    ! [A_479,D_480,D_481,A_482] :
      ( k3_tmap_1(A_479,'#skF_2',D_480,D_481,k3_tmap_1(A_482,'#skF_2','#skF_1',D_480,'#skF_5')) = k2_partfun1(u1_struct_0(D_480),u1_struct_0('#skF_2'),k3_tmap_1(A_482,'#skF_2','#skF_1',D_480,'#skF_5'),u1_struct_0(D_481))
      | ~ m1_pre_topc(D_481,D_480)
      | ~ v1_funct_2(k3_tmap_1(A_482,'#skF_2','#skF_1',D_480,'#skF_5'),u1_struct_0(D_480),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_482,'#skF_2','#skF_1',D_480,'#skF_5'))
      | ~ m1_pre_topc(D_481,A_479)
      | ~ m1_pre_topc(D_480,A_479)
      | ~ l1_pre_topc(A_479)
      | ~ v2_pre_topc(A_479)
      | v2_struct_0(A_479)
      | ~ m1_pre_topc(D_480,A_482)
      | ~ m1_pre_topc('#skF_1',A_482)
      | ~ l1_pre_topc(A_482)
      | ~ v2_pre_topc(A_482)
      | v2_struct_0(A_482) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1042])).

tff(c_844,plain,(
    ! [C_416,B_414,D_413,A_415,D_417,E_412] :
      ( k2_partfun1(u1_struct_0(D_413),u1_struct_0(B_414),k3_tmap_1(A_415,B_414,C_416,D_413,E_412),u1_struct_0(D_417)) = k2_tmap_1(D_413,B_414,k3_tmap_1(A_415,B_414,C_416,D_413,E_412),D_417)
      | ~ m1_pre_topc(D_417,D_413)
      | ~ v1_funct_2(k3_tmap_1(A_415,B_414,C_416,D_413,E_412),u1_struct_0(D_413),u1_struct_0(B_414))
      | ~ v1_funct_1(k3_tmap_1(A_415,B_414,C_416,D_413,E_412))
      | ~ l1_pre_topc(D_413)
      | ~ v2_pre_topc(D_413)
      | v2_struct_0(D_413)
      | ~ m1_subset_1(E_412,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_416),u1_struct_0(B_414))))
      | ~ v1_funct_2(E_412,u1_struct_0(C_416),u1_struct_0(B_414))
      | ~ v1_funct_1(E_412)
      | ~ m1_pre_topc(D_413,A_415)
      | ~ m1_pre_topc(C_416,A_415)
      | ~ l1_pre_topc(B_414)
      | ~ v2_pre_topc(B_414)
      | v2_struct_0(B_414)
      | ~ l1_pre_topc(A_415)
      | ~ v2_pre_topc(A_415)
      | v2_struct_0(A_415) ) ),
    inference(resolution,[status(thm)],[c_272,c_10])).

tff(c_854,plain,(
    ! [D_413,A_415,D_417] :
      ( k2_partfun1(u1_struct_0(D_413),u1_struct_0('#skF_2'),k3_tmap_1(A_415,'#skF_2','#skF_1',D_413,'#skF_5'),u1_struct_0(D_417)) = k2_tmap_1(D_413,'#skF_2',k3_tmap_1(A_415,'#skF_2','#skF_1',D_413,'#skF_5'),D_417)
      | ~ m1_pre_topc(D_417,D_413)
      | ~ v1_funct_2(k3_tmap_1(A_415,'#skF_2','#skF_1',D_413,'#skF_5'),u1_struct_0(D_413),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_415,'#skF_2','#skF_1',D_413,'#skF_5'))
      | ~ l1_pre_topc(D_413)
      | ~ v2_pre_topc(D_413)
      | v2_struct_0(D_413)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_413,A_415)
      | ~ m1_pre_topc('#skF_1',A_415)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_415)
      | ~ v2_pre_topc(A_415)
      | v2_struct_0(A_415) ) ),
    inference(resolution,[status(thm)],[c_40,c_844])).

tff(c_870,plain,(
    ! [D_413,A_415,D_417] :
      ( k2_partfun1(u1_struct_0(D_413),u1_struct_0('#skF_2'),k3_tmap_1(A_415,'#skF_2','#skF_1',D_413,'#skF_5'),u1_struct_0(D_417)) = k2_tmap_1(D_413,'#skF_2',k3_tmap_1(A_415,'#skF_2','#skF_1',D_413,'#skF_5'),D_417)
      | ~ m1_pre_topc(D_417,D_413)
      | ~ v1_funct_2(k3_tmap_1(A_415,'#skF_2','#skF_1',D_413,'#skF_5'),u1_struct_0(D_413),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_415,'#skF_2','#skF_1',D_413,'#skF_5'))
      | ~ l1_pre_topc(D_413)
      | ~ v2_pre_topc(D_413)
      | v2_struct_0(D_413)
      | ~ m1_pre_topc(D_413,A_415)
      | ~ m1_pre_topc('#skF_1',A_415)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_415)
      | ~ v2_pre_topc(A_415)
      | v2_struct_0(A_415) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_44,c_42,c_854])).

tff(c_871,plain,(
    ! [D_413,A_415,D_417] :
      ( k2_partfun1(u1_struct_0(D_413),u1_struct_0('#skF_2'),k3_tmap_1(A_415,'#skF_2','#skF_1',D_413,'#skF_5'),u1_struct_0(D_417)) = k2_tmap_1(D_413,'#skF_2',k3_tmap_1(A_415,'#skF_2','#skF_1',D_413,'#skF_5'),D_417)
      | ~ m1_pre_topc(D_417,D_413)
      | ~ v1_funct_2(k3_tmap_1(A_415,'#skF_2','#skF_1',D_413,'#skF_5'),u1_struct_0(D_413),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_415,'#skF_2','#skF_1',D_413,'#skF_5'))
      | ~ l1_pre_topc(D_413)
      | ~ v2_pre_topc(D_413)
      | v2_struct_0(D_413)
      | ~ m1_pre_topc(D_413,A_415)
      | ~ m1_pre_topc('#skF_1',A_415)
      | ~ l1_pre_topc(A_415)
      | ~ v2_pre_topc(A_415)
      | v2_struct_0(A_415) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_870])).

tff(c_6785,plain,(
    ! [A_695,D_696,D_697,A_698] :
      ( k3_tmap_1(A_695,'#skF_2',D_696,D_697,k3_tmap_1(A_698,'#skF_2','#skF_1',D_696,'#skF_5')) = k2_tmap_1(D_696,'#skF_2',k3_tmap_1(A_698,'#skF_2','#skF_1',D_696,'#skF_5'),D_697)
      | ~ m1_pre_topc(D_697,D_696)
      | ~ v1_funct_2(k3_tmap_1(A_698,'#skF_2','#skF_1',D_696,'#skF_5'),u1_struct_0(D_696),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_698,'#skF_2','#skF_1',D_696,'#skF_5'))
      | ~ l1_pre_topc(D_696)
      | ~ v2_pre_topc(D_696)
      | v2_struct_0(D_696)
      | ~ m1_pre_topc(D_696,A_698)
      | ~ m1_pre_topc('#skF_1',A_698)
      | ~ l1_pre_topc(A_698)
      | ~ v2_pre_topc(A_698)
      | v2_struct_0(A_698)
      | ~ m1_pre_topc(D_697,D_696)
      | ~ v1_funct_2(k3_tmap_1(A_698,'#skF_2','#skF_1',D_696,'#skF_5'),u1_struct_0(D_696),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_698,'#skF_2','#skF_1',D_696,'#skF_5'))
      | ~ m1_pre_topc(D_697,A_695)
      | ~ m1_pre_topc(D_696,A_695)
      | ~ l1_pre_topc(A_695)
      | ~ v2_pre_topc(A_695)
      | v2_struct_0(A_695)
      | ~ m1_pre_topc(D_696,A_698)
      | ~ m1_pre_topc('#skF_1',A_698)
      | ~ l1_pre_topc(A_698)
      | ~ v2_pre_topc(A_698)
      | v2_struct_0(A_698) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2068,c_871])).

tff(c_6793,plain,(
    ! [A_695,D_697] :
      ( k3_tmap_1(A_695,'#skF_2','#skF_4',D_697,k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')) = k2_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5'),D_697)
      | ~ m1_pre_topc(D_697,'#skF_4')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ m1_pre_topc('#skF_1','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ m1_pre_topc(D_697,'#skF_4')
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5'))
      | ~ m1_pre_topc(D_697,A_695)
      | ~ m1_pre_topc('#skF_4',A_695)
      | ~ l1_pre_topc(A_695)
      | ~ v2_pre_topc(A_695)
      | v2_struct_0(A_695)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ m1_pre_topc('#skF_1','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_405,c_6785])).

tff(c_6803,plain,(
    ! [A_695,D_697] :
      ( k3_tmap_1(A_695,'#skF_2','#skF_4',D_697,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),D_697)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(D_697,'#skF_4')
      | ~ m1_pre_topc(D_697,A_695)
      | ~ m1_pre_topc('#skF_4',A_695)
      | ~ l1_pre_topc(A_695)
      | ~ v2_pre_topc(A_695)
      | v2_struct_0(A_695)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_356,c_46,c_430,c_405,c_427,c_405,c_62,c_60,c_356,c_46,c_114,c_89,c_430,c_405,c_427,c_405,c_405,c_6793])).

tff(c_6804,plain,(
    ! [A_695,D_697] :
      ( k3_tmap_1(A_695,'#skF_2','#skF_4',D_697,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),D_697)
      | ~ m1_pre_topc(D_697,'#skF_4')
      | ~ m1_pre_topc(D_697,A_695)
      | ~ m1_pre_topc('#skF_4',A_695)
      | ~ l1_pre_topc(A_695)
      | ~ v2_pre_topc(A_695)
      | v2_struct_0(A_695) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_48,c_6803])).

tff(c_294,plain,(
    ! [A_362,D_365] :
      ( k3_tmap_1(A_362,'#skF_2','#skF_1',D_365,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_365))
      | ~ m1_pre_topc(D_365,'#skF_1')
      | ~ m1_pre_topc(D_365,A_362)
      | ~ m1_pre_topc('#skF_1',A_362)
      | ~ l1_pre_topc(A_362)
      | ~ v2_pre_topc(A_362)
      | v2_struct_0(A_362) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_293])).

tff(c_358,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_1')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_356,c_294])).

tff(c_376,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_1')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_356,c_358])).

tff(c_377,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_1')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_376])).

tff(c_487,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_254])).

tff(c_494,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_487])).

tff(c_508,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'))
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_246])).

tff(c_518,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_356,c_356,c_508])).

tff(c_519,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_518])).

tff(c_505,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_270])).

tff(c_515,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_356,c_356,c_505])).

tff(c_516,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_515])).

tff(c_2126,plain,(
    ! [A_479,D_481] :
      ( k3_tmap_1(A_479,'#skF_2','#skF_1',D_481,k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_5')) = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0(D_481))
      | ~ m1_pre_topc(D_481,'#skF_1')
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_5'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_5'))
      | ~ m1_pre_topc(D_481,A_479)
      | ~ m1_pre_topc('#skF_1',A_479)
      | ~ l1_pre_topc(A_479)
      | ~ v2_pre_topc(A_479)
      | v2_struct_0(A_479)
      | ~ m1_pre_topc('#skF_1','#skF_1')
      | ~ m1_pre_topc('#skF_1','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_2068])).

tff(c_2166,plain,(
    ! [A_479,D_481] :
      ( k3_tmap_1(A_479,'#skF_2','#skF_1',D_481,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1')) = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0(D_481))
      | ~ m1_pre_topc(D_481,'#skF_1')
      | ~ m1_pre_topc(D_481,A_479)
      | ~ m1_pre_topc('#skF_1',A_479)
      | ~ l1_pre_topc(A_479)
      | ~ v2_pre_topc(A_479)
      | v2_struct_0(A_479)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_356,c_356,c_519,c_494,c_516,c_494,c_494,c_2126])).

tff(c_2504,plain,(
    ! [A_494,D_495] :
      ( k3_tmap_1(A_494,'#skF_2','#skF_1',D_495,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1')) = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0(D_495))
      | ~ m1_pre_topc(D_495,'#skF_1')
      | ~ m1_pre_topc(D_495,A_494)
      | ~ m1_pre_topc('#skF_1',A_494)
      | ~ l1_pre_topc(A_494)
      | ~ v2_pre_topc(A_494)
      | v2_struct_0(A_494) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2166])).

tff(c_630,plain,(
    ! [A_392,D_393] :
      ( v1_funct_1(k3_tmap_1(A_392,'#skF_2','#skF_1',D_393,k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_5')))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_5'))
      | ~ m1_pre_topc(D_393,A_392)
      | ~ m1_pre_topc('#skF_1',A_392)
      | ~ l1_pre_topc(A_392)
      | ~ v2_pre_topc(A_392)
      | v2_struct_0(A_392)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_1','#skF_1')
      | ~ m1_pre_topc('#skF_1','#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_628])).

tff(c_636,plain,(
    ! [A_392,D_393] :
      ( v1_funct_1(k3_tmap_1(A_392,'#skF_2','#skF_1',D_393,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1')))
      | ~ m1_pre_topc(D_393,A_392)
      | ~ m1_pre_topc('#skF_1',A_392)
      | ~ l1_pre_topc(A_392)
      | ~ v2_pre_topc(A_392)
      | v2_struct_0(A_392)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_356,c_356,c_44,c_42,c_40,c_519,c_494,c_516,c_494,c_630])).

tff(c_637,plain,(
    ! [A_392,D_393] :
      ( v1_funct_1(k3_tmap_1(A_392,'#skF_2','#skF_1',D_393,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1')))
      | ~ m1_pre_topc(D_393,A_392)
      | ~ m1_pre_topc('#skF_1',A_392)
      | ~ l1_pre_topc(A_392)
      | ~ v2_pre_topc(A_392)
      | v2_struct_0(A_392) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_636])).

tff(c_4306,plain,(
    ! [D_554,A_555] :
      ( v1_funct_1(k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0(D_554)))
      | ~ m1_pre_topc(D_554,A_555)
      | ~ m1_pre_topc('#skF_1',A_555)
      | ~ l1_pre_topc(A_555)
      | ~ v2_pre_topc(A_555)
      | v2_struct_0(A_555)
      | ~ m1_pre_topc(D_554,'#skF_1')
      | ~ m1_pre_topc(D_554,A_555)
      | ~ m1_pre_topc('#skF_1',A_555)
      | ~ l1_pre_topc(A_555)
      | ~ v2_pre_topc(A_555)
      | v2_struct_0(A_555) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2504,c_637])).

tff(c_4322,plain,
    ( v1_funct_1(k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_4')))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_4306])).

tff(c_4350,plain,
    ( v1_funct_1(k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_356,c_46,c_4322])).

tff(c_4351,plain,(
    v1_funct_1(k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_4350])).

tff(c_790,plain,(
    ! [A_400,D_401] :
      ( v1_funct_2(k3_tmap_1(A_400,'#skF_2','#skF_1',D_401,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1')),u1_struct_0(D_401),u1_struct_0('#skF_2'))
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_5'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_5'))
      | ~ m1_pre_topc(D_401,A_400)
      | ~ m1_pre_topc('#skF_1',A_400)
      | ~ l1_pre_topc(A_400)
      | ~ v2_pre_topc(A_400)
      | v2_struct_0(A_400)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_1','#skF_1')
      | ~ m1_pre_topc('#skF_1','#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_782])).

tff(c_799,plain,(
    ! [A_400,D_401] :
      ( v1_funct_2(k3_tmap_1(A_400,'#skF_2','#skF_1',D_401,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1')),u1_struct_0(D_401),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_401,A_400)
      | ~ m1_pre_topc('#skF_1',A_400)
      | ~ l1_pre_topc(A_400)
      | ~ v2_pre_topc(A_400)
      | v2_struct_0(A_400)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_356,c_356,c_44,c_42,c_40,c_519,c_494,c_516,c_494,c_790])).

tff(c_800,plain,(
    ! [A_400,D_401] :
      ( v1_funct_2(k3_tmap_1(A_400,'#skF_2','#skF_1',D_401,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1')),u1_struct_0(D_401),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_401,A_400)
      | ~ m1_pre_topc('#skF_1',A_400)
      | ~ l1_pre_topc(A_400)
      | ~ v2_pre_topc(A_400)
      | v2_struct_0(A_400) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_799])).

tff(c_5241,plain,(
    ! [D_618,A_619] :
      ( v1_funct_2(k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0(D_618)),u1_struct_0(D_618),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_618,A_619)
      | ~ m1_pre_topc('#skF_1',A_619)
      | ~ l1_pre_topc(A_619)
      | ~ v2_pre_topc(A_619)
      | v2_struct_0(A_619)
      | ~ m1_pre_topc(D_618,'#skF_1')
      | ~ m1_pre_topc(D_618,A_619)
      | ~ m1_pre_topc('#skF_1',A_619)
      | ~ l1_pre_topc(A_619)
      | ~ v2_pre_topc(A_619)
      | v2_struct_0(A_619) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2504,c_800])).

tff(c_5257,plain,
    ( v1_funct_2(k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_4')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_5241])).

tff(c_5285,plain,
    ( v1_funct_2(k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_4')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_356,c_46,c_5257])).

tff(c_5286,plain,(
    v1_funct_2(k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_4')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_5285])).

tff(c_502,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_14])).

tff(c_512,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_356,c_356,c_44,c_42,c_40,c_502])).

tff(c_513,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_512])).

tff(c_2537,plain,(
    ! [D_495,A_494] :
      ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0(D_495)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_495),u1_struct_0('#skF_2'))))
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'))
      | ~ m1_pre_topc(D_495,A_494)
      | ~ m1_pre_topc('#skF_1',A_494)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_494)
      | ~ v2_pre_topc(A_494)
      | v2_struct_0(A_494)
      | ~ m1_pre_topc(D_495,'#skF_1')
      | ~ m1_pre_topc(D_495,A_494)
      | ~ m1_pre_topc('#skF_1',A_494)
      | ~ l1_pre_topc(A_494)
      | ~ v2_pre_topc(A_494)
      | v2_struct_0(A_494) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2504,c_14])).

tff(c_2567,plain,(
    ! [D_495,A_494] :
      ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0(D_495)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_495),u1_struct_0('#skF_2'))))
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(D_495,'#skF_1')
      | ~ m1_pre_topc(D_495,A_494)
      | ~ m1_pre_topc('#skF_1',A_494)
      | ~ l1_pre_topc(A_494)
      | ~ v2_pre_topc(A_494)
      | v2_struct_0(A_494) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_519,c_516,c_513,c_2537])).

tff(c_2616,plain,(
    ! [D_497,A_498] :
      ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0(D_497)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_497),u1_struct_0('#skF_2'))))
      | ~ m1_pre_topc(D_497,'#skF_1')
      | ~ m1_pre_topc(D_497,A_498)
      | ~ m1_pre_topc('#skF_1',A_498)
      | ~ l1_pre_topc(A_498)
      | ~ v2_pre_topc(A_498)
      | v2_struct_0(A_498) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2567])).

tff(c_2632,plain,
    ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_2616])).

tff(c_2660,plain,
    ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_356,c_46,c_2632])).

tff(c_2661,plain,(
    m1_subset_1(k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2660])).

tff(c_2167,plain,(
    ! [A_479,D_481] :
      ( k3_tmap_1(A_479,'#skF_2','#skF_1',D_481,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1')) = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0(D_481))
      | ~ m1_pre_topc(D_481,'#skF_1')
      | ~ m1_pre_topc(D_481,A_479)
      | ~ m1_pre_topc('#skF_1',A_479)
      | ~ l1_pre_topc(A_479)
      | ~ v2_pre_topc(A_479)
      | v2_struct_0(A_479) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2166])).

tff(c_7753,plain,(
    ! [A_739,D_738,A_737] :
      ( k3_tmap_1(A_739,'#skF_2','#skF_1',D_738,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1')) = k3_tmap_1(A_737,'#skF_2','#skF_1',D_738,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'))
      | ~ m1_pre_topc(D_738,'#skF_1')
      | ~ m1_pre_topc(D_738,A_737)
      | ~ m1_pre_topc('#skF_1',A_737)
      | ~ l1_pre_topc(A_737)
      | ~ v2_pre_topc(A_737)
      | v2_struct_0(A_737)
      | ~ m1_pre_topc(D_738,'#skF_1')
      | ~ m1_pre_topc(D_738,A_739)
      | ~ m1_pre_topc('#skF_1',A_739)
      | ~ l1_pre_topc(A_739)
      | ~ v2_pre_topc(A_739)
      | v2_struct_0(A_739) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2167,c_2504])).

tff(c_2,plain,(
    ! [A_1,B_2,D_4] :
      ( r2_funct_2(A_1,B_2,D_4,D_4)
      | ~ m1_subset_1(D_4,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(D_4,A_1,B_2)
      | ~ v1_funct_1(D_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_562,plain,
    ( r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1')) ),
    inference(resolution,[status(thm)],[c_513,c_2])).

tff(c_585,plain,(
    r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_516,c_562])).

tff(c_24,plain,(
    ! [F_188,D_182,E_186,A_126,C_174,B_158] :
      ( r2_funct_2(u1_struct_0(D_182),u1_struct_0(B_158),k3_tmap_1(A_126,B_158,C_174,D_182,F_188),k2_tmap_1(A_126,B_158,E_186,D_182))
      | ~ m1_pre_topc(D_182,C_174)
      | ~ r2_funct_2(u1_struct_0(C_174),u1_struct_0(B_158),F_188,k2_tmap_1(A_126,B_158,E_186,C_174))
      | ~ m1_subset_1(F_188,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_174),u1_struct_0(B_158))))
      | ~ v1_funct_2(F_188,u1_struct_0(C_174),u1_struct_0(B_158))
      | ~ v1_funct_1(F_188)
      | ~ m1_subset_1(E_186,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_126),u1_struct_0(B_158))))
      | ~ v1_funct_2(E_186,u1_struct_0(A_126),u1_struct_0(B_158))
      | ~ v1_funct_1(E_186)
      | ~ m1_pre_topc(D_182,A_126)
      | v2_struct_0(D_182)
      | ~ m1_pre_topc(C_174,A_126)
      | v2_struct_0(C_174)
      | ~ l1_pre_topc(B_158)
      | ~ v2_pre_topc(B_158)
      | v2_struct_0(B_158)
      | ~ l1_pre_topc(A_126)
      | ~ v2_pre_topc(A_126)
      | v2_struct_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_617,plain,(
    ! [D_182] :
      ( r2_funct_2(u1_struct_0(D_182),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_1',D_182,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1')),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_182))
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_182,'#skF_1')
      | v2_struct_0(D_182)
      | ~ m1_pre_topc('#skF_1','#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_585,c_24])).

tff(c_622,plain,(
    ! [D_182] :
      ( r2_funct_2(u1_struct_0(D_182),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_1',D_182,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1')),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_182))
      | ~ m1_pre_topc(D_182,'#skF_1')
      | v2_struct_0(D_182)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_356,c_44,c_42,c_40,c_519,c_516,c_513,c_617])).

tff(c_623,plain,(
    ! [D_182] :
      ( r2_funct_2(u1_struct_0(D_182),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_1',D_182,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1')),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_182))
      | ~ m1_pre_topc(D_182,'#skF_1')
      | v2_struct_0(D_182) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_622])).

tff(c_7877,plain,(
    ! [D_738,A_739] :
      ( r2_funct_2(u1_struct_0(D_738),u1_struct_0('#skF_2'),k3_tmap_1(A_739,'#skF_2','#skF_1',D_738,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1')),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_738))
      | ~ m1_pre_topc(D_738,'#skF_1')
      | v2_struct_0(D_738)
      | ~ m1_pre_topc(D_738,'#skF_1')
      | ~ m1_pre_topc(D_738,'#skF_1')
      | ~ m1_pre_topc('#skF_1','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ m1_pre_topc(D_738,'#skF_1')
      | ~ m1_pre_topc(D_738,A_739)
      | ~ m1_pre_topc('#skF_1',A_739)
      | ~ l1_pre_topc(A_739)
      | ~ v2_pre_topc(A_739)
      | v2_struct_0(A_739) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7753,c_623])).

tff(c_8001,plain,(
    ! [D_738,A_739] :
      ( r2_funct_2(u1_struct_0(D_738),u1_struct_0('#skF_2'),k3_tmap_1(A_739,'#skF_2','#skF_1',D_738,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1')),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_738))
      | v2_struct_0(D_738)
      | v2_struct_0('#skF_1')
      | ~ m1_pre_topc(D_738,'#skF_1')
      | ~ m1_pre_topc(D_738,A_739)
      | ~ m1_pre_topc('#skF_1',A_739)
      | ~ l1_pre_topc(A_739)
      | ~ v2_pre_topc(A_739)
      | v2_struct_0(A_739) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_356,c_7877])).

tff(c_8036,plain,(
    ! [D_740,A_741] :
      ( r2_funct_2(u1_struct_0(D_740),u1_struct_0('#skF_2'),k3_tmap_1(A_741,'#skF_2','#skF_1',D_740,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1')),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_740))
      | v2_struct_0(D_740)
      | ~ m1_pre_topc(D_740,'#skF_1')
      | ~ m1_pre_topc(D_740,A_741)
      | ~ m1_pre_topc('#skF_1',A_741)
      | ~ l1_pre_topc(A_741)
      | ~ v2_pre_topc(A_741)
      | v2_struct_0(A_741) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_8001])).

tff(c_10865,plain,(
    ! [D_868,A_869] :
      ( r2_funct_2(u1_struct_0(D_868),u1_struct_0('#skF_2'),k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0(D_868)),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_868))
      | v2_struct_0(D_868)
      | ~ m1_pre_topc(D_868,'#skF_1')
      | ~ m1_pre_topc(D_868,A_869)
      | ~ m1_pre_topc('#skF_1',A_869)
      | ~ l1_pre_topc(A_869)
      | ~ v2_pre_topc(A_869)
      | v2_struct_0(A_869)
      | ~ m1_pre_topc(D_868,'#skF_1')
      | ~ m1_pre_topc(D_868,A_869)
      | ~ m1_pre_topc('#skF_1',A_869)
      | ~ l1_pre_topc(A_869)
      | ~ v2_pre_topc(A_869)
      | v2_struct_0(A_869) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2167,c_8036])).

tff(c_10881,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_4')),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_10865])).

tff(c_10911,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_4')),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_356,c_46,c_10881])).

tff(c_10912,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_4')),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_48,c_10911])).

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

tff(c_11279,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_4')) = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ m1_subset_1(k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_4')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_10912,c_4])).

tff(c_11295,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_4')) = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4351,c_5286,c_2661,c_430,c_427,c_424,c_11279])).

tff(c_333,plain,(
    ! [A_62] :
      ( k3_tmap_1(A_62,'#skF_2','#skF_1',A_62,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(A_62))
      | ~ m1_pre_topc(A_62,'#skF_1')
      | ~ m1_pre_topc('#skF_1',A_62)
      | ~ v2_pre_topc(A_62)
      | v2_struct_0(A_62)
      | ~ l1_pre_topc(A_62) ) ),
    inference(resolution,[status(thm)],[c_20,c_314])).

tff(c_1460,plain,(
    ! [D_464,A_465,D_466] :
      ( k2_partfun1(u1_struct_0(D_464),u1_struct_0('#skF_2'),k3_tmap_1(A_465,'#skF_2','#skF_1',D_464,'#skF_5'),u1_struct_0(D_466)) = k2_tmap_1(D_464,'#skF_2',k3_tmap_1(A_465,'#skF_2','#skF_1',D_464,'#skF_5'),D_466)
      | ~ m1_pre_topc(D_466,D_464)
      | ~ v1_funct_2(k3_tmap_1(A_465,'#skF_2','#skF_1',D_464,'#skF_5'),u1_struct_0(D_464),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_465,'#skF_2','#skF_1',D_464,'#skF_5'))
      | ~ l1_pre_topc(D_464)
      | ~ v2_pre_topc(D_464)
      | v2_struct_0(D_464)
      | ~ m1_pre_topc(D_464,A_465)
      | ~ m1_pre_topc('#skF_1',A_465)
      | ~ l1_pre_topc(A_465)
      | ~ v2_pre_topc(A_465)
      | v2_struct_0(A_465) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_870])).

tff(c_5229,plain,(
    ! [A_616,D_617] :
      ( k2_tmap_1(A_616,'#skF_2',k3_tmap_1(A_616,'#skF_2','#skF_1',A_616,'#skF_5'),D_617) = k2_partfun1(u1_struct_0(A_616),u1_struct_0('#skF_2'),k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(A_616)),u1_struct_0(D_617))
      | ~ m1_pre_topc(D_617,A_616)
      | ~ v1_funct_2(k3_tmap_1(A_616,'#skF_2','#skF_1',A_616,'#skF_5'),u1_struct_0(A_616),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_616,'#skF_2','#skF_1',A_616,'#skF_5'))
      | ~ l1_pre_topc(A_616)
      | ~ v2_pre_topc(A_616)
      | v2_struct_0(A_616)
      | ~ m1_pre_topc(A_616,A_616)
      | ~ m1_pre_topc('#skF_1',A_616)
      | ~ l1_pre_topc(A_616)
      | ~ v2_pre_topc(A_616)
      | v2_struct_0(A_616)
      | ~ m1_pre_topc(A_616,'#skF_1')
      | ~ m1_pre_topc('#skF_1',A_616)
      | ~ v2_pre_topc(A_616)
      | v2_struct_0(A_616)
      | ~ l1_pre_topc(A_616) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_1460])).

tff(c_6290,plain,(
    ! [D_681,D_682] :
      ( k2_tmap_1(D_681,'#skF_2',k3_tmap_1(D_681,'#skF_2','#skF_1',D_681,'#skF_5'),D_682) = k2_partfun1(u1_struct_0(D_681),u1_struct_0('#skF_2'),k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_681)),u1_struct_0(D_682))
      | ~ m1_pre_topc(D_682,D_681)
      | ~ v1_funct_1(k3_tmap_1(D_681,'#skF_2','#skF_1',D_681,'#skF_5'))
      | ~ m1_pre_topc(D_681,'#skF_1')
      | ~ m1_pre_topc(D_681,D_681)
      | ~ m1_pre_topc('#skF_1',D_681)
      | ~ l1_pre_topc(D_681)
      | ~ v2_pre_topc(D_681)
      | v2_struct_0(D_681) ) ),
    inference(resolution,[status(thm)],[c_270,c_5229])).

tff(c_6325,plain,(
    ! [D_348,D_682] :
      ( k2_tmap_1(D_348,'#skF_2',k3_tmap_1(D_348,'#skF_2','#skF_1',D_348,'#skF_5'),D_682) = k2_partfun1(u1_struct_0(D_348),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5',D_348),u1_struct_0(D_682))
      | ~ m1_pre_topc(D_682,D_348)
      | ~ v1_funct_1(k3_tmap_1(D_348,'#skF_2','#skF_1',D_348,'#skF_5'))
      | ~ m1_pre_topc(D_348,'#skF_1')
      | ~ m1_pre_topc(D_348,D_348)
      | ~ m1_pre_topc('#skF_1',D_348)
      | ~ l1_pre_topc(D_348)
      | ~ v2_pre_topc(D_348)
      | v2_struct_0(D_348)
      | ~ m1_pre_topc(D_348,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_6290])).

tff(c_11317,plain,
    ( k2_tmap_1('#skF_1','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_5'),'#skF_4') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_5'))
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_11295,c_6325])).

tff(c_11345,plain,
    ( k2_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),'#skF_4') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_62,c_60,c_356,c_356,c_356,c_519,c_494,c_46,c_494,c_11317])).

tff(c_11346,plain,(
    k2_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),'#skF_4') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_11345])).

tff(c_4324,plain,
    ( v1_funct_1(k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_4306])).

tff(c_4354,plain,
    ( v1_funct_1(k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_356,c_50,c_4324])).

tff(c_4355,plain,(
    v1_funct_1(k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_4354])).

tff(c_5259,plain,
    ( v1_funct_2(k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_5241])).

tff(c_5289,plain,
    ( v1_funct_2(k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_356,c_50,c_5259])).

tff(c_5290,plain,(
    v1_funct_2(k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_5289])).

tff(c_2634,plain,
    ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_2616])).

tff(c_2664,plain,
    ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_356,c_50,c_2634])).

tff(c_2665,plain,(
    m1_subset_1(k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2664])).

tff(c_10883,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_3')),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_10865])).

tff(c_10915,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_3')),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_356,c_50,c_10883])).

tff(c_10916,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_3')),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_52,c_10915])).

tff(c_11103,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_3')) = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | ~ m1_subset_1(k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_10916,c_4])).

tff(c_11119,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_3')) = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4355,c_5290,c_2665,c_699,c_696,c_693,c_11103])).

tff(c_11141,plain,
    ( k2_tmap_1('#skF_1','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_5'),'#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_1','#skF_5'))
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_11119,c_6325])).

tff(c_11169,plain,
    ( k2_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),'#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_62,c_60,c_356,c_356,c_356,c_519,c_494,c_50,c_494,c_11141])).

tff(c_11170,plain,(
    k2_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),'#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_11169])).

tff(c_558,plain,(
    ! [D_25] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0(D_25)) = k2_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),D_25)
      | ~ m1_pre_topc(D_25,'#skF_1')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_513,c_10])).

tff(c_577,plain,(
    ! [D_25] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0(D_25)) = k2_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),D_25)
      | ~ m1_pre_topc(D_25,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_519,c_516,c_558])).

tff(c_578,plain,(
    ! [D_25] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0(D_25)) = k2_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),D_25)
      | ~ m1_pre_topc(D_25,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_577])).

tff(c_4371,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),'#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_578,c_4351])).

tff(c_4375,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_4371])).

tff(c_5306,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_578,c_5286])).

tff(c_5310,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_5306])).

tff(c_2787,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_578,c_2661])).

tff(c_2820,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2787])).

tff(c_2928,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),'#skF_4'),k2_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),'#skF_4'))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_2820,c_2])).

tff(c_5781,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),'#skF_4'),k2_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4375,c_5310,c_2928])).

tff(c_5783,plain,(
    ! [D_182] :
      ( r2_funct_2(u1_struct_0(D_182),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4',D_182,k2_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),'#skF_4')),k2_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),D_182))
      | ~ m1_pre_topc(D_182,'#skF_4')
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),'#skF_4'))
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'))
      | ~ m1_pre_topc(D_182,'#skF_1')
      | v2_struct_0(D_182)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_5781,c_24])).

tff(c_5788,plain,(
    ! [D_182] :
      ( r2_funct_2(u1_struct_0(D_182),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4',D_182,k2_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),'#skF_4')),k2_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),D_182))
      | ~ m1_pre_topc(D_182,'#skF_4')
      | ~ m1_pre_topc(D_182,'#skF_1')
      | v2_struct_0(D_182)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_46,c_519,c_516,c_513,c_4375,c_5310,c_2820,c_5783])).

tff(c_5789,plain,(
    ! [D_182] :
      ( r2_funct_2(u1_struct_0(D_182),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4',D_182,k2_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),'#skF_4')),k2_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),D_182))
      | ~ m1_pre_topc(D_182,'#skF_4')
      | ~ m1_pre_topc(D_182,'#skF_1')
      | v2_struct_0(D_182) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_48,c_5788])).

tff(c_11208,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),'#skF_4')),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_11170,c_5789])).

tff(c_11229,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),'#skF_4')),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_38,c_11208])).

tff(c_11230,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_1'),'#skF_4')),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_11229])).

tff(c_11445,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11346,c_11230])).

tff(c_11458,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6804,c_11445])).

tff(c_11473,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_46,c_50,c_38,c_11458])).

tff(c_11474,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_11473])).

tff(c_11479,plain,
    ( k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_11474,c_4])).

tff(c_11486,plain,(
    k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_3') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4573,c_5040,c_1544,c_699,c_696,c_693,c_11479])).

tff(c_295,plain,(
    ! [C_371,A_370,B_369,F_368,D_367] :
      ( r1_tmap_1(D_367,A_370,k2_tmap_1(B_369,A_370,C_371,D_367),F_368)
      | ~ r1_tmap_1(B_369,A_370,C_371,F_368)
      | ~ m1_subset_1(F_368,u1_struct_0(D_367))
      | ~ m1_subset_1(F_368,u1_struct_0(B_369))
      | ~ m1_pre_topc(D_367,B_369)
      | v2_struct_0(D_367)
      | ~ m1_subset_1(C_371,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_369),u1_struct_0(A_370))))
      | ~ v1_funct_2(C_371,u1_struct_0(B_369),u1_struct_0(A_370))
      | ~ v1_funct_1(C_371)
      | ~ l1_pre_topc(B_369)
      | ~ v2_pre_topc(B_369)
      | v2_struct_0(B_369)
      | ~ l1_pre_topc(A_370)
      | ~ v2_pre_topc(A_370)
      | v2_struct_0(A_370) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_1194,plain,(
    ! [C_443,D_439,A_441,D_442,B_437,E_438,F_440] :
      ( r1_tmap_1(D_439,B_437,k2_tmap_1(D_442,B_437,k3_tmap_1(A_441,B_437,C_443,D_442,E_438),D_439),F_440)
      | ~ r1_tmap_1(D_442,B_437,k3_tmap_1(A_441,B_437,C_443,D_442,E_438),F_440)
      | ~ m1_subset_1(F_440,u1_struct_0(D_439))
      | ~ m1_subset_1(F_440,u1_struct_0(D_442))
      | ~ m1_pre_topc(D_439,D_442)
      | v2_struct_0(D_439)
      | ~ v1_funct_2(k3_tmap_1(A_441,B_437,C_443,D_442,E_438),u1_struct_0(D_442),u1_struct_0(B_437))
      | ~ v1_funct_1(k3_tmap_1(A_441,B_437,C_443,D_442,E_438))
      | ~ l1_pre_topc(D_442)
      | ~ v2_pre_topc(D_442)
      | v2_struct_0(D_442)
      | ~ m1_subset_1(E_438,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_443),u1_struct_0(B_437))))
      | ~ v1_funct_2(E_438,u1_struct_0(C_443),u1_struct_0(B_437))
      | ~ v1_funct_1(E_438)
      | ~ m1_pre_topc(D_442,A_441)
      | ~ m1_pre_topc(C_443,A_441)
      | ~ l1_pre_topc(B_437)
      | ~ v2_pre_topc(B_437)
      | v2_struct_0(B_437)
      | ~ l1_pre_topc(A_441)
      | ~ v2_pre_topc(A_441)
      | v2_struct_0(A_441) ) ),
    inference(resolution,[status(thm)],[c_14,c_295])).

tff(c_1210,plain,(
    ! [D_439,F_440] :
      ( r1_tmap_1(D_439,'#skF_2',k2_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5'),D_439),F_440)
      | ~ r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5'),F_440)
      | ~ m1_subset_1(F_440,u1_struct_0(D_439))
      | ~ m1_subset_1(F_440,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_439,'#skF_4')
      | v2_struct_0(D_439)
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ m1_pre_topc('#skF_1','#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_405,c_1194])).

tff(c_1236,plain,(
    ! [D_439,F_440] :
      ( r1_tmap_1(D_439,'#skF_2',k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),D_439),F_440)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),F_440)
      | ~ m1_subset_1(F_440,u1_struct_0(D_439))
      | ~ m1_subset_1(F_440,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_439,'#skF_4')
      | v2_struct_0(D_439)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_356,c_46,c_44,c_42,c_40,c_114,c_89,c_430,c_405,c_427,c_405,c_405,c_1210])).

tff(c_1237,plain,(
    ! [D_439,F_440] :
      ( r1_tmap_1(D_439,'#skF_2',k2_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),D_439),F_440)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),F_440)
      | ~ m1_subset_1(F_440,u1_struct_0(D_439))
      | ~ m1_subset_1(F_440,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_439,'#skF_4')
      | v2_struct_0(D_439) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_48,c_1236])).

tff(c_11517,plain,(
    ! [F_440] :
      ( r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),F_440)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),F_440)
      | ~ m1_subset_1(F_440,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_440,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11486,c_1237])).

tff(c_11538,plain,(
    ! [F_440] :
      ( r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),F_440)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),F_440)
      | ~ m1_subset_1(F_440,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_440,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_11517])).

tff(c_11762,plain,(
    ! [F_896] :
      ( r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),F_896)
      | ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),F_896)
      | ~ m1_subset_1(F_896,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_896,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_11538])).

tff(c_28,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_66,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28])).

tff(c_11765,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),'#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_11762,c_66])).

tff(c_11769,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_65,c_30,c_11765])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:23:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.59/5.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.75/5.57  
% 13.75/5.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.75/5.57  %$ r2_funct_2 > r1_tmap_1 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 13.75/5.57  
% 13.75/5.57  %Foreground sorts:
% 13.75/5.57  
% 13.75/5.57  
% 13.75/5.57  %Background operators:
% 13.75/5.57  
% 13.75/5.57  
% 13.75/5.57  %Foreground operators:
% 13.75/5.57  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 13.75/5.57  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 13.75/5.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.75/5.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.75/5.57  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 13.75/5.57  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 13.75/5.57  tff('#skF_7', type, '#skF_7': $i).
% 13.75/5.57  tff('#skF_5', type, '#skF_5': $i).
% 13.75/5.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.75/5.57  tff('#skF_6', type, '#skF_6': $i).
% 13.75/5.57  tff('#skF_2', type, '#skF_2': $i).
% 13.75/5.57  tff('#skF_3', type, '#skF_3': $i).
% 13.75/5.57  tff('#skF_1', type, '#skF_1': $i).
% 13.75/5.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.75/5.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.75/5.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.75/5.57  tff('#skF_4', type, '#skF_4': $i).
% 13.75/5.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.75/5.57  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 13.75/5.57  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 13.75/5.57  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 13.75/5.57  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 13.75/5.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 13.75/5.57  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 13.75/5.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.75/5.57  
% 13.75/5.62  tff(f_298, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(D, B, k2_tmap_1(A, B, E, D), F)) => r1_tmap_1(C, B, k2_tmap_1(A, B, E, C), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_tmap_1)).
% 13.75/5.62  tff(f_50, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 13.75/5.62  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 13.75/5.62  tff(f_150, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 13.75/5.62  tff(f_116, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 13.75/5.62  tff(f_84, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 13.75/5.62  tff(f_146, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 13.75/5.62  tff(f_41, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 13.75/5.62  tff(f_237, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((r2_funct_2(u1_struct_0(C), u1_struct_0(B), F, k2_tmap_1(A, B, E, C)) & m1_pre_topc(D, C)) => r2_funct_2(u1_struct_0(D), u1_struct_0(B), k3_tmap_1(A, B, C, D, F), k2_tmap_1(A, B, E, D))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tmap_1)).
% 13.75/5.62  tff(f_190, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 13.75/5.62  tff(c_36, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_298])).
% 13.75/5.62  tff(c_32, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_298])).
% 13.75/5.62  tff(c_34, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_298])).
% 13.75/5.62  tff(c_65, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34])).
% 13.75/5.62  tff(c_30, plain, (r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_298])).
% 13.75/5.62  tff(c_52, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_298])).
% 13.75/5.62  tff(c_38, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_298])).
% 13.75/5.62  tff(c_48, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_298])).
% 13.75/5.62  tff(c_58, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_298])).
% 13.75/5.62  tff(c_62, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_298])).
% 13.75/5.62  tff(c_60, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_298])).
% 13.75/5.62  tff(c_46, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_298])).
% 13.75/5.62  tff(c_95, plain, (![B_319, A_320]: (v2_pre_topc(B_319) | ~m1_pre_topc(B_319, A_320) | ~l1_pre_topc(A_320) | ~v2_pre_topc(A_320))), inference(cnfTransformation, [status(thm)], [f_50])).
% 13.75/5.62  tff(c_104, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_95])).
% 13.75/5.62  tff(c_114, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_104])).
% 13.75/5.62  tff(c_72, plain, (![B_317, A_318]: (l1_pre_topc(B_317) | ~m1_pre_topc(B_317, A_318) | ~l1_pre_topc(A_318))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.75/5.62  tff(c_81, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_72])).
% 13.75/5.62  tff(c_89, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_81])).
% 13.75/5.62  tff(c_56, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_298])).
% 13.75/5.62  tff(c_54, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_298])).
% 13.75/5.62  tff(c_64, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_298])).
% 13.75/5.62  tff(c_20, plain, (![A_62]: (m1_pre_topc(A_62, A_62) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_150])).
% 13.75/5.62  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_298])).
% 13.75/5.62  tff(c_42, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_298])).
% 13.75/5.62  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_298])).
% 13.75/5.62  tff(c_285, plain, (![D_365, C_364, A_362, B_366, E_363]: (k3_tmap_1(A_362, B_366, C_364, D_365, E_363)=k2_partfun1(u1_struct_0(C_364), u1_struct_0(B_366), E_363, u1_struct_0(D_365)) | ~m1_pre_topc(D_365, C_364) | ~m1_subset_1(E_363, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_364), u1_struct_0(B_366)))) | ~v1_funct_2(E_363, u1_struct_0(C_364), u1_struct_0(B_366)) | ~v1_funct_1(E_363) | ~m1_pre_topc(D_365, A_362) | ~m1_pre_topc(C_364, A_362) | ~l1_pre_topc(B_366) | ~v2_pre_topc(B_366) | v2_struct_0(B_366) | ~l1_pre_topc(A_362) | ~v2_pre_topc(A_362) | v2_struct_0(A_362))), inference(cnfTransformation, [status(thm)], [f_116])).
% 13.75/5.62  tff(c_289, plain, (![A_362, D_365]: (k3_tmap_1(A_362, '#skF_2', '#skF_1', D_365, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_365)) | ~m1_pre_topc(D_365, '#skF_1') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_365, A_362) | ~m1_pre_topc('#skF_1', A_362) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_362) | ~v2_pre_topc(A_362) | v2_struct_0(A_362))), inference(resolution, [status(thm)], [c_40, c_285])).
% 13.75/5.62  tff(c_293, plain, (![A_362, D_365]: (k3_tmap_1(A_362, '#skF_2', '#skF_1', D_365, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_365)) | ~m1_pre_topc(D_365, '#skF_1') | ~m1_pre_topc(D_365, A_362) | ~m1_pre_topc('#skF_1', A_362) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_362) | ~v2_pre_topc(A_362) | v2_struct_0(A_362))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_44, c_42, c_289])).
% 13.75/5.62  tff(c_314, plain, (![A_374, D_375]: (k3_tmap_1(A_374, '#skF_2', '#skF_1', D_375, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_375)) | ~m1_pre_topc(D_375, '#skF_1') | ~m1_pre_topc(D_375, A_374) | ~m1_pre_topc('#skF_1', A_374) | ~l1_pre_topc(A_374) | ~v2_pre_topc(A_374) | v2_struct_0(A_374))), inference(negUnitSimplification, [status(thm)], [c_58, c_293])).
% 13.75/5.62  tff(c_324, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_314])).
% 13.75/5.62  tff(c_340, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_46, c_324])).
% 13.75/5.62  tff(c_341, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_64, c_340])).
% 13.75/5.62  tff(c_347, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_341])).
% 13.75/5.62  tff(c_350, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_347])).
% 13.75/5.62  tff(c_354, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_350])).
% 13.75/5.62  tff(c_356, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_341])).
% 13.75/5.62  tff(c_355, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_341])).
% 13.75/5.62  tff(c_248, plain, (![A_345, B_346, C_347, D_348]: (k2_partfun1(u1_struct_0(A_345), u1_struct_0(B_346), C_347, u1_struct_0(D_348))=k2_tmap_1(A_345, B_346, C_347, D_348) | ~m1_pre_topc(D_348, A_345) | ~m1_subset_1(C_347, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_345), u1_struct_0(B_346)))) | ~v1_funct_2(C_347, u1_struct_0(A_345), u1_struct_0(B_346)) | ~v1_funct_1(C_347) | ~l1_pre_topc(B_346) | ~v2_pre_topc(B_346) | v2_struct_0(B_346) | ~l1_pre_topc(A_345) | ~v2_pre_topc(A_345) | v2_struct_0(A_345))), inference(cnfTransformation, [status(thm)], [f_84])).
% 13.75/5.62  tff(c_250, plain, (![D_348]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_348))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_348) | ~m1_pre_topc(D_348, '#skF_1') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_248])).
% 13.75/5.62  tff(c_253, plain, (![D_348]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_348))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_348) | ~m1_pre_topc(D_348, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_44, c_42, c_250])).
% 13.75/5.62  tff(c_254, plain, (![D_348]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_348))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_348) | ~m1_pre_topc(D_348, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_253])).
% 13.75/5.62  tff(c_398, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_355, c_254])).
% 13.75/5.62  tff(c_405, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_398])).
% 13.75/5.62  tff(c_240, plain, (![C_342, E_339, B_338, D_341, A_340]: (v1_funct_1(k3_tmap_1(A_340, B_338, C_342, D_341, E_339)) | ~m1_subset_1(E_339, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_342), u1_struct_0(B_338)))) | ~v1_funct_2(E_339, u1_struct_0(C_342), u1_struct_0(B_338)) | ~v1_funct_1(E_339) | ~m1_pre_topc(D_341, A_340) | ~m1_pre_topc(C_342, A_340) | ~l1_pre_topc(B_338) | ~v2_pre_topc(B_338) | v2_struct_0(B_338) | ~l1_pre_topc(A_340) | ~v2_pre_topc(A_340) | v2_struct_0(A_340))), inference(cnfTransformation, [status(thm)], [f_146])).
% 13.75/5.62  tff(c_242, plain, (![A_340, D_341]: (v1_funct_1(k3_tmap_1(A_340, '#skF_2', '#skF_1', D_341, '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_341, A_340) | ~m1_pre_topc('#skF_1', A_340) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_340) | ~v2_pre_topc(A_340) | v2_struct_0(A_340))), inference(resolution, [status(thm)], [c_40, c_240])).
% 13.75/5.62  tff(c_245, plain, (![A_340, D_341]: (v1_funct_1(k3_tmap_1(A_340, '#skF_2', '#skF_1', D_341, '#skF_5')) | ~m1_pre_topc(D_341, A_340) | ~m1_pre_topc('#skF_1', A_340) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_340) | ~v2_pre_topc(A_340) | v2_struct_0(A_340))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_44, c_42, c_242])).
% 13.75/5.62  tff(c_246, plain, (![A_340, D_341]: (v1_funct_1(k3_tmap_1(A_340, '#skF_2', '#skF_1', D_341, '#skF_5')) | ~m1_pre_topc(D_341, A_340) | ~m1_pre_topc('#skF_1', A_340) | ~l1_pre_topc(A_340) | ~v2_pre_topc(A_340) | v2_struct_0(A_340))), inference(negUnitSimplification, [status(thm)], [c_58, c_245])).
% 13.75/5.62  tff(c_419, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_405, c_246])).
% 13.75/5.62  tff(c_429, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_356, c_46, c_419])).
% 13.75/5.62  tff(c_430, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_64, c_429])).
% 13.75/5.62  tff(c_264, plain, (![B_350, C_354, A_352, E_351, D_353]: (v1_funct_2(k3_tmap_1(A_352, B_350, C_354, D_353, E_351), u1_struct_0(D_353), u1_struct_0(B_350)) | ~m1_subset_1(E_351, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_354), u1_struct_0(B_350)))) | ~v1_funct_2(E_351, u1_struct_0(C_354), u1_struct_0(B_350)) | ~v1_funct_1(E_351) | ~m1_pre_topc(D_353, A_352) | ~m1_pre_topc(C_354, A_352) | ~l1_pre_topc(B_350) | ~v2_pre_topc(B_350) | v2_struct_0(B_350) | ~l1_pre_topc(A_352) | ~v2_pre_topc(A_352) | v2_struct_0(A_352))), inference(cnfTransformation, [status(thm)], [f_146])).
% 13.75/5.62  tff(c_266, plain, (![A_352, D_353]: (v1_funct_2(k3_tmap_1(A_352, '#skF_2', '#skF_1', D_353, '#skF_5'), u1_struct_0(D_353), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_353, A_352) | ~m1_pre_topc('#skF_1', A_352) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_352) | ~v2_pre_topc(A_352) | v2_struct_0(A_352))), inference(resolution, [status(thm)], [c_40, c_264])).
% 13.75/5.62  tff(c_269, plain, (![A_352, D_353]: (v1_funct_2(k3_tmap_1(A_352, '#skF_2', '#skF_1', D_353, '#skF_5'), u1_struct_0(D_353), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_353, A_352) | ~m1_pre_topc('#skF_1', A_352) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_352) | ~v2_pre_topc(A_352) | v2_struct_0(A_352))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_44, c_42, c_266])).
% 13.75/5.62  tff(c_270, plain, (![A_352, D_353]: (v1_funct_2(k3_tmap_1(A_352, '#skF_2', '#skF_1', D_353, '#skF_5'), u1_struct_0(D_353), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_353, A_352) | ~m1_pre_topc('#skF_1', A_352) | ~l1_pre_topc(A_352) | ~v2_pre_topc(A_352) | v2_struct_0(A_352))), inference(negUnitSimplification, [status(thm)], [c_58, c_269])).
% 13.75/5.62  tff(c_416, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_405, c_270])).
% 13.75/5.62  tff(c_426, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_356, c_46, c_416])).
% 13.75/5.62  tff(c_427, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_64, c_426])).
% 13.75/5.62  tff(c_14, plain, (![A_57, E_61, B_58, D_60, C_59]: (m1_subset_1(k3_tmap_1(A_57, B_58, C_59, D_60, E_61), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_60), u1_struct_0(B_58)))) | ~m1_subset_1(E_61, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_59), u1_struct_0(B_58)))) | ~v1_funct_2(E_61, u1_struct_0(C_59), u1_struct_0(B_58)) | ~v1_funct_1(E_61) | ~m1_pre_topc(D_60, A_57) | ~m1_pre_topc(C_59, A_57) | ~l1_pre_topc(B_58) | ~v2_pre_topc(B_58) | v2_struct_0(B_58) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_146])).
% 13.75/5.62  tff(c_413, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_405, c_14])).
% 13.75/5.62  tff(c_423, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_356, c_46, c_44, c_42, c_40, c_413])).
% 13.75/5.62  tff(c_424, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_423])).
% 13.75/5.62  tff(c_10, plain, (![A_11, B_19, C_23, D_25]: (k2_partfun1(u1_struct_0(A_11), u1_struct_0(B_19), C_23, u1_struct_0(D_25))=k2_tmap_1(A_11, B_19, C_23, D_25) | ~m1_pre_topc(D_25, A_11) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_11), u1_struct_0(B_19)))) | ~v1_funct_2(C_23, u1_struct_0(A_11), u1_struct_0(B_19)) | ~v1_funct_1(C_23) | ~l1_pre_topc(B_19) | ~v2_pre_topc(B_19) | v2_struct_0(B_19) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_84])).
% 13.75/5.62  tff(c_440, plain, (![D_25]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_25))=k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), D_25) | ~m1_pre_topc(D_25, '#skF_4') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_424, c_10])).
% 13.75/5.62  tff(c_459, plain, (![D_25]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_25))=k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), D_25) | ~m1_pre_topc(D_25, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_89, c_56, c_54, c_430, c_427, c_440])).
% 13.75/5.62  tff(c_460, plain, (![D_25]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_25))=k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), D_25) | ~m1_pre_topc(D_25, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_48, c_58, c_459])).
% 13.75/5.62  tff(c_12, plain, (![A_26, C_50, B_42, D_54, E_56]: (k3_tmap_1(A_26, B_42, C_50, D_54, E_56)=k2_partfun1(u1_struct_0(C_50), u1_struct_0(B_42), E_56, u1_struct_0(D_54)) | ~m1_pre_topc(D_54, C_50) | ~m1_subset_1(E_56, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_50), u1_struct_0(B_42)))) | ~v1_funct_2(E_56, u1_struct_0(C_50), u1_struct_0(B_42)) | ~v1_funct_1(E_56) | ~m1_pre_topc(D_54, A_26) | ~m1_pre_topc(C_50, A_26) | ~l1_pre_topc(B_42) | ~v2_pre_topc(B_42) | v2_struct_0(B_42) | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_116])).
% 13.75/5.62  tff(c_436, plain, (![A_26, D_54]: (k3_tmap_1(A_26, '#skF_2', '#skF_4', D_54, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_54)) | ~m1_pre_topc(D_54, '#skF_4') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_pre_topc(D_54, A_26) | ~m1_pre_topc('#skF_4', A_26) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(resolution, [status(thm)], [c_424, c_12])).
% 13.75/5.62  tff(c_451, plain, (![A_26, D_54]: (k3_tmap_1(A_26, '#skF_2', '#skF_4', D_54, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_54)) | ~m1_pre_topc(D_54, '#skF_4') | ~m1_pre_topc(D_54, A_26) | ~m1_pre_topc('#skF_4', A_26) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_430, c_427, c_436])).
% 13.75/5.62  tff(c_1361, plain, (![A_460, D_461]: (k3_tmap_1(A_460, '#skF_2', '#skF_4', D_461, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_461)) | ~m1_pre_topc(D_461, '#skF_4') | ~m1_pre_topc(D_461, A_460) | ~m1_pre_topc('#skF_4', A_460) | ~l1_pre_topc(A_460) | ~v2_pre_topc(A_460) | v2_struct_0(A_460))), inference(negUnitSimplification, [status(thm)], [c_58, c_451])).
% 13.75/5.62  tff(c_1392, plain, (![D_461, A_460]: (m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_461)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_461), u1_struct_0('#skF_2')))) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_pre_topc(D_461, A_460) | ~m1_pre_topc('#skF_4', A_460) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_460) | ~v2_pre_topc(A_460) | v2_struct_0(A_460) | ~m1_pre_topc(D_461, '#skF_4') | ~m1_pre_topc(D_461, A_460) | ~m1_pre_topc('#skF_4', A_460) | ~l1_pre_topc(A_460) | ~v2_pre_topc(A_460) | v2_struct_0(A_460))), inference(superposition, [status(thm), theory('equality')], [c_1361, c_14])).
% 13.75/5.62  tff(c_1419, plain, (![D_461, A_460]: (m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_461)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_461), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2') | ~m1_pre_topc(D_461, '#skF_4') | ~m1_pre_topc(D_461, A_460) | ~m1_pre_topc('#skF_4', A_460) | ~l1_pre_topc(A_460) | ~v2_pre_topc(A_460) | v2_struct_0(A_460))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_430, c_427, c_424, c_1392])).
% 13.75/5.62  tff(c_1422, plain, (![D_462, A_463]: (m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_462)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_462), u1_struct_0('#skF_2')))) | ~m1_pre_topc(D_462, '#skF_4') | ~m1_pre_topc(D_462, A_463) | ~m1_pre_topc('#skF_4', A_463) | ~l1_pre_topc(A_463) | ~v2_pre_topc(A_463) | v2_struct_0(A_463))), inference(negUnitSimplification, [status(thm)], [c_58, c_1419])).
% 13.75/5.62  tff(c_1434, plain, (m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~m1_pre_topc('#skF_4', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_1422])).
% 13.75/5.62  tff(c_1454, plain, (m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_46, c_1434])).
% 13.75/5.62  tff(c_1455, plain, (m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~m1_pre_topc('#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_64, c_1454])).
% 13.75/5.62  tff(c_1590, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_1455])).
% 13.75/5.62  tff(c_1594, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_20, c_1590])).
% 13.75/5.62  tff(c_1598, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_1594])).
% 13.75/5.62  tff(c_1600, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_1455])).
% 13.75/5.62  tff(c_272, plain, (![B_357, C_361, A_359, E_358, D_360]: (m1_subset_1(k3_tmap_1(A_359, B_357, C_361, D_360, E_358), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_360), u1_struct_0(B_357)))) | ~m1_subset_1(E_358, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_361), u1_struct_0(B_357)))) | ~v1_funct_2(E_358, u1_struct_0(C_361), u1_struct_0(B_357)) | ~v1_funct_1(E_358) | ~m1_pre_topc(D_360, A_359) | ~m1_pre_topc(C_361, A_359) | ~l1_pre_topc(B_357) | ~v2_pre_topc(B_357) | v2_struct_0(B_357) | ~l1_pre_topc(A_359) | ~v2_pre_topc(A_359) | v2_struct_0(A_359))), inference(cnfTransformation, [status(thm)], [f_146])).
% 13.75/5.62  tff(c_18, plain, (![A_57, E_61, B_58, D_60, C_59]: (v1_funct_1(k3_tmap_1(A_57, B_58, C_59, D_60, E_61)) | ~m1_subset_1(E_61, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_59), u1_struct_0(B_58)))) | ~v1_funct_2(E_61, u1_struct_0(C_59), u1_struct_0(B_58)) | ~v1_funct_1(E_61) | ~m1_pre_topc(D_60, A_57) | ~m1_pre_topc(C_59, A_57) | ~l1_pre_topc(B_58) | ~v2_pre_topc(B_58) | v2_struct_0(B_58) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_146])).
% 13.75/5.62  tff(c_628, plain, (![C_391, A_390, D_388, D_393, B_389, A_392, E_387]: (v1_funct_1(k3_tmap_1(A_392, B_389, D_388, D_393, k3_tmap_1(A_390, B_389, C_391, D_388, E_387))) | ~v1_funct_2(k3_tmap_1(A_390, B_389, C_391, D_388, E_387), u1_struct_0(D_388), u1_struct_0(B_389)) | ~v1_funct_1(k3_tmap_1(A_390, B_389, C_391, D_388, E_387)) | ~m1_pre_topc(D_393, A_392) | ~m1_pre_topc(D_388, A_392) | ~l1_pre_topc(A_392) | ~v2_pre_topc(A_392) | v2_struct_0(A_392) | ~m1_subset_1(E_387, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_391), u1_struct_0(B_389)))) | ~v1_funct_2(E_387, u1_struct_0(C_391), u1_struct_0(B_389)) | ~v1_funct_1(E_387) | ~m1_pre_topc(D_388, A_390) | ~m1_pre_topc(C_391, A_390) | ~l1_pre_topc(B_389) | ~v2_pre_topc(B_389) | v2_struct_0(B_389) | ~l1_pre_topc(A_390) | ~v2_pre_topc(A_390) | v2_struct_0(A_390))), inference(resolution, [status(thm)], [c_272, c_18])).
% 13.75/5.62  tff(c_632, plain, (![A_392, D_393]: (v1_funct_1(k3_tmap_1(A_392, '#skF_2', '#skF_4', D_393, k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5'))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')) | ~m1_pre_topc(D_393, A_392) | ~m1_pre_topc('#skF_4', A_392) | ~l1_pre_topc(A_392) | ~v2_pre_topc(A_392) | v2_struct_0(A_392) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_405, c_628])).
% 13.75/5.62  tff(c_639, plain, (![A_392, D_393]: (v1_funct_1(k3_tmap_1(A_392, '#skF_2', '#skF_4', D_393, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_pre_topc(D_393, A_392) | ~m1_pre_topc('#skF_4', A_392) | ~l1_pre_topc(A_392) | ~v2_pre_topc(A_392) | v2_struct_0(A_392) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_356, c_46, c_44, c_42, c_40, c_430, c_405, c_427, c_405, c_632])).
% 13.75/5.62  tff(c_640, plain, (![A_392, D_393]: (v1_funct_1(k3_tmap_1(A_392, '#skF_2', '#skF_4', D_393, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_pre_topc(D_393, A_392) | ~m1_pre_topc('#skF_4', A_392) | ~l1_pre_topc(A_392) | ~v2_pre_topc(A_392) | v2_struct_0(A_392))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_639])).
% 13.75/5.62  tff(c_4514, plain, (![D_568, A_569]: (v1_funct_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_568))) | ~m1_pre_topc(D_568, A_569) | ~m1_pre_topc('#skF_4', A_569) | ~l1_pre_topc(A_569) | ~v2_pre_topc(A_569) | v2_struct_0(A_569) | ~m1_pre_topc(D_568, '#skF_4') | ~m1_pre_topc(D_568, A_569) | ~m1_pre_topc('#skF_4', A_569) | ~l1_pre_topc(A_569) | ~v2_pre_topc(A_569) | v2_struct_0(A_569))), inference(superposition, [status(thm), theory('equality')], [c_1361, c_640])).
% 13.75/5.62  tff(c_4528, plain, (v1_funct_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_38, c_4514])).
% 13.75/5.62  tff(c_4554, plain, (v1_funct_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_3'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_89, c_1600, c_38, c_4528])).
% 13.75/5.62  tff(c_4555, plain, (v1_funct_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_48, c_4554])).
% 13.75/5.62  tff(c_4569, plain, (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_460, c_4555])).
% 13.75/5.62  tff(c_4573, plain, (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4569])).
% 13.75/5.62  tff(c_16, plain, (![A_57, E_61, B_58, D_60, C_59]: (v1_funct_2(k3_tmap_1(A_57, B_58, C_59, D_60, E_61), u1_struct_0(D_60), u1_struct_0(B_58)) | ~m1_subset_1(E_61, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_59), u1_struct_0(B_58)))) | ~v1_funct_2(E_61, u1_struct_0(C_59), u1_struct_0(B_58)) | ~v1_funct_1(E_61) | ~m1_pre_topc(D_60, A_57) | ~m1_pre_topc(C_59, A_57) | ~l1_pre_topc(B_58) | ~v2_pre_topc(B_58) | v2_struct_0(B_58) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_146])).
% 13.75/5.62  tff(c_782, plain, (![D_396, B_397, A_400, D_401, A_398, E_395, C_399]: (v1_funct_2(k3_tmap_1(A_400, B_397, D_396, D_401, k3_tmap_1(A_398, B_397, C_399, D_396, E_395)), u1_struct_0(D_401), u1_struct_0(B_397)) | ~v1_funct_2(k3_tmap_1(A_398, B_397, C_399, D_396, E_395), u1_struct_0(D_396), u1_struct_0(B_397)) | ~v1_funct_1(k3_tmap_1(A_398, B_397, C_399, D_396, E_395)) | ~m1_pre_topc(D_401, A_400) | ~m1_pre_topc(D_396, A_400) | ~l1_pre_topc(A_400) | ~v2_pre_topc(A_400) | v2_struct_0(A_400) | ~m1_subset_1(E_395, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_399), u1_struct_0(B_397)))) | ~v1_funct_2(E_395, u1_struct_0(C_399), u1_struct_0(B_397)) | ~v1_funct_1(E_395) | ~m1_pre_topc(D_396, A_398) | ~m1_pre_topc(C_399, A_398) | ~l1_pre_topc(B_397) | ~v2_pre_topc(B_397) | v2_struct_0(B_397) | ~l1_pre_topc(A_398) | ~v2_pre_topc(A_398) | v2_struct_0(A_398))), inference(resolution, [status(thm)], [c_272, c_16])).
% 13.75/5.62  tff(c_793, plain, (![A_400, D_401]: (v1_funct_2(k3_tmap_1(A_400, '#skF_2', '#skF_4', D_401, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0(D_401), u1_struct_0('#skF_2')) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')) | ~m1_pre_topc(D_401, A_400) | ~m1_pre_topc('#skF_4', A_400) | ~l1_pre_topc(A_400) | ~v2_pre_topc(A_400) | v2_struct_0(A_400) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_405, c_782])).
% 13.75/5.62  tff(c_802, plain, (![A_400, D_401]: (v1_funct_2(k3_tmap_1(A_400, '#skF_2', '#skF_4', D_401, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0(D_401), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_401, A_400) | ~m1_pre_topc('#skF_4', A_400) | ~l1_pre_topc(A_400) | ~v2_pre_topc(A_400) | v2_struct_0(A_400) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_356, c_46, c_44, c_42, c_40, c_430, c_405, c_427, c_405, c_793])).
% 13.75/5.62  tff(c_803, plain, (![A_400, D_401]: (v1_funct_2(k3_tmap_1(A_400, '#skF_2', '#skF_4', D_401, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0(D_401), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_401, A_400) | ~m1_pre_topc('#skF_4', A_400) | ~l1_pre_topc(A_400) | ~v2_pre_topc(A_400) | v2_struct_0(A_400))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_802])).
% 13.75/5.62  tff(c_4981, plain, (![D_597, A_598]: (v1_funct_2(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0(D_597)), u1_struct_0(D_597), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_597, A_598) | ~m1_pre_topc('#skF_4', A_598) | ~l1_pre_topc(A_598) | ~v2_pre_topc(A_598) | v2_struct_0(A_598) | ~m1_pre_topc(D_597, '#skF_4') | ~m1_pre_topc(D_597, A_598) | ~m1_pre_topc('#skF_4', A_598) | ~l1_pre_topc(A_598) | ~v2_pre_topc(A_598) | v2_struct_0(A_598))), inference(superposition, [status(thm), theory('equality')], [c_1361, c_803])).
% 13.75/5.62  tff(c_4995, plain, (v1_funct_2(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_38, c_4981])).
% 13.75/5.62  tff(c_5021, plain, (v1_funct_2(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_89, c_1600, c_38, c_4995])).
% 13.75/5.62  tff(c_5022, plain, (v1_funct_2(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_48, c_5021])).
% 13.75/5.62  tff(c_5036, plain, (v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_460, c_5022])).
% 13.75/5.62  tff(c_5040, plain, (v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_5036])).
% 13.75/5.62  tff(c_50, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_298])).
% 13.75/5.62  tff(c_1436, plain, (m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_1422])).
% 13.75/5.62  tff(c_1458, plain, (m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_46, c_38, c_1436])).
% 13.75/5.62  tff(c_1459, plain, (m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_1458])).
% 13.75/5.62  tff(c_1511, plain, (m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_460, c_1459])).
% 13.75/5.62  tff(c_1544, plain, (m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1511])).
% 13.75/5.62  tff(c_326, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_314])).
% 13.75/5.62  tff(c_344, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_50, c_326])).
% 13.75/5.62  tff(c_345, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_64, c_344])).
% 13.75/5.62  tff(c_646, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_356, c_345])).
% 13.75/5.62  tff(c_650, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_646, c_254])).
% 13.75/5.62  tff(c_657, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_650])).
% 13.75/5.62  tff(c_679, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_657, c_246])).
% 13.75/5.62  tff(c_698, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_356, c_50, c_679])).
% 13.75/5.62  tff(c_699, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_64, c_698])).
% 13.75/5.62  tff(c_676, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_657, c_270])).
% 13.75/5.62  tff(c_695, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_356, c_50, c_676])).
% 13.75/5.62  tff(c_696, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_64, c_695])).
% 13.75/5.62  tff(c_673, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_657, c_14])).
% 13.75/5.62  tff(c_692, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_356, c_50, c_44, c_42, c_40, c_673])).
% 13.75/5.62  tff(c_693, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_692])).
% 13.75/5.62  tff(c_1016, plain, (![D_427, E_424, A_426, C_428, A_422, D_425, B_423]: (k3_tmap_1(A_422, B_423, D_427, D_425, k3_tmap_1(A_426, B_423, C_428, D_427, E_424))=k2_partfun1(u1_struct_0(D_427), u1_struct_0(B_423), k3_tmap_1(A_426, B_423, C_428, D_427, E_424), u1_struct_0(D_425)) | ~m1_pre_topc(D_425, D_427) | ~v1_funct_2(k3_tmap_1(A_426, B_423, C_428, D_427, E_424), u1_struct_0(D_427), u1_struct_0(B_423)) | ~v1_funct_1(k3_tmap_1(A_426, B_423, C_428, D_427, E_424)) | ~m1_pre_topc(D_425, A_422) | ~m1_pre_topc(D_427, A_422) | ~l1_pre_topc(A_422) | ~v2_pre_topc(A_422) | v2_struct_0(A_422) | ~m1_subset_1(E_424, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_428), u1_struct_0(B_423)))) | ~v1_funct_2(E_424, u1_struct_0(C_428), u1_struct_0(B_423)) | ~v1_funct_1(E_424) | ~m1_pre_topc(D_427, A_426) | ~m1_pre_topc(C_428, A_426) | ~l1_pre_topc(B_423) | ~v2_pre_topc(B_423) | v2_struct_0(B_423) | ~l1_pre_topc(A_426) | ~v2_pre_topc(A_426) | v2_struct_0(A_426))), inference(resolution, [status(thm)], [c_14, c_285])).
% 13.75/5.62  tff(c_1026, plain, (![A_422, D_427, D_425, A_426]: (k3_tmap_1(A_422, '#skF_2', D_427, D_425, k3_tmap_1(A_426, '#skF_2', '#skF_1', D_427, '#skF_5'))=k2_partfun1(u1_struct_0(D_427), u1_struct_0('#skF_2'), k3_tmap_1(A_426, '#skF_2', '#skF_1', D_427, '#skF_5'), u1_struct_0(D_425)) | ~m1_pre_topc(D_425, D_427) | ~v1_funct_2(k3_tmap_1(A_426, '#skF_2', '#skF_1', D_427, '#skF_5'), u1_struct_0(D_427), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_426, '#skF_2', '#skF_1', D_427, '#skF_5')) | ~m1_pre_topc(D_425, A_422) | ~m1_pre_topc(D_427, A_422) | ~l1_pre_topc(A_422) | ~v2_pre_topc(A_422) | v2_struct_0(A_422) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_427, A_426) | ~m1_pre_topc('#skF_1', A_426) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_426) | ~v2_pre_topc(A_426) | v2_struct_0(A_426))), inference(resolution, [status(thm)], [c_40, c_1016])).
% 13.75/5.62  tff(c_1042, plain, (![A_422, D_427, D_425, A_426]: (k3_tmap_1(A_422, '#skF_2', D_427, D_425, k3_tmap_1(A_426, '#skF_2', '#skF_1', D_427, '#skF_5'))=k2_partfun1(u1_struct_0(D_427), u1_struct_0('#skF_2'), k3_tmap_1(A_426, '#skF_2', '#skF_1', D_427, '#skF_5'), u1_struct_0(D_425)) | ~m1_pre_topc(D_425, D_427) | ~v1_funct_2(k3_tmap_1(A_426, '#skF_2', '#skF_1', D_427, '#skF_5'), u1_struct_0(D_427), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_426, '#skF_2', '#skF_1', D_427, '#skF_5')) | ~m1_pre_topc(D_425, A_422) | ~m1_pre_topc(D_427, A_422) | ~l1_pre_topc(A_422) | ~v2_pre_topc(A_422) | v2_struct_0(A_422) | ~m1_pre_topc(D_427, A_426) | ~m1_pre_topc('#skF_1', A_426) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_426) | ~v2_pre_topc(A_426) | v2_struct_0(A_426))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_44, c_42, c_1026])).
% 13.75/5.62  tff(c_2068, plain, (![A_479, D_480, D_481, A_482]: (k3_tmap_1(A_479, '#skF_2', D_480, D_481, k3_tmap_1(A_482, '#skF_2', '#skF_1', D_480, '#skF_5'))=k2_partfun1(u1_struct_0(D_480), u1_struct_0('#skF_2'), k3_tmap_1(A_482, '#skF_2', '#skF_1', D_480, '#skF_5'), u1_struct_0(D_481)) | ~m1_pre_topc(D_481, D_480) | ~v1_funct_2(k3_tmap_1(A_482, '#skF_2', '#skF_1', D_480, '#skF_5'), u1_struct_0(D_480), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_482, '#skF_2', '#skF_1', D_480, '#skF_5')) | ~m1_pre_topc(D_481, A_479) | ~m1_pre_topc(D_480, A_479) | ~l1_pre_topc(A_479) | ~v2_pre_topc(A_479) | v2_struct_0(A_479) | ~m1_pre_topc(D_480, A_482) | ~m1_pre_topc('#skF_1', A_482) | ~l1_pre_topc(A_482) | ~v2_pre_topc(A_482) | v2_struct_0(A_482))), inference(negUnitSimplification, [status(thm)], [c_58, c_1042])).
% 13.75/5.62  tff(c_844, plain, (![C_416, B_414, D_413, A_415, D_417, E_412]: (k2_partfun1(u1_struct_0(D_413), u1_struct_0(B_414), k3_tmap_1(A_415, B_414, C_416, D_413, E_412), u1_struct_0(D_417))=k2_tmap_1(D_413, B_414, k3_tmap_1(A_415, B_414, C_416, D_413, E_412), D_417) | ~m1_pre_topc(D_417, D_413) | ~v1_funct_2(k3_tmap_1(A_415, B_414, C_416, D_413, E_412), u1_struct_0(D_413), u1_struct_0(B_414)) | ~v1_funct_1(k3_tmap_1(A_415, B_414, C_416, D_413, E_412)) | ~l1_pre_topc(D_413) | ~v2_pre_topc(D_413) | v2_struct_0(D_413) | ~m1_subset_1(E_412, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_416), u1_struct_0(B_414)))) | ~v1_funct_2(E_412, u1_struct_0(C_416), u1_struct_0(B_414)) | ~v1_funct_1(E_412) | ~m1_pre_topc(D_413, A_415) | ~m1_pre_topc(C_416, A_415) | ~l1_pre_topc(B_414) | ~v2_pre_topc(B_414) | v2_struct_0(B_414) | ~l1_pre_topc(A_415) | ~v2_pre_topc(A_415) | v2_struct_0(A_415))), inference(resolution, [status(thm)], [c_272, c_10])).
% 13.75/5.62  tff(c_854, plain, (![D_413, A_415, D_417]: (k2_partfun1(u1_struct_0(D_413), u1_struct_0('#skF_2'), k3_tmap_1(A_415, '#skF_2', '#skF_1', D_413, '#skF_5'), u1_struct_0(D_417))=k2_tmap_1(D_413, '#skF_2', k3_tmap_1(A_415, '#skF_2', '#skF_1', D_413, '#skF_5'), D_417) | ~m1_pre_topc(D_417, D_413) | ~v1_funct_2(k3_tmap_1(A_415, '#skF_2', '#skF_1', D_413, '#skF_5'), u1_struct_0(D_413), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_415, '#skF_2', '#skF_1', D_413, '#skF_5')) | ~l1_pre_topc(D_413) | ~v2_pre_topc(D_413) | v2_struct_0(D_413) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_413, A_415) | ~m1_pre_topc('#skF_1', A_415) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_415) | ~v2_pre_topc(A_415) | v2_struct_0(A_415))), inference(resolution, [status(thm)], [c_40, c_844])).
% 13.75/5.62  tff(c_870, plain, (![D_413, A_415, D_417]: (k2_partfun1(u1_struct_0(D_413), u1_struct_0('#skF_2'), k3_tmap_1(A_415, '#skF_2', '#skF_1', D_413, '#skF_5'), u1_struct_0(D_417))=k2_tmap_1(D_413, '#skF_2', k3_tmap_1(A_415, '#skF_2', '#skF_1', D_413, '#skF_5'), D_417) | ~m1_pre_topc(D_417, D_413) | ~v1_funct_2(k3_tmap_1(A_415, '#skF_2', '#skF_1', D_413, '#skF_5'), u1_struct_0(D_413), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_415, '#skF_2', '#skF_1', D_413, '#skF_5')) | ~l1_pre_topc(D_413) | ~v2_pre_topc(D_413) | v2_struct_0(D_413) | ~m1_pre_topc(D_413, A_415) | ~m1_pre_topc('#skF_1', A_415) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_415) | ~v2_pre_topc(A_415) | v2_struct_0(A_415))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_44, c_42, c_854])).
% 13.75/5.62  tff(c_871, plain, (![D_413, A_415, D_417]: (k2_partfun1(u1_struct_0(D_413), u1_struct_0('#skF_2'), k3_tmap_1(A_415, '#skF_2', '#skF_1', D_413, '#skF_5'), u1_struct_0(D_417))=k2_tmap_1(D_413, '#skF_2', k3_tmap_1(A_415, '#skF_2', '#skF_1', D_413, '#skF_5'), D_417) | ~m1_pre_topc(D_417, D_413) | ~v1_funct_2(k3_tmap_1(A_415, '#skF_2', '#skF_1', D_413, '#skF_5'), u1_struct_0(D_413), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_415, '#skF_2', '#skF_1', D_413, '#skF_5')) | ~l1_pre_topc(D_413) | ~v2_pre_topc(D_413) | v2_struct_0(D_413) | ~m1_pre_topc(D_413, A_415) | ~m1_pre_topc('#skF_1', A_415) | ~l1_pre_topc(A_415) | ~v2_pre_topc(A_415) | v2_struct_0(A_415))), inference(negUnitSimplification, [status(thm)], [c_58, c_870])).
% 13.75/5.62  tff(c_6785, plain, (![A_695, D_696, D_697, A_698]: (k3_tmap_1(A_695, '#skF_2', D_696, D_697, k3_tmap_1(A_698, '#skF_2', '#skF_1', D_696, '#skF_5'))=k2_tmap_1(D_696, '#skF_2', k3_tmap_1(A_698, '#skF_2', '#skF_1', D_696, '#skF_5'), D_697) | ~m1_pre_topc(D_697, D_696) | ~v1_funct_2(k3_tmap_1(A_698, '#skF_2', '#skF_1', D_696, '#skF_5'), u1_struct_0(D_696), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_698, '#skF_2', '#skF_1', D_696, '#skF_5')) | ~l1_pre_topc(D_696) | ~v2_pre_topc(D_696) | v2_struct_0(D_696) | ~m1_pre_topc(D_696, A_698) | ~m1_pre_topc('#skF_1', A_698) | ~l1_pre_topc(A_698) | ~v2_pre_topc(A_698) | v2_struct_0(A_698) | ~m1_pre_topc(D_697, D_696) | ~v1_funct_2(k3_tmap_1(A_698, '#skF_2', '#skF_1', D_696, '#skF_5'), u1_struct_0(D_696), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_698, '#skF_2', '#skF_1', D_696, '#skF_5')) | ~m1_pre_topc(D_697, A_695) | ~m1_pre_topc(D_696, A_695) | ~l1_pre_topc(A_695) | ~v2_pre_topc(A_695) | v2_struct_0(A_695) | ~m1_pre_topc(D_696, A_698) | ~m1_pre_topc('#skF_1', A_698) | ~l1_pre_topc(A_698) | ~v2_pre_topc(A_698) | v2_struct_0(A_698))), inference(superposition, [status(thm), theory('equality')], [c_2068, c_871])).
% 13.75/5.62  tff(c_6793, plain, (![A_695, D_697]: (k3_tmap_1(A_695, '#skF_2', '#skF_4', D_697, k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5'))=k2_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5'), D_697) | ~m1_pre_topc(D_697, '#skF_4') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~m1_pre_topc(D_697, '#skF_4') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')) | ~m1_pre_topc(D_697, A_695) | ~m1_pre_topc('#skF_4', A_695) | ~l1_pre_topc(A_695) | ~v2_pre_topc(A_695) | v2_struct_0(A_695) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_405, c_6785])).
% 13.75/5.62  tff(c_6803, plain, (![A_695, D_697]: (k3_tmap_1(A_695, '#skF_2', '#skF_4', D_697, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))=k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), D_697) | v2_struct_0('#skF_4') | ~m1_pre_topc(D_697, '#skF_4') | ~m1_pre_topc(D_697, A_695) | ~m1_pre_topc('#skF_4', A_695) | ~l1_pre_topc(A_695) | ~v2_pre_topc(A_695) | v2_struct_0(A_695) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_356, c_46, c_430, c_405, c_427, c_405, c_62, c_60, c_356, c_46, c_114, c_89, c_430, c_405, c_427, c_405, c_405, c_6793])).
% 13.75/5.62  tff(c_6804, plain, (![A_695, D_697]: (k3_tmap_1(A_695, '#skF_2', '#skF_4', D_697, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))=k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), D_697) | ~m1_pre_topc(D_697, '#skF_4') | ~m1_pre_topc(D_697, A_695) | ~m1_pre_topc('#skF_4', A_695) | ~l1_pre_topc(A_695) | ~v2_pre_topc(A_695) | v2_struct_0(A_695))), inference(negUnitSimplification, [status(thm)], [c_64, c_48, c_6803])).
% 13.75/5.62  tff(c_294, plain, (![A_362, D_365]: (k3_tmap_1(A_362, '#skF_2', '#skF_1', D_365, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_365)) | ~m1_pre_topc(D_365, '#skF_1') | ~m1_pre_topc(D_365, A_362) | ~m1_pre_topc('#skF_1', A_362) | ~l1_pre_topc(A_362) | ~v2_pre_topc(A_362) | v2_struct_0(A_362))), inference(negUnitSimplification, [status(thm)], [c_58, c_293])).
% 13.75/5.62  tff(c_358, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_1'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_356, c_294])).
% 13.75/5.62  tff(c_376, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_1'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_356, c_358])).
% 13.75/5.62  tff(c_377, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_1'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_64, c_376])).
% 13.75/5.62  tff(c_487, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_377, c_254])).
% 13.75/5.62  tff(c_494, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_356, c_487])).
% 13.75/5.62  tff(c_508, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1')) | ~m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_494, c_246])).
% 13.75/5.62  tff(c_518, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_356, c_356, c_508])).
% 13.75/5.62  tff(c_519, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_64, c_518])).
% 13.75/5.62  tff(c_505, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_494, c_270])).
% 13.75/5.62  tff(c_515, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_356, c_356, c_505])).
% 13.75/5.62  tff(c_516, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_64, c_515])).
% 13.75/5.62  tff(c_2126, plain, (![A_479, D_481]: (k3_tmap_1(A_479, '#skF_2', '#skF_1', D_481, k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_5'))=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0(D_481)) | ~m1_pre_topc(D_481, '#skF_1') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_5'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_5')) | ~m1_pre_topc(D_481, A_479) | ~m1_pre_topc('#skF_1', A_479) | ~l1_pre_topc(A_479) | ~v2_pre_topc(A_479) | v2_struct_0(A_479) | ~m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_494, c_2068])).
% 13.75/5.62  tff(c_2166, plain, (![A_479, D_481]: (k3_tmap_1(A_479, '#skF_2', '#skF_1', D_481, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'))=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0(D_481)) | ~m1_pre_topc(D_481, '#skF_1') | ~m1_pre_topc(D_481, A_479) | ~m1_pre_topc('#skF_1', A_479) | ~l1_pre_topc(A_479) | ~v2_pre_topc(A_479) | v2_struct_0(A_479) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_356, c_356, c_519, c_494, c_516, c_494, c_494, c_2126])).
% 13.75/5.62  tff(c_2504, plain, (![A_494, D_495]: (k3_tmap_1(A_494, '#skF_2', '#skF_1', D_495, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'))=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0(D_495)) | ~m1_pre_topc(D_495, '#skF_1') | ~m1_pre_topc(D_495, A_494) | ~m1_pre_topc('#skF_1', A_494) | ~l1_pre_topc(A_494) | ~v2_pre_topc(A_494) | v2_struct_0(A_494))), inference(negUnitSimplification, [status(thm)], [c_64, c_2166])).
% 13.75/5.62  tff(c_630, plain, (![A_392, D_393]: (v1_funct_1(k3_tmap_1(A_392, '#skF_2', '#skF_1', D_393, k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_5'))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_5')) | ~m1_pre_topc(D_393, A_392) | ~m1_pre_topc('#skF_1', A_392) | ~l1_pre_topc(A_392) | ~v2_pre_topc(A_392) | v2_struct_0(A_392) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_494, c_628])).
% 13.75/5.62  tff(c_636, plain, (![A_392, D_393]: (v1_funct_1(k3_tmap_1(A_392, '#skF_2', '#skF_1', D_393, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'))) | ~m1_pre_topc(D_393, A_392) | ~m1_pre_topc('#skF_1', A_392) | ~l1_pre_topc(A_392) | ~v2_pre_topc(A_392) | v2_struct_0(A_392) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_356, c_356, c_44, c_42, c_40, c_519, c_494, c_516, c_494, c_630])).
% 13.75/5.62  tff(c_637, plain, (![A_392, D_393]: (v1_funct_1(k3_tmap_1(A_392, '#skF_2', '#skF_1', D_393, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'))) | ~m1_pre_topc(D_393, A_392) | ~m1_pre_topc('#skF_1', A_392) | ~l1_pre_topc(A_392) | ~v2_pre_topc(A_392) | v2_struct_0(A_392))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_636])).
% 13.75/5.62  tff(c_4306, plain, (![D_554, A_555]: (v1_funct_1(k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0(D_554))) | ~m1_pre_topc(D_554, A_555) | ~m1_pre_topc('#skF_1', A_555) | ~l1_pre_topc(A_555) | ~v2_pre_topc(A_555) | v2_struct_0(A_555) | ~m1_pre_topc(D_554, '#skF_1') | ~m1_pre_topc(D_554, A_555) | ~m1_pre_topc('#skF_1', A_555) | ~l1_pre_topc(A_555) | ~v2_pre_topc(A_555) | v2_struct_0(A_555))), inference(superposition, [status(thm), theory('equality')], [c_2504, c_637])).
% 13.75/5.62  tff(c_4322, plain, (v1_funct_1(k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_4306])).
% 13.75/5.62  tff(c_4350, plain, (v1_funct_1(k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_4'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_356, c_46, c_4322])).
% 13.75/5.62  tff(c_4351, plain, (v1_funct_1(k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_64, c_4350])).
% 13.75/5.62  tff(c_790, plain, (![A_400, D_401]: (v1_funct_2(k3_tmap_1(A_400, '#skF_2', '#skF_1', D_401, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1')), u1_struct_0(D_401), u1_struct_0('#skF_2')) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_5'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_5')) | ~m1_pre_topc(D_401, A_400) | ~m1_pre_topc('#skF_1', A_400) | ~l1_pre_topc(A_400) | ~v2_pre_topc(A_400) | v2_struct_0(A_400) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_494, c_782])).
% 13.75/5.62  tff(c_799, plain, (![A_400, D_401]: (v1_funct_2(k3_tmap_1(A_400, '#skF_2', '#skF_1', D_401, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1')), u1_struct_0(D_401), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_401, A_400) | ~m1_pre_topc('#skF_1', A_400) | ~l1_pre_topc(A_400) | ~v2_pre_topc(A_400) | v2_struct_0(A_400) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_356, c_356, c_44, c_42, c_40, c_519, c_494, c_516, c_494, c_790])).
% 13.75/5.62  tff(c_800, plain, (![A_400, D_401]: (v1_funct_2(k3_tmap_1(A_400, '#skF_2', '#skF_1', D_401, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1')), u1_struct_0(D_401), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_401, A_400) | ~m1_pre_topc('#skF_1', A_400) | ~l1_pre_topc(A_400) | ~v2_pre_topc(A_400) | v2_struct_0(A_400))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_799])).
% 13.75/5.62  tff(c_5241, plain, (![D_618, A_619]: (v1_funct_2(k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0(D_618)), u1_struct_0(D_618), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_618, A_619) | ~m1_pre_topc('#skF_1', A_619) | ~l1_pre_topc(A_619) | ~v2_pre_topc(A_619) | v2_struct_0(A_619) | ~m1_pre_topc(D_618, '#skF_1') | ~m1_pre_topc(D_618, A_619) | ~m1_pre_topc('#skF_1', A_619) | ~l1_pre_topc(A_619) | ~v2_pre_topc(A_619) | v2_struct_0(A_619))), inference(superposition, [status(thm), theory('equality')], [c_2504, c_800])).
% 13.75/5.62  tff(c_5257, plain, (v1_funct_2(k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_4')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_5241])).
% 13.75/5.62  tff(c_5285, plain, (v1_funct_2(k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_4')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_356, c_46, c_5257])).
% 13.75/5.62  tff(c_5286, plain, (v1_funct_2(k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_4')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_64, c_5285])).
% 13.75/5.62  tff(c_502, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_494, c_14])).
% 13.75/5.62  tff(c_512, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_356, c_356, c_44, c_42, c_40, c_502])).
% 13.75/5.62  tff(c_513, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_512])).
% 13.75/5.62  tff(c_2537, plain, (![D_495, A_494]: (m1_subset_1(k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0(D_495)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_495), u1_struct_0('#skF_2')))) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1')) | ~m1_pre_topc(D_495, A_494) | ~m1_pre_topc('#skF_1', A_494) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_494) | ~v2_pre_topc(A_494) | v2_struct_0(A_494) | ~m1_pre_topc(D_495, '#skF_1') | ~m1_pre_topc(D_495, A_494) | ~m1_pre_topc('#skF_1', A_494) | ~l1_pre_topc(A_494) | ~v2_pre_topc(A_494) | v2_struct_0(A_494))), inference(superposition, [status(thm), theory('equality')], [c_2504, c_14])).
% 13.75/5.62  tff(c_2567, plain, (![D_495, A_494]: (m1_subset_1(k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0(D_495)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_495), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2') | ~m1_pre_topc(D_495, '#skF_1') | ~m1_pre_topc(D_495, A_494) | ~m1_pre_topc('#skF_1', A_494) | ~l1_pre_topc(A_494) | ~v2_pre_topc(A_494) | v2_struct_0(A_494))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_519, c_516, c_513, c_2537])).
% 13.75/5.62  tff(c_2616, plain, (![D_497, A_498]: (m1_subset_1(k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0(D_497)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_497), u1_struct_0('#skF_2')))) | ~m1_pre_topc(D_497, '#skF_1') | ~m1_pre_topc(D_497, A_498) | ~m1_pre_topc('#skF_1', A_498) | ~l1_pre_topc(A_498) | ~v2_pre_topc(A_498) | v2_struct_0(A_498))), inference(negUnitSimplification, [status(thm)], [c_58, c_2567])).
% 13.75/5.62  tff(c_2632, plain, (m1_subset_1(k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_2616])).
% 13.75/5.62  tff(c_2660, plain, (m1_subset_1(k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_356, c_46, c_2632])).
% 13.75/5.62  tff(c_2661, plain, (m1_subset_1(k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_2660])).
% 13.75/5.62  tff(c_2167, plain, (![A_479, D_481]: (k3_tmap_1(A_479, '#skF_2', '#skF_1', D_481, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'))=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0(D_481)) | ~m1_pre_topc(D_481, '#skF_1') | ~m1_pre_topc(D_481, A_479) | ~m1_pre_topc('#skF_1', A_479) | ~l1_pre_topc(A_479) | ~v2_pre_topc(A_479) | v2_struct_0(A_479))), inference(negUnitSimplification, [status(thm)], [c_64, c_2166])).
% 13.75/5.62  tff(c_7753, plain, (![A_739, D_738, A_737]: (k3_tmap_1(A_739, '#skF_2', '#skF_1', D_738, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'))=k3_tmap_1(A_737, '#skF_2', '#skF_1', D_738, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1')) | ~m1_pre_topc(D_738, '#skF_1') | ~m1_pre_topc(D_738, A_737) | ~m1_pre_topc('#skF_1', A_737) | ~l1_pre_topc(A_737) | ~v2_pre_topc(A_737) | v2_struct_0(A_737) | ~m1_pre_topc(D_738, '#skF_1') | ~m1_pre_topc(D_738, A_739) | ~m1_pre_topc('#skF_1', A_739) | ~l1_pre_topc(A_739) | ~v2_pre_topc(A_739) | v2_struct_0(A_739))), inference(superposition, [status(thm), theory('equality')], [c_2167, c_2504])).
% 13.75/5.62  tff(c_2, plain, (![A_1, B_2, D_4]: (r2_funct_2(A_1, B_2, D_4, D_4) | ~m1_subset_1(D_4, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(D_4, A_1, B_2) | ~v1_funct_1(D_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.75/5.62  tff(c_562, plain, (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1')) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'))), inference(resolution, [status(thm)], [c_513, c_2])).
% 13.75/5.62  tff(c_585, plain, (r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_519, c_516, c_562])).
% 13.75/5.62  tff(c_24, plain, (![F_188, D_182, E_186, A_126, C_174, B_158]: (r2_funct_2(u1_struct_0(D_182), u1_struct_0(B_158), k3_tmap_1(A_126, B_158, C_174, D_182, F_188), k2_tmap_1(A_126, B_158, E_186, D_182)) | ~m1_pre_topc(D_182, C_174) | ~r2_funct_2(u1_struct_0(C_174), u1_struct_0(B_158), F_188, k2_tmap_1(A_126, B_158, E_186, C_174)) | ~m1_subset_1(F_188, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_174), u1_struct_0(B_158)))) | ~v1_funct_2(F_188, u1_struct_0(C_174), u1_struct_0(B_158)) | ~v1_funct_1(F_188) | ~m1_subset_1(E_186, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_126), u1_struct_0(B_158)))) | ~v1_funct_2(E_186, u1_struct_0(A_126), u1_struct_0(B_158)) | ~v1_funct_1(E_186) | ~m1_pre_topc(D_182, A_126) | v2_struct_0(D_182) | ~m1_pre_topc(C_174, A_126) | v2_struct_0(C_174) | ~l1_pre_topc(B_158) | ~v2_pre_topc(B_158) | v2_struct_0(B_158) | ~l1_pre_topc(A_126) | ~v2_pre_topc(A_126) | v2_struct_0(A_126))), inference(cnfTransformation, [status(thm)], [f_237])).
% 13.75/5.62  tff(c_617, plain, (![D_182]: (r2_funct_2(u1_struct_0(D_182), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', D_182, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_182)) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_182, '#skF_1') | v2_struct_0(D_182) | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_585, c_24])).
% 13.75/5.62  tff(c_622, plain, (![D_182]: (r2_funct_2(u1_struct_0(D_182), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', D_182, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_182)) | ~m1_pre_topc(D_182, '#skF_1') | v2_struct_0(D_182) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_356, c_44, c_42, c_40, c_519, c_516, c_513, c_617])).
% 13.75/5.62  tff(c_623, plain, (![D_182]: (r2_funct_2(u1_struct_0(D_182), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', D_182, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_182)) | ~m1_pre_topc(D_182, '#skF_1') | v2_struct_0(D_182))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_622])).
% 13.75/5.62  tff(c_7877, plain, (![D_738, A_739]: (r2_funct_2(u1_struct_0(D_738), u1_struct_0('#skF_2'), k3_tmap_1(A_739, '#skF_2', '#skF_1', D_738, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_738)) | ~m1_pre_topc(D_738, '#skF_1') | v2_struct_0(D_738) | ~m1_pre_topc(D_738, '#skF_1') | ~m1_pre_topc(D_738, '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~m1_pre_topc(D_738, '#skF_1') | ~m1_pre_topc(D_738, A_739) | ~m1_pre_topc('#skF_1', A_739) | ~l1_pre_topc(A_739) | ~v2_pre_topc(A_739) | v2_struct_0(A_739))), inference(superposition, [status(thm), theory('equality')], [c_7753, c_623])).
% 13.75/5.62  tff(c_8001, plain, (![D_738, A_739]: (r2_funct_2(u1_struct_0(D_738), u1_struct_0('#skF_2'), k3_tmap_1(A_739, '#skF_2', '#skF_1', D_738, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_738)) | v2_struct_0(D_738) | v2_struct_0('#skF_1') | ~m1_pre_topc(D_738, '#skF_1') | ~m1_pre_topc(D_738, A_739) | ~m1_pre_topc('#skF_1', A_739) | ~l1_pre_topc(A_739) | ~v2_pre_topc(A_739) | v2_struct_0(A_739))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_356, c_7877])).
% 13.75/5.62  tff(c_8036, plain, (![D_740, A_741]: (r2_funct_2(u1_struct_0(D_740), u1_struct_0('#skF_2'), k3_tmap_1(A_741, '#skF_2', '#skF_1', D_740, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_740)) | v2_struct_0(D_740) | ~m1_pre_topc(D_740, '#skF_1') | ~m1_pre_topc(D_740, A_741) | ~m1_pre_topc('#skF_1', A_741) | ~l1_pre_topc(A_741) | ~v2_pre_topc(A_741) | v2_struct_0(A_741))), inference(negUnitSimplification, [status(thm)], [c_64, c_8001])).
% 13.75/5.62  tff(c_10865, plain, (![D_868, A_869]: (r2_funct_2(u1_struct_0(D_868), u1_struct_0('#skF_2'), k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0(D_868)), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_868)) | v2_struct_0(D_868) | ~m1_pre_topc(D_868, '#skF_1') | ~m1_pre_topc(D_868, A_869) | ~m1_pre_topc('#skF_1', A_869) | ~l1_pre_topc(A_869) | ~v2_pre_topc(A_869) | v2_struct_0(A_869) | ~m1_pre_topc(D_868, '#skF_1') | ~m1_pre_topc(D_868, A_869) | ~m1_pre_topc('#skF_1', A_869) | ~l1_pre_topc(A_869) | ~v2_pre_topc(A_869) | v2_struct_0(A_869))), inference(superposition, [status(thm), theory('equality')], [c_2167, c_8036])).
% 13.75/5.62  tff(c_10881, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_4')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_10865])).
% 13.75/5.62  tff(c_10911, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_4')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_356, c_46, c_10881])).
% 13.75/5.62  tff(c_10912, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_4')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_64, c_48, c_10911])).
% 13.75/5.62  tff(c_4, plain, (![D_4, C_3, A_1, B_2]: (D_4=C_3 | ~r2_funct_2(A_1, B_2, C_3, D_4) | ~m1_subset_1(D_4, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(D_4, A_1, B_2) | ~v1_funct_1(D_4) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(C_3, A_1, B_2) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.75/5.62  tff(c_11279, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_4'))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4') | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_4')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_10912, c_4])).
% 13.75/5.62  tff(c_11295, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_4'))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4351, c_5286, c_2661, c_430, c_427, c_424, c_11279])).
% 13.75/5.62  tff(c_333, plain, (![A_62]: (k3_tmap_1(A_62, '#skF_2', '#skF_1', A_62, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(A_62)) | ~m1_pre_topc(A_62, '#skF_1') | ~m1_pre_topc('#skF_1', A_62) | ~v2_pre_topc(A_62) | v2_struct_0(A_62) | ~l1_pre_topc(A_62))), inference(resolution, [status(thm)], [c_20, c_314])).
% 13.75/5.62  tff(c_1460, plain, (![D_464, A_465, D_466]: (k2_partfun1(u1_struct_0(D_464), u1_struct_0('#skF_2'), k3_tmap_1(A_465, '#skF_2', '#skF_1', D_464, '#skF_5'), u1_struct_0(D_466))=k2_tmap_1(D_464, '#skF_2', k3_tmap_1(A_465, '#skF_2', '#skF_1', D_464, '#skF_5'), D_466) | ~m1_pre_topc(D_466, D_464) | ~v1_funct_2(k3_tmap_1(A_465, '#skF_2', '#skF_1', D_464, '#skF_5'), u1_struct_0(D_464), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_465, '#skF_2', '#skF_1', D_464, '#skF_5')) | ~l1_pre_topc(D_464) | ~v2_pre_topc(D_464) | v2_struct_0(D_464) | ~m1_pre_topc(D_464, A_465) | ~m1_pre_topc('#skF_1', A_465) | ~l1_pre_topc(A_465) | ~v2_pre_topc(A_465) | v2_struct_0(A_465))), inference(negUnitSimplification, [status(thm)], [c_58, c_870])).
% 13.75/5.62  tff(c_5229, plain, (![A_616, D_617]: (k2_tmap_1(A_616, '#skF_2', k3_tmap_1(A_616, '#skF_2', '#skF_1', A_616, '#skF_5'), D_617)=k2_partfun1(u1_struct_0(A_616), u1_struct_0('#skF_2'), k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(A_616)), u1_struct_0(D_617)) | ~m1_pre_topc(D_617, A_616) | ~v1_funct_2(k3_tmap_1(A_616, '#skF_2', '#skF_1', A_616, '#skF_5'), u1_struct_0(A_616), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_616, '#skF_2', '#skF_1', A_616, '#skF_5')) | ~l1_pre_topc(A_616) | ~v2_pre_topc(A_616) | v2_struct_0(A_616) | ~m1_pre_topc(A_616, A_616) | ~m1_pre_topc('#skF_1', A_616) | ~l1_pre_topc(A_616) | ~v2_pre_topc(A_616) | v2_struct_0(A_616) | ~m1_pre_topc(A_616, '#skF_1') | ~m1_pre_topc('#skF_1', A_616) | ~v2_pre_topc(A_616) | v2_struct_0(A_616) | ~l1_pre_topc(A_616))), inference(superposition, [status(thm), theory('equality')], [c_333, c_1460])).
% 13.75/5.62  tff(c_6290, plain, (![D_681, D_682]: (k2_tmap_1(D_681, '#skF_2', k3_tmap_1(D_681, '#skF_2', '#skF_1', D_681, '#skF_5'), D_682)=k2_partfun1(u1_struct_0(D_681), u1_struct_0('#skF_2'), k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_681)), u1_struct_0(D_682)) | ~m1_pre_topc(D_682, D_681) | ~v1_funct_1(k3_tmap_1(D_681, '#skF_2', '#skF_1', D_681, '#skF_5')) | ~m1_pre_topc(D_681, '#skF_1') | ~m1_pre_topc(D_681, D_681) | ~m1_pre_topc('#skF_1', D_681) | ~l1_pre_topc(D_681) | ~v2_pre_topc(D_681) | v2_struct_0(D_681))), inference(resolution, [status(thm)], [c_270, c_5229])).
% 13.75/5.62  tff(c_6325, plain, (![D_348, D_682]: (k2_tmap_1(D_348, '#skF_2', k3_tmap_1(D_348, '#skF_2', '#skF_1', D_348, '#skF_5'), D_682)=k2_partfun1(u1_struct_0(D_348), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_348), u1_struct_0(D_682)) | ~m1_pre_topc(D_682, D_348) | ~v1_funct_1(k3_tmap_1(D_348, '#skF_2', '#skF_1', D_348, '#skF_5')) | ~m1_pre_topc(D_348, '#skF_1') | ~m1_pre_topc(D_348, D_348) | ~m1_pre_topc('#skF_1', D_348) | ~l1_pre_topc(D_348) | ~v2_pre_topc(D_348) | v2_struct_0(D_348) | ~m1_pre_topc(D_348, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_254, c_6290])).
% 13.75/5.62  tff(c_11317, plain, (k2_tmap_1('#skF_1', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_5'), '#skF_4')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_5')) | ~m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_11295, c_6325])).
% 13.75/5.62  tff(c_11345, plain, (k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), '#skF_4')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_356, c_62, c_60, c_356, c_356, c_356, c_519, c_494, c_46, c_494, c_11317])).
% 13.75/5.62  tff(c_11346, plain, (k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), '#skF_4')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_64, c_11345])).
% 13.75/5.62  tff(c_4324, plain, (v1_funct_1(k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_4306])).
% 13.75/5.62  tff(c_4354, plain, (v1_funct_1(k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_3'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_356, c_50, c_4324])).
% 13.75/5.62  tff(c_4355, plain, (v1_funct_1(k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_64, c_4354])).
% 13.75/5.62  tff(c_5259, plain, (v1_funct_2(k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_5241])).
% 13.75/5.62  tff(c_5289, plain, (v1_funct_2(k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_356, c_50, c_5259])).
% 13.75/5.62  tff(c_5290, plain, (v1_funct_2(k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_64, c_5289])).
% 13.75/5.62  tff(c_2634, plain, (m1_subset_1(k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_2616])).
% 13.75/5.62  tff(c_2664, plain, (m1_subset_1(k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_356, c_50, c_2634])).
% 13.75/5.62  tff(c_2665, plain, (m1_subset_1(k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_2664])).
% 13.75/5.62  tff(c_10883, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_3')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_10865])).
% 13.75/5.62  tff(c_10915, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_3')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_356, c_50, c_10883])).
% 13.75/5.62  tff(c_10916, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_3')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_64, c_52, c_10915])).
% 13.75/5.62  tff(c_11103, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_3'))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3') | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~m1_subset_1(k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_10916, c_4])).
% 13.75/5.62  tff(c_11119, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_3'))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4355, c_5290, c_2665, c_699, c_696, c_693, c_11103])).
% 13.75/5.62  tff(c_11141, plain, (k2_tmap_1('#skF_1', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_5'), '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_1', '#skF_5')) | ~m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_11119, c_6325])).
% 13.75/5.62  tff(c_11169, plain, (k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_356, c_62, c_60, c_356, c_356, c_356, c_519, c_494, c_50, c_494, c_11141])).
% 13.75/5.62  tff(c_11170, plain, (k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_64, c_11169])).
% 13.75/5.62  tff(c_558, plain, (![D_25]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0(D_25))=k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), D_25) | ~m1_pre_topc(D_25, '#skF_1') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_513, c_10])).
% 13.75/5.62  tff(c_577, plain, (![D_25]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0(D_25))=k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), D_25) | ~m1_pre_topc(D_25, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_519, c_516, c_558])).
% 13.75/5.62  tff(c_578, plain, (![D_25]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0(D_25))=k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), D_25) | ~m1_pre_topc(D_25, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_577])).
% 13.75/5.62  tff(c_4371, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_578, c_4351])).
% 13.75/5.62  tff(c_4375, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_4371])).
% 13.75/5.62  tff(c_5306, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_578, c_5286])).
% 13.75/5.62  tff(c_5310, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_5306])).
% 13.75/5.62  tff(c_2787, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~m1_pre_topc('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_578, c_2661])).
% 13.75/5.62  tff(c_2820, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2787])).
% 13.75/5.62  tff(c_2928, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), '#skF_4'), k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), '#skF_4')) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), '#skF_4'))), inference(resolution, [status(thm)], [c_2820, c_2])).
% 13.75/5.62  tff(c_5781, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), '#skF_4'), k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4375, c_5310, c_2928])).
% 13.75/5.62  tff(c_5783, plain, (![D_182]: (r2_funct_2(u1_struct_0(D_182), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', D_182, k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), '#skF_4')), k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), D_182)) | ~m1_pre_topc(D_182, '#skF_4') | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), '#skF_4')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1')) | ~m1_pre_topc(D_182, '#skF_1') | v2_struct_0(D_182) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_5781, c_24])).
% 13.75/5.62  tff(c_5788, plain, (![D_182]: (r2_funct_2(u1_struct_0(D_182), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', D_182, k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), '#skF_4')), k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), D_182)) | ~m1_pre_topc(D_182, '#skF_4') | ~m1_pre_topc(D_182, '#skF_1') | v2_struct_0(D_182) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_46, c_519, c_516, c_513, c_4375, c_5310, c_2820, c_5783])).
% 13.75/5.62  tff(c_5789, plain, (![D_182]: (r2_funct_2(u1_struct_0(D_182), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', D_182, k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), '#skF_4')), k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), D_182)) | ~m1_pre_topc(D_182, '#skF_4') | ~m1_pre_topc(D_182, '#skF_1') | v2_struct_0(D_182))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_48, c_5788])).
% 13.75/5.62  tff(c_11208, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), '#skF_4')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_11170, c_5789])).
% 13.75/5.62  tff(c_11229, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), '#skF_4')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_38, c_11208])).
% 13.75/5.62  tff(c_11230, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_1'), '#skF_4')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_11229])).
% 13.75/5.62  tff(c_11445, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_11346, c_11230])).
% 13.75/5.62  tff(c_11458, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6804, c_11445])).
% 13.75/5.62  tff(c_11473, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_46, c_50, c_38, c_11458])).
% 13.75/5.62  tff(c_11474, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_64, c_11473])).
% 13.75/5.62  tff(c_11479, plain, (k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3') | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_3'))), inference(resolution, [status(thm)], [c_11474, c_4])).
% 13.75/5.62  tff(c_11486, plain, (k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_3')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4573, c_5040, c_1544, c_699, c_696, c_693, c_11479])).
% 13.75/5.62  tff(c_295, plain, (![C_371, A_370, B_369, F_368, D_367]: (r1_tmap_1(D_367, A_370, k2_tmap_1(B_369, A_370, C_371, D_367), F_368) | ~r1_tmap_1(B_369, A_370, C_371, F_368) | ~m1_subset_1(F_368, u1_struct_0(D_367)) | ~m1_subset_1(F_368, u1_struct_0(B_369)) | ~m1_pre_topc(D_367, B_369) | v2_struct_0(D_367) | ~m1_subset_1(C_371, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_369), u1_struct_0(A_370)))) | ~v1_funct_2(C_371, u1_struct_0(B_369), u1_struct_0(A_370)) | ~v1_funct_1(C_371) | ~l1_pre_topc(B_369) | ~v2_pre_topc(B_369) | v2_struct_0(B_369) | ~l1_pre_topc(A_370) | ~v2_pre_topc(A_370) | v2_struct_0(A_370))), inference(cnfTransformation, [status(thm)], [f_190])).
% 13.75/5.62  tff(c_1194, plain, (![C_443, D_439, A_441, D_442, B_437, E_438, F_440]: (r1_tmap_1(D_439, B_437, k2_tmap_1(D_442, B_437, k3_tmap_1(A_441, B_437, C_443, D_442, E_438), D_439), F_440) | ~r1_tmap_1(D_442, B_437, k3_tmap_1(A_441, B_437, C_443, D_442, E_438), F_440) | ~m1_subset_1(F_440, u1_struct_0(D_439)) | ~m1_subset_1(F_440, u1_struct_0(D_442)) | ~m1_pre_topc(D_439, D_442) | v2_struct_0(D_439) | ~v1_funct_2(k3_tmap_1(A_441, B_437, C_443, D_442, E_438), u1_struct_0(D_442), u1_struct_0(B_437)) | ~v1_funct_1(k3_tmap_1(A_441, B_437, C_443, D_442, E_438)) | ~l1_pre_topc(D_442) | ~v2_pre_topc(D_442) | v2_struct_0(D_442) | ~m1_subset_1(E_438, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_443), u1_struct_0(B_437)))) | ~v1_funct_2(E_438, u1_struct_0(C_443), u1_struct_0(B_437)) | ~v1_funct_1(E_438) | ~m1_pre_topc(D_442, A_441) | ~m1_pre_topc(C_443, A_441) | ~l1_pre_topc(B_437) | ~v2_pre_topc(B_437) | v2_struct_0(B_437) | ~l1_pre_topc(A_441) | ~v2_pre_topc(A_441) | v2_struct_0(A_441))), inference(resolution, [status(thm)], [c_14, c_295])).
% 13.75/5.62  tff(c_1210, plain, (![D_439, F_440]: (r1_tmap_1(D_439, '#skF_2', k2_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5'), D_439), F_440) | ~r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5'), F_440) | ~m1_subset_1(F_440, u1_struct_0(D_439)) | ~m1_subset_1(F_440, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_439, '#skF_4') | v2_struct_0(D_439) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_405, c_1194])).
% 13.75/5.62  tff(c_1236, plain, (![D_439, F_440]: (r1_tmap_1(D_439, '#skF_2', k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), D_439), F_440) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), F_440) | ~m1_subset_1(F_440, u1_struct_0(D_439)) | ~m1_subset_1(F_440, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_439, '#skF_4') | v2_struct_0(D_439) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_356, c_46, c_44, c_42, c_40, c_114, c_89, c_430, c_405, c_427, c_405, c_405, c_1210])).
% 13.75/5.62  tff(c_1237, plain, (![D_439, F_440]: (r1_tmap_1(D_439, '#skF_2', k2_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), D_439), F_440) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), F_440) | ~m1_subset_1(F_440, u1_struct_0(D_439)) | ~m1_subset_1(F_440, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_439, '#skF_4') | v2_struct_0(D_439))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_48, c_1236])).
% 13.75/5.62  tff(c_11517, plain, (![F_440]: (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), F_440) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), F_440) | ~m1_subset_1(F_440, u1_struct_0('#skF_3')) | ~m1_subset_1(F_440, u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_11486, c_1237])).
% 13.75/5.62  tff(c_11538, plain, (![F_440]: (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), F_440) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), F_440) | ~m1_subset_1(F_440, u1_struct_0('#skF_3')) | ~m1_subset_1(F_440, u1_struct_0('#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_11517])).
% 13.75/5.62  tff(c_11762, plain, (![F_896]: (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), F_896) | ~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), F_896) | ~m1_subset_1(F_896, u1_struct_0('#skF_3')) | ~m1_subset_1(F_896, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_52, c_11538])).
% 13.75/5.62  tff(c_28, plain, (~r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_298])).
% 13.75/5.62  tff(c_66, plain, (~r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28])).
% 13.75/5.62  tff(c_11765, plain, (~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_11762, c_66])).
% 13.75/5.62  tff(c_11769, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_65, c_30, c_11765])).
% 13.75/5.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.75/5.62  
% 13.75/5.62  Inference rules
% 13.75/5.62  ----------------------
% 13.75/5.62  #Ref     : 0
% 13.75/5.62  #Sup     : 2241
% 13.75/5.62  #Fact    : 0
% 13.75/5.62  #Define  : 0
% 13.75/5.62  #Split   : 14
% 13.75/5.62  #Chain   : 0
% 13.75/5.62  #Close   : 0
% 13.75/5.62  
% 13.75/5.62  Ordering : KBO
% 13.75/5.62  
% 13.75/5.62  Simplification rules
% 13.75/5.62  ----------------------
% 13.75/5.62  #Subsume      : 938
% 13.75/5.62  #Demod        : 7068
% 13.75/5.62  #Tautology    : 443
% 13.75/5.62  #SimpNegUnit  : 1234
% 13.75/5.62  #BackRed      : 41
% 13.75/5.62  
% 13.75/5.62  #Partial instantiations: 0
% 13.75/5.62  #Strategies tried      : 1
% 13.75/5.62  
% 13.75/5.62  Timing (in seconds)
% 13.75/5.62  ----------------------
% 13.75/5.62  Preprocessing        : 0.40
% 13.75/5.62  Parsing              : 0.20
% 13.75/5.62  CNF conversion       : 0.05
% 13.75/5.62  Main loop            : 4.39
% 13.75/5.62  Inferencing          : 1.03
% 13.75/5.62  Reduction            : 1.69
% 13.75/5.62  Demodulation         : 1.40
% 13.75/5.62  BG Simplification    : 0.09
% 13.75/5.63  Subsumption          : 1.46
% 13.75/5.63  Abstraction          : 0.17
% 13.75/5.63  MUC search           : 0.00
% 13.75/5.63  Cooper               : 0.00
% 13.75/5.63  Total                : 4.89
% 13.75/5.63  Index Insertion      : 0.00
% 13.75/5.63  Index Deletion       : 0.00
% 13.75/5.63  Index Matching       : 0.00
% 13.75/5.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
