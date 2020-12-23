%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1812+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:27 EST 2020

% Result     : Theorem 11.43s
% Output     : CNFRefutation 11.43s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 605 expanded)
%              Number of leaves         :   37 ( 269 expanded)
%              Depth                    :   11
%              Number of atoms          :  669 (7041 expanded)
%              Number of equality atoms :   13 (  14 expanded)
%              Maximal formula depth    :   29 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > r4_tsep_1 > v1_tsep_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_1 > #skF_8 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_310,negated_conjecture,(
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
                  & v1_tsep_1(C,A)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & v1_tsep_1(D,A)
                      & m1_pre_topc(D,A) )
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
                            & m1_subset_1(k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_tmap_1)).

tff(f_247,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_tsep_1(B,A)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( v1_tsep_1(C,A)
                & m1_pre_topc(C,A) )
             => r4_tsep_1(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tsep_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => k1_tsep_1(A,B,C) = k1_tsep_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k1_tsep_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => ( ~ v2_struct_0(k1_tsep_1(A,B,C))
        & v1_pre_topc(k1_tsep_1(A,B,C))
        & m1_pre_topc(k1_tsep_1(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

tff(f_114,axiom,(
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

tff(f_221,axiom,(
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

tff(c_100,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_98,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_96,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_86,plain,(
    v1_tsep_1('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_84,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_80,plain,(
    v1_tsep_1('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_78,plain,(
    m1_pre_topc('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_70,plain,(
    ! [A_63,B_67,C_69] :
      ( r4_tsep_1(A_63,B_67,C_69)
      | ~ m1_pre_topc(C_69,A_63)
      | ~ v1_tsep_1(C_69,A_63)
      | ~ m1_pre_topc(B_67,A_63)
      | ~ v1_tsep_1(B_67,A_63)
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_94,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_88,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_82,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_92,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_90,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_3856,plain,(
    ! [A_262,C_263,B_264] :
      ( k1_tsep_1(A_262,C_263,B_264) = k1_tsep_1(A_262,B_264,C_263)
      | ~ m1_pre_topc(C_263,A_262)
      | v2_struct_0(C_263)
      | ~ m1_pre_topc(B_264,A_262)
      | v2_struct_0(B_264)
      | ~ l1_pre_topc(A_262)
      | v2_struct_0(A_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3864,plain,(
    ! [B_264] :
      ( k1_tsep_1('#skF_4',B_264,'#skF_7') = k1_tsep_1('#skF_4','#skF_7',B_264)
      | v2_struct_0('#skF_7')
      | ~ m1_pre_topc(B_264,'#skF_4')
      | v2_struct_0(B_264)
      | ~ l1_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_78,c_3856])).

tff(c_3872,plain,(
    ! [B_264] :
      ( k1_tsep_1('#skF_4',B_264,'#skF_7') = k1_tsep_1('#skF_4','#skF_7',B_264)
      | v2_struct_0('#skF_7')
      | ~ m1_pre_topc(B_264,'#skF_4')
      | v2_struct_0(B_264)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_3864])).

tff(c_3878,plain,(
    ! [B_265] :
      ( k1_tsep_1('#skF_4',B_265,'#skF_7') = k1_tsep_1('#skF_4','#skF_7',B_265)
      | ~ m1_pre_topc(B_265,'#skF_4')
      | v2_struct_0(B_265) ) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_82,c_3872])).

tff(c_3896,plain,
    ( k1_tsep_1('#skF_4','#skF_7','#skF_6') = k1_tsep_1('#skF_4','#skF_6','#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_84,c_3878])).

tff(c_3914,plain,(
    k1_tsep_1('#skF_4','#skF_7','#skF_6') = k1_tsep_1('#skF_4','#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_3896])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] :
      ( m1_pre_topc(k1_tsep_1(A_10,B_11,C_12),A_10)
      | ~ m1_pre_topc(C_12,A_10)
      | v2_struct_0(C_12)
      | ~ m1_pre_topc(B_11,A_10)
      | v2_struct_0(B_11)
      | ~ l1_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3924,plain,
    ( m1_pre_topc(k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_4')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | v2_struct_0('#skF_6')
    | ~ m1_pre_topc('#skF_7','#skF_4')
    | v2_struct_0('#skF_7')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3914,c_12])).

tff(c_3940,plain,
    ( m1_pre_topc(k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_4')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_7')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_78,c_84,c_3924])).

tff(c_3941,plain,(
    m1_pre_topc(k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_82,c_88,c_3940])).

tff(c_76,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_74,plain,(
    v1_funct_2('#skF_8',u1_struct_0(k1_tsep_1('#skF_4','#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_72,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_4','#skF_6','#skF_7')),u1_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_4227,plain,(
    ! [A_285,B_283,C_286,D_282,E_284] :
      ( m1_subset_1(k3_tmap_1(A_285,B_283,C_286,D_282,E_284),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_282),u1_struct_0(B_283))))
      | ~ m1_subset_1(E_284,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_286),u1_struct_0(B_283))))
      | ~ v1_funct_2(E_284,u1_struct_0(C_286),u1_struct_0(B_283))
      | ~ v1_funct_1(E_284)
      | ~ m1_pre_topc(D_282,A_285)
      | ~ m1_pre_topc(C_286,A_285)
      | ~ l1_pre_topc(B_283)
      | ~ v2_pre_topc(B_283)
      | v2_struct_0(B_283)
      | ~ l1_pre_topc(A_285)
      | ~ v2_pre_topc(A_285)
      | v2_struct_0(A_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_338,plain,(
    ! [A_143,C_144,B_145] :
      ( k1_tsep_1(A_143,C_144,B_145) = k1_tsep_1(A_143,B_145,C_144)
      | ~ m1_pre_topc(C_144,A_143)
      | v2_struct_0(C_144)
      | ~ m1_pre_topc(B_145,A_143)
      | v2_struct_0(B_145)
      | ~ l1_pre_topc(A_143)
      | v2_struct_0(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_346,plain,(
    ! [B_145] :
      ( k1_tsep_1('#skF_4',B_145,'#skF_7') = k1_tsep_1('#skF_4','#skF_7',B_145)
      | v2_struct_0('#skF_7')
      | ~ m1_pre_topc(B_145,'#skF_4')
      | v2_struct_0(B_145)
      | ~ l1_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_78,c_338])).

tff(c_354,plain,(
    ! [B_145] :
      ( k1_tsep_1('#skF_4',B_145,'#skF_7') = k1_tsep_1('#skF_4','#skF_7',B_145)
      | v2_struct_0('#skF_7')
      | ~ m1_pre_topc(B_145,'#skF_4')
      | v2_struct_0(B_145)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_346])).

tff(c_3500,plain,(
    ! [B_242] :
      ( k1_tsep_1('#skF_4',B_242,'#skF_7') = k1_tsep_1('#skF_4','#skF_7',B_242)
      | ~ m1_pre_topc(B_242,'#skF_4')
      | v2_struct_0(B_242) ) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_82,c_354])).

tff(c_3518,plain,
    ( k1_tsep_1('#skF_4','#skF_7','#skF_6') = k1_tsep_1('#skF_4','#skF_6','#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_84,c_3500])).

tff(c_3536,plain,(
    k1_tsep_1('#skF_4','#skF_7','#skF_6') = k1_tsep_1('#skF_4','#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_3518])).

tff(c_3546,plain,
    ( m1_pre_topc(k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_4')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | v2_struct_0('#skF_6')
    | ~ m1_pre_topc('#skF_7','#skF_4')
    | v2_struct_0('#skF_7')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3536,c_12])).

tff(c_3562,plain,
    ( m1_pre_topc(k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_4')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_7')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_78,c_84,c_3546])).

tff(c_3563,plain,(
    m1_pre_topc(k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_82,c_88,c_3562])).

tff(c_3832,plain,(
    ! [E_256,D_254,A_257,B_255,C_258] :
      ( m1_subset_1(k3_tmap_1(A_257,B_255,C_258,D_254,E_256),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_254),u1_struct_0(B_255))))
      | ~ m1_subset_1(E_256,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_258),u1_struct_0(B_255))))
      | ~ v1_funct_2(E_256,u1_struct_0(C_258),u1_struct_0(B_255))
      | ~ v1_funct_1(E_256)
      | ~ m1_pre_topc(D_254,A_257)
      | ~ m1_pre_topc(C_258,A_257)
      | ~ l1_pre_topc(B_255)
      | ~ v2_pre_topc(B_255)
      | v2_struct_0(B_255)
      | ~ l1_pre_topc(A_257)
      | ~ v2_pre_topc(A_257)
      | v2_struct_0(A_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_186,plain,
    ( v5_pre_topc('#skF_8',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_5')
    | v1_funct_1(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_308,plain,(
    v1_funct_1(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_176,plain,
    ( v5_pre_topc('#skF_8',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_5')
    | v1_funct_2(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_6','#skF_8'),u1_struct_0('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_326,plain,(
    v1_funct_2(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_6','#skF_8'),u1_struct_0('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_166,plain,
    ( v5_pre_topc('#skF_8',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_5')
    | v5_pre_topc(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_6','#skF_8'),'#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_314,plain,(
    v5_pre_topc(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_6','#skF_8'),'#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_156,plain,
    ( v5_pre_topc('#skF_8',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_5')
    | m1_subset_1(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_6','#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_329,plain,(
    m1_subset_1(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_6','#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5')))) ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_146,plain,
    ( v5_pre_topc('#skF_8',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_5')
    | v1_funct_1(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_311,plain,(
    v1_funct_1(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_136,plain,
    ( v5_pre_topc('#skF_8',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_5')
    | v1_funct_2(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_7','#skF_8'),u1_struct_0('#skF_7'),u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_327,plain,(
    v1_funct_2(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_7','#skF_8'),u1_struct_0('#skF_7'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_126,plain,
    ( v5_pre_topc('#skF_8',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_5')
    | v5_pre_topc(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_7','#skF_8'),'#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_313,plain,(
    v5_pre_topc(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_7','#skF_8'),'#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_116,plain,
    ( v5_pre_topc('#skF_8',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_5')
    | m1_subset_1(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_360,plain,(
    m1_subset_1(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_5')))) ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_102,plain,
    ( ~ m1_subset_1(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_5'))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_7','#skF_8'),'#skF_7','#skF_5')
    | ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_7','#skF_8'),u1_struct_0('#skF_7'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_7','#skF_8'))
    | ~ m1_subset_1(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_6','#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_6','#skF_8'),'#skF_6','#skF_5')
    | ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_6','#skF_8'),u1_struct_0('#skF_6'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_6','#skF_8'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_4','#skF_6','#skF_7')),u1_struct_0('#skF_5'))))
    | ~ v5_pre_topc('#skF_8',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_5')
    | ~ v1_funct_2('#skF_8',u1_struct_0(k1_tsep_1('#skF_4','#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_199,plain,
    ( ~ m1_subset_1(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_5'))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_7','#skF_8'),'#skF_7','#skF_5')
    | ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_7','#skF_8'),u1_struct_0('#skF_7'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_7','#skF_8'))
    | ~ m1_subset_1(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_6','#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_6','#skF_8'),'#skF_6','#skF_5')
    | ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_6','#skF_8'),u1_struct_0('#skF_6'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_6','#skF_8'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_4','#skF_6','#skF_7')),u1_struct_0('#skF_5'))))
    | ~ v5_pre_topc('#skF_8',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_5')
    | ~ v1_funct_2('#skF_8',u1_struct_0(k1_tsep_1('#skF_4','#skF_6','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_102])).

tff(c_210,plain,
    ( ~ m1_subset_1(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_5'))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_7','#skF_8'),'#skF_7','#skF_5')
    | ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_7','#skF_8'),u1_struct_0('#skF_7'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_7','#skF_8'))
    | ~ m1_subset_1(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_6','#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_6','#skF_8'),'#skF_6','#skF_5')
    | ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_6','#skF_8'),u1_struct_0('#skF_6'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_6','#skF_8'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_4','#skF_6','#skF_7')),u1_struct_0('#skF_5'))))
    | ~ v5_pre_topc('#skF_8',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_199])).

tff(c_220,plain,
    ( ~ m1_subset_1(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_5'))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_7','#skF_8'),'#skF_7','#skF_5')
    | ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_7','#skF_8'),u1_struct_0('#skF_7'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_7','#skF_8'))
    | ~ m1_subset_1(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_6','#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_6','#skF_8'),'#skF_6','#skF_5')
    | ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_6','#skF_8'),u1_struct_0('#skF_6'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_6','#skF_8'))
    | ~ v5_pre_topc('#skF_8',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_210])).

tff(c_3014,plain,(
    ~ v5_pre_topc('#skF_8',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_326,c_314,c_329,c_311,c_327,c_313,c_360,c_220])).

tff(c_3387,plain,(
    ! [E_241,C_237,B_239,D_240,A_238] :
      ( v5_pre_topc(E_241,k1_tsep_1(A_238,C_237,D_240),B_239)
      | ~ m1_subset_1(k3_tmap_1(A_238,B_239,k1_tsep_1(A_238,C_237,D_240),D_240,E_241),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_240),u1_struct_0(B_239))))
      | ~ v5_pre_topc(k3_tmap_1(A_238,B_239,k1_tsep_1(A_238,C_237,D_240),D_240,E_241),D_240,B_239)
      | ~ v1_funct_2(k3_tmap_1(A_238,B_239,k1_tsep_1(A_238,C_237,D_240),D_240,E_241),u1_struct_0(D_240),u1_struct_0(B_239))
      | ~ v1_funct_1(k3_tmap_1(A_238,B_239,k1_tsep_1(A_238,C_237,D_240),D_240,E_241))
      | ~ m1_subset_1(k3_tmap_1(A_238,B_239,k1_tsep_1(A_238,C_237,D_240),C_237,E_241),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_237),u1_struct_0(B_239))))
      | ~ v5_pre_topc(k3_tmap_1(A_238,B_239,k1_tsep_1(A_238,C_237,D_240),C_237,E_241),C_237,B_239)
      | ~ v1_funct_2(k3_tmap_1(A_238,B_239,k1_tsep_1(A_238,C_237,D_240),C_237,E_241),u1_struct_0(C_237),u1_struct_0(B_239))
      | ~ v1_funct_1(k3_tmap_1(A_238,B_239,k1_tsep_1(A_238,C_237,D_240),C_237,E_241))
      | ~ m1_subset_1(E_241,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_238,C_237,D_240)),u1_struct_0(B_239))))
      | ~ v1_funct_2(E_241,u1_struct_0(k1_tsep_1(A_238,C_237,D_240)),u1_struct_0(B_239))
      | ~ v1_funct_1(E_241)
      | ~ r4_tsep_1(A_238,C_237,D_240)
      | ~ m1_pre_topc(D_240,A_238)
      | v2_struct_0(D_240)
      | ~ m1_pre_topc(C_237,A_238)
      | v2_struct_0(C_237)
      | ~ l1_pre_topc(B_239)
      | ~ v2_pre_topc(B_239)
      | v2_struct_0(B_239)
      | ~ l1_pre_topc(A_238)
      | ~ v2_pre_topc(A_238)
      | v2_struct_0(A_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_3427,plain,
    ( v5_pre_topc('#skF_8',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_5')
    | ~ v5_pre_topc(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_7','#skF_8'),'#skF_7','#skF_5')
    | ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_7','#skF_8'),u1_struct_0('#skF_7'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_7','#skF_8'))
    | ~ m1_subset_1(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_6','#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5'))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_6','#skF_8'),'#skF_6','#skF_5')
    | ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_6','#skF_8'),u1_struct_0('#skF_6'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_6','#skF_8'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_4','#skF_6','#skF_7')),u1_struct_0('#skF_5'))))
    | ~ v1_funct_2('#skF_8',u1_struct_0(k1_tsep_1('#skF_4','#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_8')
    | ~ r4_tsep_1('#skF_4','#skF_6','#skF_7')
    | ~ m1_pre_topc('#skF_7','#skF_4')
    | v2_struct_0('#skF_7')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | v2_struct_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_360,c_3387])).

tff(c_3482,plain,
    ( v5_pre_topc('#skF_8',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_5')
    | ~ r4_tsep_1('#skF_4','#skF_6','#skF_7')
    | v2_struct_0('#skF_7')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_92,c_90,c_84,c_78,c_76,c_74,c_72,c_308,c_326,c_314,c_329,c_311,c_327,c_313,c_3427])).

tff(c_3483,plain,(
    ~ r4_tsep_1('#skF_4','#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_94,c_88,c_82,c_3014,c_3482])).

tff(c_3492,plain,
    ( ~ m1_pre_topc('#skF_7','#skF_4')
    | ~ v1_tsep_1('#skF_7','#skF_4')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ v1_tsep_1('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_3483])).

tff(c_3495,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_86,c_84,c_80,c_78,c_3492])).

tff(c_3497,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_3495])).

tff(c_3499,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_7','#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_5')))) ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_3839,plain,
    ( ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_4','#skF_6','#skF_7')),u1_struct_0('#skF_5'))))
    | ~ v1_funct_2('#skF_8',u1_struct_0(k1_tsep_1('#skF_4','#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_8')
    | ~ m1_pre_topc('#skF_7','#skF_4')
    | ~ m1_pre_topc(k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_4')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_3832,c_3499])).

tff(c_3846,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_92,c_90,c_3563,c_78,c_76,c_74,c_72,c_3839])).

tff(c_3848,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_94,c_3846])).

tff(c_3850,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_6','#skF_8'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5')))) ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_4234,plain,
    ( ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_4','#skF_6','#skF_7')),u1_struct_0('#skF_5'))))
    | ~ v1_funct_2('#skF_8',u1_struct_0(k1_tsep_1('#skF_4','#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_8')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ m1_pre_topc(k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_4')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4227,c_3850])).

tff(c_4241,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_92,c_90,c_3941,c_84,c_76,c_74,c_72,c_4234])).

tff(c_4243,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_94,c_4241])).

tff(c_4245,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_7','#skF_8'),u1_struct_0('#skF_7'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_4244,plain,(
    v5_pre_topc('#skF_8',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_5593,plain,(
    ! [C_345,D_348,A_346,B_347,E_349] :
      ( v1_funct_2(k3_tmap_1(A_346,B_347,k1_tsep_1(A_346,C_345,D_348),D_348,E_349),u1_struct_0(D_348),u1_struct_0(B_347))
      | ~ v5_pre_topc(E_349,k1_tsep_1(A_346,C_345,D_348),B_347)
      | ~ m1_subset_1(E_349,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_346,C_345,D_348)),u1_struct_0(B_347))))
      | ~ v1_funct_2(E_349,u1_struct_0(k1_tsep_1(A_346,C_345,D_348)),u1_struct_0(B_347))
      | ~ v1_funct_1(E_349)
      | ~ r4_tsep_1(A_346,C_345,D_348)
      | ~ m1_pre_topc(D_348,A_346)
      | v2_struct_0(D_348)
      | ~ m1_pre_topc(C_345,A_346)
      | v2_struct_0(C_345)
      | ~ l1_pre_topc(B_347)
      | ~ v2_pre_topc(B_347)
      | v2_struct_0(B_347)
      | ~ l1_pre_topc(A_346)
      | ~ v2_pre_topc(A_346)
      | v2_struct_0(A_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_5620,plain,
    ( v1_funct_2(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_7','#skF_8'),u1_struct_0('#skF_7'),u1_struct_0('#skF_5'))
    | ~ v5_pre_topc('#skF_8',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_5')
    | ~ v1_funct_2('#skF_8',u1_struct_0(k1_tsep_1('#skF_4','#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_8')
    | ~ r4_tsep_1('#skF_4','#skF_6','#skF_7')
    | ~ m1_pre_topc('#skF_7','#skF_4')
    | v2_struct_0('#skF_7')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | v2_struct_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_5593])).

tff(c_5657,plain,
    ( v1_funct_2(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_7','#skF_8'),u1_struct_0('#skF_7'),u1_struct_0('#skF_5'))
    | ~ r4_tsep_1('#skF_4','#skF_6','#skF_7')
    | v2_struct_0('#skF_7')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_92,c_90,c_84,c_78,c_76,c_74,c_4244,c_5620])).

tff(c_5658,plain,(
    ~ r4_tsep_1('#skF_4','#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_94,c_88,c_82,c_4245,c_5657])).

tff(c_5661,plain,
    ( ~ m1_pre_topc('#skF_7','#skF_4')
    | ~ v1_tsep_1('#skF_7','#skF_4')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ v1_tsep_1('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_5658])).

tff(c_5664,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_86,c_84,c_80,c_78,c_5661])).

tff(c_5666,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_5664])).

tff(c_5668,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_6','#skF_8'),u1_struct_0('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_5667,plain,(
    v5_pre_topc('#skF_8',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_6995,plain,(
    ! [C_412,B_414,D_415,A_413,E_416] :
      ( v1_funct_2(k3_tmap_1(A_413,B_414,k1_tsep_1(A_413,C_412,D_415),C_412,E_416),u1_struct_0(C_412),u1_struct_0(B_414))
      | ~ v5_pre_topc(E_416,k1_tsep_1(A_413,C_412,D_415),B_414)
      | ~ m1_subset_1(E_416,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_413,C_412,D_415)),u1_struct_0(B_414))))
      | ~ v1_funct_2(E_416,u1_struct_0(k1_tsep_1(A_413,C_412,D_415)),u1_struct_0(B_414))
      | ~ v1_funct_1(E_416)
      | ~ r4_tsep_1(A_413,C_412,D_415)
      | ~ m1_pre_topc(D_415,A_413)
      | v2_struct_0(D_415)
      | ~ m1_pre_topc(C_412,A_413)
      | v2_struct_0(C_412)
      | ~ l1_pre_topc(B_414)
      | ~ v2_pre_topc(B_414)
      | v2_struct_0(B_414)
      | ~ l1_pre_topc(A_413)
      | ~ v2_pre_topc(A_413)
      | v2_struct_0(A_413) ) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_7022,plain,
    ( v1_funct_2(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_6','#skF_8'),u1_struct_0('#skF_6'),u1_struct_0('#skF_5'))
    | ~ v5_pre_topc('#skF_8',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_5')
    | ~ v1_funct_2('#skF_8',u1_struct_0(k1_tsep_1('#skF_4','#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_8')
    | ~ r4_tsep_1('#skF_4','#skF_6','#skF_7')
    | ~ m1_pre_topc('#skF_7','#skF_4')
    | v2_struct_0('#skF_7')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | v2_struct_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_6995])).

tff(c_7059,plain,
    ( v1_funct_2(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_6','#skF_8'),u1_struct_0('#skF_6'),u1_struct_0('#skF_5'))
    | ~ r4_tsep_1('#skF_4','#skF_6','#skF_7')
    | v2_struct_0('#skF_7')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_92,c_90,c_84,c_78,c_76,c_74,c_5667,c_7022])).

tff(c_7060,plain,(
    ~ r4_tsep_1('#skF_4','#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_94,c_88,c_82,c_5668,c_7059])).

tff(c_7063,plain,
    ( ~ m1_pre_topc('#skF_7','#skF_4')
    | ~ v1_tsep_1('#skF_7','#skF_4')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ v1_tsep_1('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_7060])).

tff(c_7066,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_86,c_84,c_80,c_78,c_7063])).

tff(c_7068,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_7066])).

tff(c_7070,plain,(
    ~ v5_pre_topc(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_6','#skF_8'),'#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_7069,plain,(
    v5_pre_topc('#skF_8',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_8150,plain,(
    ! [A_475,C_474,E_478,D_477,B_476] :
      ( v5_pre_topc(k3_tmap_1(A_475,B_476,k1_tsep_1(A_475,C_474,D_477),C_474,E_478),C_474,B_476)
      | ~ v5_pre_topc(E_478,k1_tsep_1(A_475,C_474,D_477),B_476)
      | ~ m1_subset_1(E_478,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_475,C_474,D_477)),u1_struct_0(B_476))))
      | ~ v1_funct_2(E_478,u1_struct_0(k1_tsep_1(A_475,C_474,D_477)),u1_struct_0(B_476))
      | ~ v1_funct_1(E_478)
      | ~ r4_tsep_1(A_475,C_474,D_477)
      | ~ m1_pre_topc(D_477,A_475)
      | v2_struct_0(D_477)
      | ~ m1_pre_topc(C_474,A_475)
      | v2_struct_0(C_474)
      | ~ l1_pre_topc(B_476)
      | ~ v2_pre_topc(B_476)
      | v2_struct_0(B_476)
      | ~ l1_pre_topc(A_475)
      | ~ v2_pre_topc(A_475)
      | v2_struct_0(A_475) ) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_8173,plain,
    ( v5_pre_topc(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_6','#skF_8'),'#skF_6','#skF_5')
    | ~ v5_pre_topc('#skF_8',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_5')
    | ~ v1_funct_2('#skF_8',u1_struct_0(k1_tsep_1('#skF_4','#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_8')
    | ~ r4_tsep_1('#skF_4','#skF_6','#skF_7')
    | ~ m1_pre_topc('#skF_7','#skF_4')
    | v2_struct_0('#skF_7')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | v2_struct_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_8150])).

tff(c_8204,plain,
    ( v5_pre_topc(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_6','#skF_8'),'#skF_6','#skF_5')
    | ~ r4_tsep_1('#skF_4','#skF_6','#skF_7')
    | v2_struct_0('#skF_7')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_92,c_90,c_84,c_78,c_76,c_74,c_7069,c_8173])).

tff(c_8205,plain,(
    ~ r4_tsep_1('#skF_4','#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_94,c_88,c_82,c_7070,c_8204])).

tff(c_8208,plain,
    ( ~ m1_pre_topc('#skF_7','#skF_4')
    | ~ v1_tsep_1('#skF_7','#skF_4')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ v1_tsep_1('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_8205])).

tff(c_8211,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_86,c_84,c_80,c_78,c_8208])).

tff(c_8213,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_8211])).

tff(c_8215,plain,(
    ~ v5_pre_topc(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_7','#skF_8'),'#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_8214,plain,(
    v5_pre_topc('#skF_8',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_9410,plain,(
    ! [B_549,C_547,A_548,D_550,E_551] :
      ( v5_pre_topc(k3_tmap_1(A_548,B_549,k1_tsep_1(A_548,C_547,D_550),D_550,E_551),D_550,B_549)
      | ~ v5_pre_topc(E_551,k1_tsep_1(A_548,C_547,D_550),B_549)
      | ~ m1_subset_1(E_551,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_548,C_547,D_550)),u1_struct_0(B_549))))
      | ~ v1_funct_2(E_551,u1_struct_0(k1_tsep_1(A_548,C_547,D_550)),u1_struct_0(B_549))
      | ~ v1_funct_1(E_551)
      | ~ r4_tsep_1(A_548,C_547,D_550)
      | ~ m1_pre_topc(D_550,A_548)
      | v2_struct_0(D_550)
      | ~ m1_pre_topc(C_547,A_548)
      | v2_struct_0(C_547)
      | ~ l1_pre_topc(B_549)
      | ~ v2_pre_topc(B_549)
      | v2_struct_0(B_549)
      | ~ l1_pre_topc(A_548)
      | ~ v2_pre_topc(A_548)
      | v2_struct_0(A_548) ) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_9433,plain,
    ( v5_pre_topc(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_7','#skF_8'),'#skF_7','#skF_5')
    | ~ v5_pre_topc('#skF_8',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_5')
    | ~ v1_funct_2('#skF_8',u1_struct_0(k1_tsep_1('#skF_4','#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_8')
    | ~ r4_tsep_1('#skF_4','#skF_6','#skF_7')
    | ~ m1_pre_topc('#skF_7','#skF_4')
    | v2_struct_0('#skF_7')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | v2_struct_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_9410])).

tff(c_9464,plain,
    ( v5_pre_topc(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_7','#skF_8'),'#skF_7','#skF_5')
    | ~ r4_tsep_1('#skF_4','#skF_6','#skF_7')
    | v2_struct_0('#skF_7')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_92,c_90,c_84,c_78,c_76,c_74,c_8214,c_9433])).

tff(c_9465,plain,(
    ~ r4_tsep_1('#skF_4','#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_94,c_88,c_82,c_8215,c_9464])).

tff(c_9468,plain,
    ( ~ m1_pre_topc('#skF_7','#skF_4')
    | ~ v1_tsep_1('#skF_7','#skF_4')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ v1_tsep_1('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_9465])).

tff(c_9471,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_86,c_84,c_80,c_78,c_9468])).

tff(c_9473,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_9471])).

tff(c_9475,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_9474,plain,(
    v5_pre_topc('#skF_8',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_10352,plain,(
    ! [E_615,B_613,C_611,A_612,D_614] :
      ( v1_funct_1(k3_tmap_1(A_612,B_613,k1_tsep_1(A_612,C_611,D_614),D_614,E_615))
      | ~ v5_pre_topc(E_615,k1_tsep_1(A_612,C_611,D_614),B_613)
      | ~ m1_subset_1(E_615,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_612,C_611,D_614)),u1_struct_0(B_613))))
      | ~ v1_funct_2(E_615,u1_struct_0(k1_tsep_1(A_612,C_611,D_614)),u1_struct_0(B_613))
      | ~ v1_funct_1(E_615)
      | ~ r4_tsep_1(A_612,C_611,D_614)
      | ~ m1_pre_topc(D_614,A_612)
      | v2_struct_0(D_614)
      | ~ m1_pre_topc(C_611,A_612)
      | v2_struct_0(C_611)
      | ~ l1_pre_topc(B_613)
      | ~ v2_pre_topc(B_613)
      | v2_struct_0(B_613)
      | ~ l1_pre_topc(A_612)
      | ~ v2_pre_topc(A_612)
      | v2_struct_0(A_612) ) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_10373,plain,
    ( v1_funct_1(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_7','#skF_8'))
    | ~ v5_pre_topc('#skF_8',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_5')
    | ~ v1_funct_2('#skF_8',u1_struct_0(k1_tsep_1('#skF_4','#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_8')
    | ~ r4_tsep_1('#skF_4','#skF_6','#skF_7')
    | ~ m1_pre_topc('#skF_7','#skF_4')
    | v2_struct_0('#skF_7')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | v2_struct_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_10352])).

tff(c_10401,plain,
    ( v1_funct_1(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_7','#skF_8'))
    | ~ r4_tsep_1('#skF_4','#skF_6','#skF_7')
    | v2_struct_0('#skF_7')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_92,c_90,c_84,c_78,c_76,c_74,c_9474,c_10373])).

tff(c_10402,plain,(
    ~ r4_tsep_1('#skF_4','#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_94,c_88,c_82,c_9475,c_10401])).

tff(c_10405,plain,
    ( ~ m1_pre_topc('#skF_7','#skF_4')
    | ~ v1_tsep_1('#skF_7','#skF_4')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ v1_tsep_1('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_10402])).

tff(c_10408,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_86,c_84,c_80,c_78,c_10405])).

tff(c_10410,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_10408])).

tff(c_10412,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_10411,plain,(
    v5_pre_topc('#skF_8',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_10850,plain,(
    ! [D_660,E_661,B_659,C_657,A_658] :
      ( v1_funct_1(k3_tmap_1(A_658,B_659,k1_tsep_1(A_658,C_657,D_660),C_657,E_661))
      | ~ v5_pre_topc(E_661,k1_tsep_1(A_658,C_657,D_660),B_659)
      | ~ m1_subset_1(E_661,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_658,C_657,D_660)),u1_struct_0(B_659))))
      | ~ v1_funct_2(E_661,u1_struct_0(k1_tsep_1(A_658,C_657,D_660)),u1_struct_0(B_659))
      | ~ v1_funct_1(E_661)
      | ~ r4_tsep_1(A_658,C_657,D_660)
      | ~ m1_pre_topc(D_660,A_658)
      | v2_struct_0(D_660)
      | ~ m1_pre_topc(C_657,A_658)
      | v2_struct_0(C_657)
      | ~ l1_pre_topc(B_659)
      | ~ v2_pre_topc(B_659)
      | v2_struct_0(B_659)
      | ~ l1_pre_topc(A_658)
      | ~ v2_pre_topc(A_658)
      | v2_struct_0(A_658) ) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_10863,plain,
    ( v1_funct_1(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_6','#skF_8'))
    | ~ v5_pre_topc('#skF_8',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_5')
    | ~ v1_funct_2('#skF_8',u1_struct_0(k1_tsep_1('#skF_4','#skF_6','#skF_7')),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_8')
    | ~ r4_tsep_1('#skF_4','#skF_6','#skF_7')
    | ~ m1_pre_topc('#skF_7','#skF_4')
    | v2_struct_0('#skF_7')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | v2_struct_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_10850])).

tff(c_10879,plain,
    ( v1_funct_1(k3_tmap_1('#skF_4','#skF_5',k1_tsep_1('#skF_4','#skF_6','#skF_7'),'#skF_6','#skF_8'))
    | ~ r4_tsep_1('#skF_4','#skF_6','#skF_7')
    | v2_struct_0('#skF_7')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_92,c_90,c_84,c_78,c_76,c_74,c_10411,c_10863])).

tff(c_10880,plain,(
    ~ r4_tsep_1('#skF_4','#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_94,c_88,c_82,c_10412,c_10879])).

tff(c_10883,plain,
    ( ~ m1_pre_topc('#skF_7','#skF_4')
    | ~ v1_tsep_1('#skF_7','#skF_4')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ v1_tsep_1('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_10880])).

tff(c_10886,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_86,c_84,c_80,c_78,c_10883])).

tff(c_10888,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_10886])).

%------------------------------------------------------------------------------
