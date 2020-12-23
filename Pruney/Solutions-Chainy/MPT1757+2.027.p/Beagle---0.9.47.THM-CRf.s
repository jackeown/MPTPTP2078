%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:07 EST 2020

% Result     : Theorem 3.76s
% Output     : CNFRefutation 4.01s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 703 expanded)
%              Number of leaves         :   41 ( 284 expanded)
%              Depth                    :   24
%              Number of atoms          :  401 (5237 expanded)
%              Number of equality atoms :    5 ( 255 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_283,negated_conjecture,(
    ~ ! [A] :
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
                      & v1_tsep_1(D,B)
                      & m1_pre_topc(D,B) )
                   => ! [E] :
                        ( m1_subset_1(E,u1_struct_0(B))
                       => ! [F] :
                            ( m1_subset_1(F,u1_struct_0(D))
                           => ( E = F
                             => ( r1_tmap_1(B,A,C,E)
                              <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_153,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_146,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( ( v1_tsep_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).

tff(f_128,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ~ ( m1_connsp_2(C,A,B)
                  & ! [D] :
                      ( ( ~ v1_xboole_0(D)
                        & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A))) )
                     => ~ ( m1_connsp_2(D,A,B)
                          & v3_pre_topc(D,A)
                          & r1_tarski(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_connsp_2)).

tff(f_240,axiom,(
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
                      ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(B)))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(B))
                         => ! [G] :
                              ( m1_subset_1(G,u1_struct_0(D))
                             => ( ( r1_tarski(E,u1_struct_0(D))
                                  & m1_connsp_2(E,B,F)
                                  & F = G )
                               => ( r1_tmap_1(B,A,C,F)
                                <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),G) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tmap_1)).

tff(f_66,axiom,(
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

tff(f_99,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( v3_pre_topc(B,A)
                  & r2_hidden(C,B) )
               => m1_connsp_2(B,A,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

tff(f_50,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_193,axiom,(
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

tff(c_50,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_46,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_40,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_42,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_77,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42])).

tff(c_58,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_85,plain,(
    ! [B_298,A_299] :
      ( l1_pre_topc(B_298)
      | ~ m1_pre_topc(B_298,A_299)
      | ~ l1_pre_topc(A_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_88,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_85])).

tff(c_91,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_88])).

tff(c_4,plain,(
    ! [A_3] :
      ( l1_struct_0(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_48,plain,(
    v1_tsep_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_32,plain,(
    ! [B_49,A_47] :
      ( m1_subset_1(u1_struct_0(B_49),k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ m1_pre_topc(B_49,A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_138,plain,(
    ! [B_321,A_322] :
      ( v3_pre_topc(u1_struct_0(B_321),A_322)
      | ~ v1_tsep_1(B_321,A_322)
      | ~ m1_subset_1(u1_struct_0(B_321),k1_zfmisc_1(u1_struct_0(A_322)))
      | ~ m1_pre_topc(B_321,A_322)
      | ~ l1_pre_topc(A_322)
      | ~ v2_pre_topc(A_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_142,plain,(
    ! [B_49,A_47] :
      ( v3_pre_topc(u1_struct_0(B_49),A_47)
      | ~ v1_tsep_1(B_49,A_47)
      | ~ v2_pre_topc(A_47)
      | ~ m1_pre_topc(B_49,A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_32,c_138])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_153,plain,(
    ! [A_331,B_332,C_333] :
      ( r1_tarski('#skF_1'(A_331,B_332,C_333),C_333)
      | ~ m1_connsp_2(C_333,A_331,B_332)
      | ~ m1_subset_1(C_333,k1_zfmisc_1(u1_struct_0(A_331)))
      | ~ m1_subset_1(B_332,u1_struct_0(A_331))
      | ~ l1_pre_topc(A_331)
      | ~ v2_pre_topc(A_331)
      | v2_struct_0(A_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_156,plain,(
    ! [A_47,B_332,B_49] :
      ( r1_tarski('#skF_1'(A_47,B_332,u1_struct_0(B_49)),u1_struct_0(B_49))
      | ~ m1_connsp_2(u1_struct_0(B_49),A_47,B_332)
      | ~ m1_subset_1(B_332,u1_struct_0(A_47))
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47)
      | ~ m1_pre_topc(B_49,A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_32,c_153])).

tff(c_22,plain,(
    ! [A_26,B_34,C_38] :
      ( m1_subset_1('#skF_1'(A_26,B_34,C_38),k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ m1_connsp_2(C_38,A_26,B_34)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ m1_subset_1(B_34,u1_struct_0(A_26))
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_76,plain,
    ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
    | r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_78,plain,
    ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
    | r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76])).

tff(c_93,plain,(
    r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_70,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_7')
    | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_79,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_6')
    | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_70])).

tff(c_97,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_79])).

tff(c_66,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_64,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_54,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_442,plain,(
    ! [D_396,E_397,B_398,A_400,G_399,C_395] :
      ( r1_tmap_1(B_398,A_400,C_395,G_399)
      | ~ r1_tmap_1(D_396,A_400,k2_tmap_1(B_398,A_400,C_395,D_396),G_399)
      | ~ m1_connsp_2(E_397,B_398,G_399)
      | ~ r1_tarski(E_397,u1_struct_0(D_396))
      | ~ m1_subset_1(G_399,u1_struct_0(D_396))
      | ~ m1_subset_1(G_399,u1_struct_0(B_398))
      | ~ m1_subset_1(E_397,k1_zfmisc_1(u1_struct_0(B_398)))
      | ~ m1_pre_topc(D_396,B_398)
      | v2_struct_0(D_396)
      | ~ m1_subset_1(C_395,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_398),u1_struct_0(A_400))))
      | ~ v1_funct_2(C_395,u1_struct_0(B_398),u1_struct_0(A_400))
      | ~ v1_funct_1(C_395)
      | ~ l1_pre_topc(B_398)
      | ~ v2_pre_topc(B_398)
      | v2_struct_0(B_398)
      | ~ l1_pre_topc(A_400)
      | ~ v2_pre_topc(A_400)
      | v2_struct_0(A_400) ) ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_446,plain,(
    ! [E_397] :
      ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
      | ~ m1_connsp_2(E_397,'#skF_3','#skF_6')
      | ~ r1_tarski(E_397,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(E_397,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_93,c_442])).

tff(c_453,plain,(
    ! [E_397] :
      ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
      | ~ m1_connsp_2(E_397,'#skF_3','#skF_6')
      | ~ r1_tarski(E_397,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(E_397,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_58,c_56,c_54,c_52,c_46,c_44,c_77,c_446])).

tff(c_455,plain,(
    ! [E_401] :
      ( ~ m1_connsp_2(E_401,'#skF_3','#skF_6')
      | ~ r1_tarski(E_401,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(E_401,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_50,c_97,c_453])).

tff(c_469,plain,(
    ! [B_34,C_38] :
      ( ~ m1_connsp_2('#skF_1'('#skF_3',B_34,C_38),'#skF_3','#skF_6')
      | ~ r1_tarski('#skF_1'('#skF_3',B_34,C_38),u1_struct_0('#skF_5'))
      | ~ m1_connsp_2(C_38,'#skF_3',B_34)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_34,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_455])).

tff(c_485,plain,(
    ! [B_34,C_38] :
      ( ~ m1_connsp_2('#skF_1'('#skF_3',B_34,C_38),'#skF_3','#skF_6')
      | ~ r1_tarski('#skF_1'('#skF_3',B_34,C_38),u1_struct_0('#skF_5'))
      | ~ m1_connsp_2(C_38,'#skF_3',B_34)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_34,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_469])).

tff(c_492,plain,(
    ! [B_403,C_404] :
      ( ~ m1_connsp_2('#skF_1'('#skF_3',B_403,C_404),'#skF_3','#skF_6')
      | ~ r1_tarski('#skF_1'('#skF_3',B_403,C_404),u1_struct_0('#skF_5'))
      | ~ m1_connsp_2(C_404,'#skF_3',B_403)
      | ~ m1_subset_1(C_404,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_403,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_485])).

tff(c_500,plain,(
    ! [B_332] :
      ( ~ m1_connsp_2('#skF_1'('#skF_3',B_332,u1_struct_0('#skF_5')),'#skF_3','#skF_6')
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3',B_332)
      | ~ m1_subset_1(B_332,u1_struct_0('#skF_3'))
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_156,c_492])).

tff(c_506,plain,(
    ! [B_332] :
      ( ~ m1_connsp_2('#skF_1'('#skF_3',B_332,u1_struct_0('#skF_5')),'#skF_3','#skF_6')
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3',B_332)
      | ~ m1_subset_1(B_332,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_46,c_60,c_500])).

tff(c_507,plain,(
    ! [B_332] :
      ( ~ m1_connsp_2('#skF_1'('#skF_3',B_332,u1_struct_0('#skF_5')),'#skF_3','#skF_6')
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3',B_332)
      | ~ m1_subset_1(B_332,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_506])).

tff(c_508,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_507])).

tff(c_514,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_508])).

tff(c_521,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_46,c_514])).

tff(c_523,plain,(
    m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_507])).

tff(c_98,plain,(
    ! [C_305,A_306,B_307] :
      ( m1_subset_1(C_305,u1_struct_0(A_306))
      | ~ m1_subset_1(C_305,u1_struct_0(B_307))
      | ~ m1_pre_topc(B_307,A_306)
      | v2_struct_0(B_307)
      | ~ l1_pre_topc(A_306)
      | v2_struct_0(A_306) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_100,plain,(
    ! [A_306] :
      ( m1_subset_1('#skF_6',u1_struct_0(A_306))
      | ~ m1_pre_topc('#skF_5',A_306)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_306)
      | v2_struct_0(A_306) ) ),
    inference(resolution,[status(thm)],[c_77,c_98])).

tff(c_105,plain,(
    ! [A_306] :
      ( m1_subset_1('#skF_6',u1_struct_0(A_306))
      | ~ m1_pre_topc('#skF_5',A_306)
      | ~ l1_pre_topc(A_306)
      | v2_struct_0(A_306) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_100])).

tff(c_157,plain,(
    ! [B_334,A_335,C_336] :
      ( m1_connsp_2(B_334,A_335,C_336)
      | ~ r2_hidden(C_336,B_334)
      | ~ v3_pre_topc(B_334,A_335)
      | ~ m1_subset_1(C_336,u1_struct_0(A_335))
      | ~ m1_subset_1(B_334,k1_zfmisc_1(u1_struct_0(A_335)))
      | ~ l1_pre_topc(A_335)
      | ~ v2_pre_topc(A_335)
      | v2_struct_0(A_335) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_167,plain,(
    ! [B_334,A_306] :
      ( m1_connsp_2(B_334,A_306,'#skF_6')
      | ~ r2_hidden('#skF_6',B_334)
      | ~ v3_pre_topc(B_334,A_306)
      | ~ m1_subset_1(B_334,k1_zfmisc_1(u1_struct_0(A_306)))
      | ~ v2_pre_topc(A_306)
      | ~ m1_pre_topc('#skF_5',A_306)
      | ~ l1_pre_topc(A_306)
      | v2_struct_0(A_306) ) ),
    inference(resolution,[status(thm)],[c_105,c_157])).

tff(c_533,plain,
    ( m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3','#skF_6')
    | ~ r2_hidden('#skF_6',u1_struct_0('#skF_5'))
    | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_523,c_167])).

tff(c_552,plain,
    ( m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3','#skF_6')
    | ~ r2_hidden('#skF_6',u1_struct_0('#skF_5'))
    | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_46,c_60,c_533])).

tff(c_553,plain,
    ( m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3','#skF_6')
    | ~ r2_hidden('#skF_6',u1_struct_0('#skF_5'))
    | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_552])).

tff(c_569,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_553])).

tff(c_572,plain,
    ( ~ v1_tsep_1('#skF_5','#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_142,c_569])).

tff(c_576,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_46,c_60,c_48,c_572])).

tff(c_577,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_5'))
    | m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3','#skF_6') ),
    inference(splitRight,[status(thm)],[c_553])).

tff(c_586,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_577])).

tff(c_589,plain,
    ( v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_2,c_586])).

tff(c_592,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_589])).

tff(c_8,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0(u1_struct_0(A_7))
      | ~ l1_struct_0(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_595,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_592,c_8])).

tff(c_598,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_595])).

tff(c_601,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_598])).

tff(c_605,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_601])).

tff(c_606,plain,(
    m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3','#skF_6') ),
    inference(splitRight,[status(thm)],[c_577])).

tff(c_20,plain,(
    ! [A_26,B_34,C_38] :
      ( m1_connsp_2('#skF_1'(A_26,B_34,C_38),A_26,B_34)
      | ~ m1_connsp_2(C_38,A_26,B_34)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ m1_subset_1(B_34,u1_struct_0(A_26))
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_530,plain,(
    ! [B_34] :
      ( m1_connsp_2('#skF_1'('#skF_3',B_34,u1_struct_0('#skF_5')),'#skF_3',B_34)
      | ~ m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3',B_34)
      | ~ m1_subset_1(B_34,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_523,c_20])).

tff(c_548,plain,(
    ! [B_34] :
      ( m1_connsp_2('#skF_1'('#skF_3',B_34,u1_struct_0('#skF_5')),'#skF_3',B_34)
      | ~ m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3',B_34)
      | ~ m1_subset_1(B_34,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_530])).

tff(c_549,plain,(
    ! [B_34] :
      ( m1_connsp_2('#skF_1'('#skF_3',B_34,u1_struct_0('#skF_5')),'#skF_3',B_34)
      | ~ m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3',B_34)
      | ~ m1_subset_1(B_34,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_548])).

tff(c_666,plain,(
    ! [B_415] :
      ( ~ m1_connsp_2('#skF_1'('#skF_3',B_415,u1_struct_0('#skF_5')),'#skF_3','#skF_6')
      | ~ m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3',B_415)
      | ~ m1_subset_1(B_415,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_507])).

tff(c_670,plain,
    ( ~ m1_connsp_2(u1_struct_0('#skF_5'),'#skF_3','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_549,c_666])).

tff(c_686,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_606,c_670])).

tff(c_687,plain,(
    r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_879,plain,(
    ! [B_484,A_481,D_482,C_480,F_483] :
      ( r1_tmap_1(D_482,A_481,k2_tmap_1(B_484,A_481,C_480,D_482),F_483)
      | ~ r1_tmap_1(B_484,A_481,C_480,F_483)
      | ~ m1_subset_1(F_483,u1_struct_0(D_482))
      | ~ m1_subset_1(F_483,u1_struct_0(B_484))
      | ~ m1_pre_topc(D_482,B_484)
      | v2_struct_0(D_482)
      | ~ m1_subset_1(C_480,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_484),u1_struct_0(A_481))))
      | ~ v1_funct_2(C_480,u1_struct_0(B_484),u1_struct_0(A_481))
      | ~ v1_funct_1(C_480)
      | ~ l1_pre_topc(B_484)
      | ~ v2_pre_topc(B_484)
      | v2_struct_0(B_484)
      | ~ l1_pre_topc(A_481)
      | ~ v2_pre_topc(A_481)
      | v2_struct_0(A_481) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_881,plain,(
    ! [D_482,F_483] :
      ( r1_tmap_1(D_482,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4',D_482),F_483)
      | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4',F_483)
      | ~ m1_subset_1(F_483,u1_struct_0(D_482))
      | ~ m1_subset_1(F_483,u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_482,'#skF_3')
      | v2_struct_0(D_482)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_52,c_879])).

tff(c_884,plain,(
    ! [D_482,F_483] :
      ( r1_tmap_1(D_482,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4',D_482),F_483)
      | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4',F_483)
      | ~ m1_subset_1(F_483,u1_struct_0(D_482))
      | ~ m1_subset_1(F_483,u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_482,'#skF_3')
      | v2_struct_0(D_482)
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_58,c_56,c_54,c_881])).

tff(c_886,plain,(
    ! [D_485,F_486] :
      ( r1_tmap_1(D_485,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4',D_485),F_486)
      | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4',F_486)
      | ~ m1_subset_1(F_486,u1_struct_0(D_485))
      | ~ m1_subset_1(F_486,u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_485,'#skF_3')
      | v2_struct_0(D_485) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_884])).

tff(c_688,plain,(
    ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_889,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_886,c_688])).

tff(c_892,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_77,c_687,c_889])).

tff(c_894,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_892])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:00:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.76/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.76/1.67  
% 3.76/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.76/1.68  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 3.76/1.68  
% 3.76/1.68  %Foreground sorts:
% 3.76/1.68  
% 3.76/1.68  
% 3.76/1.68  %Background operators:
% 3.76/1.68  
% 3.76/1.68  
% 3.76/1.68  %Foreground operators:
% 3.76/1.68  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.76/1.68  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.76/1.68  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.76/1.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.76/1.68  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.76/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.76/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.76/1.68  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.76/1.68  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.76/1.68  tff('#skF_7', type, '#skF_7': $i).
% 3.76/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.76/1.68  tff('#skF_5', type, '#skF_5': $i).
% 3.76/1.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.76/1.68  tff('#skF_6', type, '#skF_6': $i).
% 3.76/1.68  tff('#skF_2', type, '#skF_2': $i).
% 3.76/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.76/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.76/1.68  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.76/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.76/1.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.76/1.68  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.76/1.68  tff('#skF_4', type, '#skF_4': $i).
% 3.76/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.76/1.68  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.76/1.68  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.76/1.68  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.76/1.68  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.76/1.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.76/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.76/1.68  
% 4.01/1.70  tff(f_283, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_tmap_1)).
% 4.01/1.70  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.01/1.70  tff(f_35, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.01/1.70  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.01/1.70  tff(f_153, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.01/1.70  tff(f_146, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 4.01/1.70  tff(f_128, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(C, A, B) & (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~((m1_connsp_2(D, A, B) & v3_pre_topc(D, A)) & r1_tarski(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_connsp_2)).
% 4.01/1.70  tff(f_240, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tmap_1)).
% 4.01/1.70  tff(f_66, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 4.01/1.70  tff(f_99, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 4.01/1.70  tff(f_50, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.01/1.70  tff(f_193, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 4.01/1.70  tff(c_50, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.01/1.70  tff(c_46, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.01/1.70  tff(c_44, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.01/1.70  tff(c_40, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.01/1.70  tff(c_42, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.01/1.70  tff(c_77, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42])).
% 4.01/1.70  tff(c_58, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.01/1.70  tff(c_85, plain, (![B_298, A_299]: (l1_pre_topc(B_298) | ~m1_pre_topc(B_298, A_299) | ~l1_pre_topc(A_299))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.01/1.70  tff(c_88, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_46, c_85])).
% 4.01/1.70  tff(c_91, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_88])).
% 4.01/1.70  tff(c_4, plain, (![A_3]: (l1_struct_0(A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.01/1.70  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.01/1.70  tff(c_60, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.01/1.70  tff(c_48, plain, (v1_tsep_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.01/1.70  tff(c_32, plain, (![B_49, A_47]: (m1_subset_1(u1_struct_0(B_49), k1_zfmisc_1(u1_struct_0(A_47))) | ~m1_pre_topc(B_49, A_47) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.01/1.70  tff(c_138, plain, (![B_321, A_322]: (v3_pre_topc(u1_struct_0(B_321), A_322) | ~v1_tsep_1(B_321, A_322) | ~m1_subset_1(u1_struct_0(B_321), k1_zfmisc_1(u1_struct_0(A_322))) | ~m1_pre_topc(B_321, A_322) | ~l1_pre_topc(A_322) | ~v2_pre_topc(A_322))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.01/1.70  tff(c_142, plain, (![B_49, A_47]: (v3_pre_topc(u1_struct_0(B_49), A_47) | ~v1_tsep_1(B_49, A_47) | ~v2_pre_topc(A_47) | ~m1_pre_topc(B_49, A_47) | ~l1_pre_topc(A_47))), inference(resolution, [status(thm)], [c_32, c_138])).
% 4.01/1.70  tff(c_62, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.01/1.70  tff(c_153, plain, (![A_331, B_332, C_333]: (r1_tarski('#skF_1'(A_331, B_332, C_333), C_333) | ~m1_connsp_2(C_333, A_331, B_332) | ~m1_subset_1(C_333, k1_zfmisc_1(u1_struct_0(A_331))) | ~m1_subset_1(B_332, u1_struct_0(A_331)) | ~l1_pre_topc(A_331) | ~v2_pre_topc(A_331) | v2_struct_0(A_331))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.01/1.70  tff(c_156, plain, (![A_47, B_332, B_49]: (r1_tarski('#skF_1'(A_47, B_332, u1_struct_0(B_49)), u1_struct_0(B_49)) | ~m1_connsp_2(u1_struct_0(B_49), A_47, B_332) | ~m1_subset_1(B_332, u1_struct_0(A_47)) | ~v2_pre_topc(A_47) | v2_struct_0(A_47) | ~m1_pre_topc(B_49, A_47) | ~l1_pre_topc(A_47))), inference(resolution, [status(thm)], [c_32, c_153])).
% 4.01/1.70  tff(c_22, plain, (![A_26, B_34, C_38]: (m1_subset_1('#skF_1'(A_26, B_34, C_38), k1_zfmisc_1(u1_struct_0(A_26))) | ~m1_connsp_2(C_38, A_26, B_34) | ~m1_subset_1(C_38, k1_zfmisc_1(u1_struct_0(A_26))) | ~m1_subset_1(B_34, u1_struct_0(A_26)) | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.01/1.70  tff(c_68, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.01/1.70  tff(c_76, plain, (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.01/1.70  tff(c_78, plain, (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_76])).
% 4.01/1.70  tff(c_93, plain, (r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_78])).
% 4.01/1.70  tff(c_70, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_7') | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.01/1.70  tff(c_79, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_6') | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_70])).
% 4.01/1.70  tff(c_97, plain, (~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_79])).
% 4.01/1.70  tff(c_66, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.01/1.70  tff(c_64, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.01/1.70  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.01/1.70  tff(c_54, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.01/1.70  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.01/1.70  tff(c_442, plain, (![D_396, E_397, B_398, A_400, G_399, C_395]: (r1_tmap_1(B_398, A_400, C_395, G_399) | ~r1_tmap_1(D_396, A_400, k2_tmap_1(B_398, A_400, C_395, D_396), G_399) | ~m1_connsp_2(E_397, B_398, G_399) | ~r1_tarski(E_397, u1_struct_0(D_396)) | ~m1_subset_1(G_399, u1_struct_0(D_396)) | ~m1_subset_1(G_399, u1_struct_0(B_398)) | ~m1_subset_1(E_397, k1_zfmisc_1(u1_struct_0(B_398))) | ~m1_pre_topc(D_396, B_398) | v2_struct_0(D_396) | ~m1_subset_1(C_395, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_398), u1_struct_0(A_400)))) | ~v1_funct_2(C_395, u1_struct_0(B_398), u1_struct_0(A_400)) | ~v1_funct_1(C_395) | ~l1_pre_topc(B_398) | ~v2_pre_topc(B_398) | v2_struct_0(B_398) | ~l1_pre_topc(A_400) | ~v2_pre_topc(A_400) | v2_struct_0(A_400))), inference(cnfTransformation, [status(thm)], [f_240])).
% 4.01/1.70  tff(c_446, plain, (![E_397]: (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | ~m1_connsp_2(E_397, '#skF_3', '#skF_6') | ~r1_tarski(E_397, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1(E_397, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_93, c_442])).
% 4.01/1.70  tff(c_453, plain, (![E_397]: (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | ~m1_connsp_2(E_397, '#skF_3', '#skF_6') | ~r1_tarski(E_397, u1_struct_0('#skF_5')) | ~m1_subset_1(E_397, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_5') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_58, c_56, c_54, c_52, c_46, c_44, c_77, c_446])).
% 4.01/1.70  tff(c_455, plain, (![E_401]: (~m1_connsp_2(E_401, '#skF_3', '#skF_6') | ~r1_tarski(E_401, u1_struct_0('#skF_5')) | ~m1_subset_1(E_401, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_50, c_97, c_453])).
% 4.01/1.70  tff(c_469, plain, (![B_34, C_38]: (~m1_connsp_2('#skF_1'('#skF_3', B_34, C_38), '#skF_3', '#skF_6') | ~r1_tarski('#skF_1'('#skF_3', B_34, C_38), u1_struct_0('#skF_5')) | ~m1_connsp_2(C_38, '#skF_3', B_34) | ~m1_subset_1(C_38, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_34, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_455])).
% 4.01/1.70  tff(c_485, plain, (![B_34, C_38]: (~m1_connsp_2('#skF_1'('#skF_3', B_34, C_38), '#skF_3', '#skF_6') | ~r1_tarski('#skF_1'('#skF_3', B_34, C_38), u1_struct_0('#skF_5')) | ~m1_connsp_2(C_38, '#skF_3', B_34) | ~m1_subset_1(C_38, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_34, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_469])).
% 4.01/1.70  tff(c_492, plain, (![B_403, C_404]: (~m1_connsp_2('#skF_1'('#skF_3', B_403, C_404), '#skF_3', '#skF_6') | ~r1_tarski('#skF_1'('#skF_3', B_403, C_404), u1_struct_0('#skF_5')) | ~m1_connsp_2(C_404, '#skF_3', B_403) | ~m1_subset_1(C_404, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_403, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_62, c_485])).
% 4.01/1.70  tff(c_500, plain, (![B_332]: (~m1_connsp_2('#skF_1'('#skF_3', B_332, u1_struct_0('#skF_5')), '#skF_3', '#skF_6') | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', B_332) | ~m1_subset_1(B_332, u1_struct_0('#skF_3')) | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_156, c_492])).
% 4.01/1.70  tff(c_506, plain, (![B_332]: (~m1_connsp_2('#skF_1'('#skF_3', B_332, u1_struct_0('#skF_5')), '#skF_3', '#skF_6') | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', B_332) | ~m1_subset_1(B_332, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_46, c_60, c_500])).
% 4.01/1.70  tff(c_507, plain, (![B_332]: (~m1_connsp_2('#skF_1'('#skF_3', B_332, u1_struct_0('#skF_5')), '#skF_3', '#skF_6') | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', B_332) | ~m1_subset_1(B_332, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_62, c_506])).
% 4.01/1.70  tff(c_508, plain, (~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_507])).
% 4.01/1.70  tff(c_514, plain, (~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_32, c_508])).
% 4.01/1.70  tff(c_521, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_46, c_514])).
% 4.01/1.70  tff(c_523, plain, (m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_507])).
% 4.01/1.70  tff(c_98, plain, (![C_305, A_306, B_307]: (m1_subset_1(C_305, u1_struct_0(A_306)) | ~m1_subset_1(C_305, u1_struct_0(B_307)) | ~m1_pre_topc(B_307, A_306) | v2_struct_0(B_307) | ~l1_pre_topc(A_306) | v2_struct_0(A_306))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.01/1.70  tff(c_100, plain, (![A_306]: (m1_subset_1('#skF_6', u1_struct_0(A_306)) | ~m1_pre_topc('#skF_5', A_306) | v2_struct_0('#skF_5') | ~l1_pre_topc(A_306) | v2_struct_0(A_306))), inference(resolution, [status(thm)], [c_77, c_98])).
% 4.01/1.70  tff(c_105, plain, (![A_306]: (m1_subset_1('#skF_6', u1_struct_0(A_306)) | ~m1_pre_topc('#skF_5', A_306) | ~l1_pre_topc(A_306) | v2_struct_0(A_306))), inference(negUnitSimplification, [status(thm)], [c_50, c_100])).
% 4.01/1.70  tff(c_157, plain, (![B_334, A_335, C_336]: (m1_connsp_2(B_334, A_335, C_336) | ~r2_hidden(C_336, B_334) | ~v3_pre_topc(B_334, A_335) | ~m1_subset_1(C_336, u1_struct_0(A_335)) | ~m1_subset_1(B_334, k1_zfmisc_1(u1_struct_0(A_335))) | ~l1_pre_topc(A_335) | ~v2_pre_topc(A_335) | v2_struct_0(A_335))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.01/1.70  tff(c_167, plain, (![B_334, A_306]: (m1_connsp_2(B_334, A_306, '#skF_6') | ~r2_hidden('#skF_6', B_334) | ~v3_pre_topc(B_334, A_306) | ~m1_subset_1(B_334, k1_zfmisc_1(u1_struct_0(A_306))) | ~v2_pre_topc(A_306) | ~m1_pre_topc('#skF_5', A_306) | ~l1_pre_topc(A_306) | v2_struct_0(A_306))), inference(resolution, [status(thm)], [c_105, c_157])).
% 4.01/1.70  tff(c_533, plain, (m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', '#skF_6') | ~r2_hidden('#skF_6', u1_struct_0('#skF_5')) | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_3') | ~v2_pre_topc('#skF_3') | ~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_523, c_167])).
% 4.01/1.70  tff(c_552, plain, (m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', '#skF_6') | ~r2_hidden('#skF_6', u1_struct_0('#skF_5')) | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_46, c_60, c_533])).
% 4.01/1.70  tff(c_553, plain, (m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', '#skF_6') | ~r2_hidden('#skF_6', u1_struct_0('#skF_5')) | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_62, c_552])).
% 4.01/1.70  tff(c_569, plain, (~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_553])).
% 4.01/1.70  tff(c_572, plain, (~v1_tsep_1('#skF_5', '#skF_3') | ~v2_pre_topc('#skF_3') | ~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_142, c_569])).
% 4.01/1.70  tff(c_576, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_46, c_60, c_48, c_572])).
% 4.01/1.70  tff(c_577, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_5')) | m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', '#skF_6')), inference(splitRight, [status(thm)], [c_553])).
% 4.01/1.70  tff(c_586, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_577])).
% 4.01/1.70  tff(c_589, plain, (v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_2, c_586])).
% 4.01/1.70  tff(c_592, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_589])).
% 4.01/1.70  tff(c_8, plain, (![A_7]: (~v1_xboole_0(u1_struct_0(A_7)) | ~l1_struct_0(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.01/1.70  tff(c_595, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_592, c_8])).
% 4.01/1.70  tff(c_598, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_50, c_595])).
% 4.01/1.70  tff(c_601, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_4, c_598])).
% 4.01/1.70  tff(c_605, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_601])).
% 4.01/1.70  tff(c_606, plain, (m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', '#skF_6')), inference(splitRight, [status(thm)], [c_577])).
% 4.01/1.70  tff(c_20, plain, (![A_26, B_34, C_38]: (m1_connsp_2('#skF_1'(A_26, B_34, C_38), A_26, B_34) | ~m1_connsp_2(C_38, A_26, B_34) | ~m1_subset_1(C_38, k1_zfmisc_1(u1_struct_0(A_26))) | ~m1_subset_1(B_34, u1_struct_0(A_26)) | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.01/1.70  tff(c_530, plain, (![B_34]: (m1_connsp_2('#skF_1'('#skF_3', B_34, u1_struct_0('#skF_5')), '#skF_3', B_34) | ~m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', B_34) | ~m1_subset_1(B_34, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_523, c_20])).
% 4.01/1.70  tff(c_548, plain, (![B_34]: (m1_connsp_2('#skF_1'('#skF_3', B_34, u1_struct_0('#skF_5')), '#skF_3', B_34) | ~m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', B_34) | ~m1_subset_1(B_34, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_530])).
% 4.01/1.70  tff(c_549, plain, (![B_34]: (m1_connsp_2('#skF_1'('#skF_3', B_34, u1_struct_0('#skF_5')), '#skF_3', B_34) | ~m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', B_34) | ~m1_subset_1(B_34, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_62, c_548])).
% 4.01/1.70  tff(c_666, plain, (![B_415]: (~m1_connsp_2('#skF_1'('#skF_3', B_415, u1_struct_0('#skF_5')), '#skF_3', '#skF_6') | ~m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', B_415) | ~m1_subset_1(B_415, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_507])).
% 4.01/1.70  tff(c_670, plain, (~m1_connsp_2(u1_struct_0('#skF_5'), '#skF_3', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_549, c_666])).
% 4.01/1.70  tff(c_686, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_606, c_670])).
% 4.01/1.70  tff(c_687, plain, (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_78])).
% 4.01/1.70  tff(c_879, plain, (![B_484, A_481, D_482, C_480, F_483]: (r1_tmap_1(D_482, A_481, k2_tmap_1(B_484, A_481, C_480, D_482), F_483) | ~r1_tmap_1(B_484, A_481, C_480, F_483) | ~m1_subset_1(F_483, u1_struct_0(D_482)) | ~m1_subset_1(F_483, u1_struct_0(B_484)) | ~m1_pre_topc(D_482, B_484) | v2_struct_0(D_482) | ~m1_subset_1(C_480, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_484), u1_struct_0(A_481)))) | ~v1_funct_2(C_480, u1_struct_0(B_484), u1_struct_0(A_481)) | ~v1_funct_1(C_480) | ~l1_pre_topc(B_484) | ~v2_pre_topc(B_484) | v2_struct_0(B_484) | ~l1_pre_topc(A_481) | ~v2_pre_topc(A_481) | v2_struct_0(A_481))), inference(cnfTransformation, [status(thm)], [f_193])).
% 4.01/1.70  tff(c_881, plain, (![D_482, F_483]: (r1_tmap_1(D_482, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_482), F_483) | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', F_483) | ~m1_subset_1(F_483, u1_struct_0(D_482)) | ~m1_subset_1(F_483, u1_struct_0('#skF_3')) | ~m1_pre_topc(D_482, '#skF_3') | v2_struct_0(D_482) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_52, c_879])).
% 4.01/1.70  tff(c_884, plain, (![D_482, F_483]: (r1_tmap_1(D_482, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_482), F_483) | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', F_483) | ~m1_subset_1(F_483, u1_struct_0(D_482)) | ~m1_subset_1(F_483, u1_struct_0('#skF_3')) | ~m1_pre_topc(D_482, '#skF_3') | v2_struct_0(D_482) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_58, c_56, c_54, c_881])).
% 4.01/1.70  tff(c_886, plain, (![D_485, F_486]: (r1_tmap_1(D_485, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_485), F_486) | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', F_486) | ~m1_subset_1(F_486, u1_struct_0(D_485)) | ~m1_subset_1(F_486, u1_struct_0('#skF_3')) | ~m1_pre_topc(D_485, '#skF_3') | v2_struct_0(D_485))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_884])).
% 4.01/1.70  tff(c_688, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_78])).
% 4.01/1.70  tff(c_889, plain, (~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_886, c_688])).
% 4.01/1.70  tff(c_892, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_77, c_687, c_889])).
% 4.01/1.70  tff(c_894, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_892])).
% 4.01/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.70  
% 4.01/1.70  Inference rules
% 4.01/1.70  ----------------------
% 4.01/1.70  #Ref     : 0
% 4.01/1.70  #Sup     : 142
% 4.01/1.70  #Fact    : 0
% 4.01/1.70  #Define  : 0
% 4.01/1.70  #Split   : 7
% 4.01/1.70  #Chain   : 0
% 4.01/1.70  #Close   : 0
% 4.01/1.70  
% 4.01/1.70  Ordering : KBO
% 4.01/1.70  
% 4.01/1.70  Simplification rules
% 4.01/1.70  ----------------------
% 4.01/1.70  #Subsume      : 21
% 4.01/1.70  #Demod        : 178
% 4.01/1.70  #Tautology    : 16
% 4.01/1.70  #SimpNegUnit  : 60
% 4.01/1.70  #BackRed      : 0
% 4.01/1.70  
% 4.01/1.70  #Partial instantiations: 0
% 4.01/1.70  #Strategies tried      : 1
% 4.01/1.70  
% 4.01/1.70  Timing (in seconds)
% 4.01/1.70  ----------------------
% 4.01/1.70  Preprocessing        : 0.42
% 4.01/1.70  Parsing              : 0.23
% 4.01/1.70  CNF conversion       : 0.05
% 4.01/1.70  Main loop            : 0.45
% 4.01/1.70  Inferencing          : 0.17
% 4.01/1.70  Reduction            : 0.13
% 4.01/1.70  Demodulation         : 0.09
% 4.01/1.70  BG Simplification    : 0.03
% 4.01/1.70  Subsumption          : 0.09
% 4.01/1.70  Abstraction          : 0.02
% 4.01/1.70  MUC search           : 0.00
% 4.01/1.70  Cooper               : 0.00
% 4.01/1.70  Total                : 0.91
% 4.01/1.70  Index Insertion      : 0.00
% 4.01/1.70  Index Deletion       : 0.00
% 4.01/1.70  Index Matching       : 0.00
% 4.01/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
