%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:04 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.41s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 253 expanded)
%              Number of leaves         :   37 ( 113 expanded)
%              Depth                    :   15
%              Number of atoms          :  294 (1697 expanded)
%              Number of equality atoms :    6 (  90 expanded)
%              Maximal formula depth    :   26 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_connsp_2,type,(
    k1_connsp_2: ( $i * $i ) > $i )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_256,negated_conjecture,(
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

tff(f_53,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k1_connsp_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_2)).

tff(f_99,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r2_hidden(B,k1_connsp_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_connsp_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_124,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_117,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_213,axiom,(
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
                             => ( ( v3_pre_topc(E,B)
                                  & r2_hidden(F,E)
                                  & r1_tarski(E,u1_struct_0(D))
                                  & F = G )
                               => ( r1_tmap_1(B,A,C,F)
                                <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),G) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tmap_1)).

tff(f_164,axiom,(
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

tff(c_46,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_42,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_36,plain,(
    '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_74,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_40])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_56,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_54,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_97,plain,(
    ! [B_290,A_291] :
      ( v2_pre_topc(B_290)
      | ~ m1_pre_topc(B_290,A_291)
      | ~ l1_pre_topc(A_291)
      | ~ v2_pre_topc(A_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_100,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_97])).

tff(c_103,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_100])).

tff(c_82,plain,(
    ! [B_286,A_287] :
      ( l1_pre_topc(B_286)
      | ~ m1_pre_topc(B_286,A_287)
      | ~ l1_pre_topc(A_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_85,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_82])).

tff(c_88,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_85])).

tff(c_18,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(k1_connsp_2(A_23,B_24),k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ m1_subset_1(B_24,u1_struct_0(A_23))
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_116,plain,(
    ! [B_304,A_305] :
      ( r2_hidden(B_304,k1_connsp_2(A_305,B_304))
      | ~ m1_subset_1(B_304,u1_struct_0(A_305))
      | ~ l1_pre_topc(A_305)
      | ~ v2_pre_topc(A_305)
      | v2_struct_0(A_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_8,plain,(
    ! [C_6,A_3,B_4] :
      ( r2_hidden(C_6,A_3)
      | ~ r2_hidden(C_6,B_4)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_178,plain,(
    ! [B_328,A_329,A_330] :
      ( r2_hidden(B_328,A_329)
      | ~ m1_subset_1(k1_connsp_2(A_330,B_328),k1_zfmisc_1(A_329))
      | ~ m1_subset_1(B_328,u1_struct_0(A_330))
      | ~ l1_pre_topc(A_330)
      | ~ v2_pre_topc(A_330)
      | v2_struct_0(A_330) ) ),
    inference(resolution,[status(thm)],[c_116,c_8])).

tff(c_182,plain,(
    ! [B_24,A_23] :
      ( r2_hidden(B_24,u1_struct_0(A_23))
      | ~ m1_subset_1(B_24,u1_struct_0(A_23))
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(resolution,[status(thm)],[c_18,c_178])).

tff(c_44,plain,(
    v1_tsep_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_28,plain,(
    ! [B_37,A_35] :
      ( m1_subset_1(u1_struct_0(B_37),k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ m1_pre_topc(B_37,A_35)
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_150,plain,(
    ! [B_315,A_316] :
      ( v3_pre_topc(u1_struct_0(B_315),A_316)
      | ~ v1_tsep_1(B_315,A_316)
      | ~ m1_subset_1(u1_struct_0(B_315),k1_zfmisc_1(u1_struct_0(A_316)))
      | ~ m1_pre_topc(B_315,A_316)
      | ~ l1_pre_topc(A_316)
      | ~ v2_pre_topc(A_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_154,plain,(
    ! [B_37,A_35] :
      ( v3_pre_topc(u1_struct_0(B_37),A_35)
      | ~ v1_tsep_1(B_37,A_35)
      | ~ v2_pre_topc(A_35)
      | ~ m1_pre_topc(B_37,A_35)
      | ~ l1_pre_topc(A_35) ) ),
    inference(resolution,[status(thm)],[c_28,c_150])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_66,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6')
    | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_75,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6')
    | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_66])).

tff(c_96,plain,(
    ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_62,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_60,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_52,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_50,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_72,plain,
    ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_5')
    | r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_73,plain,
    ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
    | r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_72])).

tff(c_115,plain,(
    r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_73])).

tff(c_294,plain,(
    ! [C_364,G_361,E_365,D_363,A_360,B_362] :
      ( r1_tmap_1(B_362,A_360,C_364,G_361)
      | ~ r1_tmap_1(D_363,A_360,k2_tmap_1(B_362,A_360,C_364,D_363),G_361)
      | ~ r1_tarski(E_365,u1_struct_0(D_363))
      | ~ r2_hidden(G_361,E_365)
      | ~ v3_pre_topc(E_365,B_362)
      | ~ m1_subset_1(G_361,u1_struct_0(D_363))
      | ~ m1_subset_1(G_361,u1_struct_0(B_362))
      | ~ m1_subset_1(E_365,k1_zfmisc_1(u1_struct_0(B_362)))
      | ~ m1_pre_topc(D_363,B_362)
      | v2_struct_0(D_363)
      | ~ m1_subset_1(C_364,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_362),u1_struct_0(A_360))))
      | ~ v1_funct_2(C_364,u1_struct_0(B_362),u1_struct_0(A_360))
      | ~ v1_funct_1(C_364)
      | ~ l1_pre_topc(B_362)
      | ~ v2_pre_topc(B_362)
      | v2_struct_0(B_362)
      | ~ l1_pre_topc(A_360)
      | ~ v2_pre_topc(A_360)
      | v2_struct_0(A_360) ) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_296,plain,(
    ! [E_365] :
      ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
      | ~ r1_tarski(E_365,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_6',E_365)
      | ~ v3_pre_topc(E_365,'#skF_2')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_365,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_115,c_294])).

tff(c_299,plain,(
    ! [E_365] :
      ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
      | ~ r1_tarski(E_365,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_6',E_365)
      | ~ v3_pre_topc(E_365,'#skF_2')
      | ~ m1_subset_1(E_365,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_52,c_50,c_48,c_42,c_74,c_38,c_296])).

tff(c_314,plain,(
    ! [E_372] :
      ( ~ r1_tarski(E_372,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_6',E_372)
      | ~ v3_pre_topc(E_372,'#skF_2')
      | ~ m1_subset_1(E_372,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_46,c_96,c_299])).

tff(c_322,plain,(
    ! [B_37] :
      ( ~ r1_tarski(u1_struct_0(B_37),u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_6',u1_struct_0(B_37))
      | ~ v3_pre_topc(u1_struct_0(B_37),'#skF_2')
      | ~ m1_pre_topc(B_37,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_314])).

tff(c_330,plain,(
    ! [B_373] :
      ( ~ r1_tarski(u1_struct_0(B_373),u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_6',u1_struct_0(B_373))
      | ~ v3_pre_topc(u1_struct_0(B_373),'#skF_2')
      | ~ m1_pre_topc(B_373,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_322])).

tff(c_334,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_4'))
    | ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_330])).

tff(c_337,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_4'))
    | ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_334])).

tff(c_338,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_337])).

tff(c_341,plain,
    ( ~ v1_tsep_1('#skF_4','#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_154,c_338])).

tff(c_345,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_42,c_56,c_44,c_341])).

tff(c_346,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_337])).

tff(c_365,plain,
    ( ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_182,c_346])).

tff(c_377,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_88,c_38,c_365])).

tff(c_379,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_377])).

tff(c_381,plain,(
    r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_590,plain,(
    ! [A_448,D_450,F_451,C_449,B_452] :
      ( r1_tmap_1(D_450,A_448,k2_tmap_1(B_452,A_448,C_449,D_450),F_451)
      | ~ r1_tmap_1(B_452,A_448,C_449,F_451)
      | ~ m1_subset_1(F_451,u1_struct_0(D_450))
      | ~ m1_subset_1(F_451,u1_struct_0(B_452))
      | ~ m1_pre_topc(D_450,B_452)
      | v2_struct_0(D_450)
      | ~ m1_subset_1(C_449,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_452),u1_struct_0(A_448))))
      | ~ v1_funct_2(C_449,u1_struct_0(B_452),u1_struct_0(A_448))
      | ~ v1_funct_1(C_449)
      | ~ l1_pre_topc(B_452)
      | ~ v2_pre_topc(B_452)
      | v2_struct_0(B_452)
      | ~ l1_pre_topc(A_448)
      | ~ v2_pre_topc(A_448)
      | v2_struct_0(A_448) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_592,plain,(
    ! [D_450,F_451] :
      ( r1_tmap_1(D_450,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_450),F_451)
      | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3',F_451)
      | ~ m1_subset_1(F_451,u1_struct_0(D_450))
      | ~ m1_subset_1(F_451,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_450,'#skF_2')
      | v2_struct_0(D_450)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_590])).

tff(c_595,plain,(
    ! [D_450,F_451] :
      ( r1_tmap_1(D_450,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_450),F_451)
      | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3',F_451)
      | ~ m1_subset_1(F_451,u1_struct_0(D_450))
      | ~ m1_subset_1(F_451,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_450,'#skF_2')
      | v2_struct_0(D_450)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_52,c_50,c_592])).

tff(c_604,plain,(
    ! [D_459,F_460] :
      ( r1_tmap_1(D_459,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_459),F_460)
      | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3',F_460)
      | ~ m1_subset_1(F_460,u1_struct_0(D_459))
      | ~ m1_subset_1(F_460,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_459,'#skF_2')
      | v2_struct_0(D_459) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_595])).

tff(c_380,plain,(
    ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_607,plain,
    ( ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_604,c_380])).

tff(c_610,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_74,c_38,c_381,c_607])).

tff(c_612,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_610])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:54:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.48  
% 3.23/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.49  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.23/1.49  
% 3.23/1.49  %Foreground sorts:
% 3.23/1.49  
% 3.23/1.49  
% 3.23/1.49  %Background operators:
% 3.23/1.49  
% 3.23/1.49  
% 3.23/1.49  %Foreground operators:
% 3.23/1.49  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.23/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.23/1.49  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.23/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.23/1.49  tff(k1_connsp_2, type, k1_connsp_2: ($i * $i) > $i).
% 3.23/1.49  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.23/1.49  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.23/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.23/1.49  tff('#skF_5', type, '#skF_5': $i).
% 3.23/1.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.23/1.49  tff('#skF_6', type, '#skF_6': $i).
% 3.23/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.23/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.23/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.23/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.23/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.23/1.49  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.23/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.23/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.49  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.23/1.49  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.23/1.49  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.23/1.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.23/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.23/1.49  
% 3.41/1.51  tff(f_256, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_tmap_1)).
% 3.41/1.51  tff(f_53, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.41/1.51  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.41/1.51  tff(f_87, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k1_connsp_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_connsp_2)).
% 3.41/1.51  tff(f_99, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r2_hidden(B, k1_connsp_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_connsp_2)).
% 3.41/1.51  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.41/1.51  tff(f_124, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.41/1.51  tff(f_117, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 3.41/1.51  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.41/1.51  tff(f_213, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((v3_pre_topc(E, B) & r2_hidden(F, E)) & r1_tarski(E, u1_struct_0(D))) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tmap_1)).
% 3.41/1.51  tff(f_164, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 3.41/1.51  tff(c_46, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_256])).
% 3.41/1.51  tff(c_42, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_256])).
% 3.41/1.51  tff(c_36, plain, ('#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_256])).
% 3.41/1.51  tff(c_40, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_256])).
% 3.41/1.51  tff(c_74, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_40])).
% 3.41/1.51  tff(c_38, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_256])).
% 3.41/1.51  tff(c_56, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_256])).
% 3.41/1.51  tff(c_54, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_256])).
% 3.41/1.51  tff(c_97, plain, (![B_290, A_291]: (v2_pre_topc(B_290) | ~m1_pre_topc(B_290, A_291) | ~l1_pre_topc(A_291) | ~v2_pre_topc(A_291))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.41/1.51  tff(c_100, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_97])).
% 3.41/1.51  tff(c_103, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_100])).
% 3.41/1.51  tff(c_82, plain, (![B_286, A_287]: (l1_pre_topc(B_286) | ~m1_pre_topc(B_286, A_287) | ~l1_pre_topc(A_287))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.41/1.51  tff(c_85, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_82])).
% 3.41/1.51  tff(c_88, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_85])).
% 3.41/1.51  tff(c_18, plain, (![A_23, B_24]: (m1_subset_1(k1_connsp_2(A_23, B_24), k1_zfmisc_1(u1_struct_0(A_23))) | ~m1_subset_1(B_24, u1_struct_0(A_23)) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.41/1.51  tff(c_116, plain, (![B_304, A_305]: (r2_hidden(B_304, k1_connsp_2(A_305, B_304)) | ~m1_subset_1(B_304, u1_struct_0(A_305)) | ~l1_pre_topc(A_305) | ~v2_pre_topc(A_305) | v2_struct_0(A_305))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.41/1.51  tff(c_8, plain, (![C_6, A_3, B_4]: (r2_hidden(C_6, A_3) | ~r2_hidden(C_6, B_4) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.41/1.51  tff(c_178, plain, (![B_328, A_329, A_330]: (r2_hidden(B_328, A_329) | ~m1_subset_1(k1_connsp_2(A_330, B_328), k1_zfmisc_1(A_329)) | ~m1_subset_1(B_328, u1_struct_0(A_330)) | ~l1_pre_topc(A_330) | ~v2_pre_topc(A_330) | v2_struct_0(A_330))), inference(resolution, [status(thm)], [c_116, c_8])).
% 3.41/1.51  tff(c_182, plain, (![B_24, A_23]: (r2_hidden(B_24, u1_struct_0(A_23)) | ~m1_subset_1(B_24, u1_struct_0(A_23)) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(resolution, [status(thm)], [c_18, c_178])).
% 3.41/1.51  tff(c_44, plain, (v1_tsep_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_256])).
% 3.41/1.51  tff(c_28, plain, (![B_37, A_35]: (m1_subset_1(u1_struct_0(B_37), k1_zfmisc_1(u1_struct_0(A_35))) | ~m1_pre_topc(B_37, A_35) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.41/1.51  tff(c_150, plain, (![B_315, A_316]: (v3_pre_topc(u1_struct_0(B_315), A_316) | ~v1_tsep_1(B_315, A_316) | ~m1_subset_1(u1_struct_0(B_315), k1_zfmisc_1(u1_struct_0(A_316))) | ~m1_pre_topc(B_315, A_316) | ~l1_pre_topc(A_316) | ~v2_pre_topc(A_316))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.41/1.51  tff(c_154, plain, (![B_37, A_35]: (v3_pre_topc(u1_struct_0(B_37), A_35) | ~v1_tsep_1(B_37, A_35) | ~v2_pre_topc(A_35) | ~m1_pre_topc(B_37, A_35) | ~l1_pre_topc(A_35))), inference(resolution, [status(thm)], [c_28, c_150])).
% 3.41/1.51  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.41/1.51  tff(c_64, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_256])).
% 3.41/1.51  tff(c_58, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_256])).
% 3.41/1.51  tff(c_66, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6') | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_256])).
% 3.41/1.51  tff(c_75, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6') | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_66])).
% 3.41/1.51  tff(c_96, plain, (~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(splitLeft, [status(thm)], [c_75])).
% 3.41/1.51  tff(c_62, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_256])).
% 3.41/1.51  tff(c_60, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_256])).
% 3.41/1.51  tff(c_52, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_256])).
% 3.41/1.51  tff(c_50, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_256])).
% 3.41/1.51  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_256])).
% 3.41/1.51  tff(c_72, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_5') | r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_256])).
% 3.41/1.51  tff(c_73, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_72])).
% 3.41/1.51  tff(c_115, plain, (r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_96, c_73])).
% 3.41/1.51  tff(c_294, plain, (![C_364, G_361, E_365, D_363, A_360, B_362]: (r1_tmap_1(B_362, A_360, C_364, G_361) | ~r1_tmap_1(D_363, A_360, k2_tmap_1(B_362, A_360, C_364, D_363), G_361) | ~r1_tarski(E_365, u1_struct_0(D_363)) | ~r2_hidden(G_361, E_365) | ~v3_pre_topc(E_365, B_362) | ~m1_subset_1(G_361, u1_struct_0(D_363)) | ~m1_subset_1(G_361, u1_struct_0(B_362)) | ~m1_subset_1(E_365, k1_zfmisc_1(u1_struct_0(B_362))) | ~m1_pre_topc(D_363, B_362) | v2_struct_0(D_363) | ~m1_subset_1(C_364, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_362), u1_struct_0(A_360)))) | ~v1_funct_2(C_364, u1_struct_0(B_362), u1_struct_0(A_360)) | ~v1_funct_1(C_364) | ~l1_pre_topc(B_362) | ~v2_pre_topc(B_362) | v2_struct_0(B_362) | ~l1_pre_topc(A_360) | ~v2_pre_topc(A_360) | v2_struct_0(A_360))), inference(cnfTransformation, [status(thm)], [f_213])).
% 3.41/1.51  tff(c_296, plain, (![E_365]: (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | ~r1_tarski(E_365, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_6', E_365) | ~v3_pre_topc(E_365, '#skF_2') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | ~m1_subset_1(E_365, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_115, c_294])).
% 3.41/1.51  tff(c_299, plain, (![E_365]: (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | ~r1_tarski(E_365, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_6', E_365) | ~v3_pre_topc(E_365, '#skF_2') | ~m1_subset_1(E_365, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_52, c_50, c_48, c_42, c_74, c_38, c_296])).
% 3.41/1.51  tff(c_314, plain, (![E_372]: (~r1_tarski(E_372, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_6', E_372) | ~v3_pre_topc(E_372, '#skF_2') | ~m1_subset_1(E_372, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_46, c_96, c_299])).
% 3.41/1.51  tff(c_322, plain, (![B_37]: (~r1_tarski(u1_struct_0(B_37), u1_struct_0('#skF_4')) | ~r2_hidden('#skF_6', u1_struct_0(B_37)) | ~v3_pre_topc(u1_struct_0(B_37), '#skF_2') | ~m1_pre_topc(B_37, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_314])).
% 3.41/1.51  tff(c_330, plain, (![B_373]: (~r1_tarski(u1_struct_0(B_373), u1_struct_0('#skF_4')) | ~r2_hidden('#skF_6', u1_struct_0(B_373)) | ~v3_pre_topc(u1_struct_0(B_373), '#skF_2') | ~m1_pre_topc(B_373, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_322])).
% 3.41/1.51  tff(c_334, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_4')) | ~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_6, c_330])).
% 3.41/1.51  tff(c_337, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_4')) | ~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_334])).
% 3.41/1.51  tff(c_338, plain, (~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_2')), inference(splitLeft, [status(thm)], [c_337])).
% 3.41/1.51  tff(c_341, plain, (~v1_tsep_1('#skF_4', '#skF_2') | ~v2_pre_topc('#skF_2') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_154, c_338])).
% 3.41/1.51  tff(c_345, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_42, c_56, c_44, c_341])).
% 3.41/1.51  tff(c_346, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_337])).
% 3.41/1.51  tff(c_365, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_182, c_346])).
% 3.41/1.51  tff(c_377, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_88, c_38, c_365])).
% 3.41/1.51  tff(c_379, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_377])).
% 3.41/1.51  tff(c_381, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(splitRight, [status(thm)], [c_75])).
% 3.41/1.51  tff(c_590, plain, (![A_448, D_450, F_451, C_449, B_452]: (r1_tmap_1(D_450, A_448, k2_tmap_1(B_452, A_448, C_449, D_450), F_451) | ~r1_tmap_1(B_452, A_448, C_449, F_451) | ~m1_subset_1(F_451, u1_struct_0(D_450)) | ~m1_subset_1(F_451, u1_struct_0(B_452)) | ~m1_pre_topc(D_450, B_452) | v2_struct_0(D_450) | ~m1_subset_1(C_449, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_452), u1_struct_0(A_448)))) | ~v1_funct_2(C_449, u1_struct_0(B_452), u1_struct_0(A_448)) | ~v1_funct_1(C_449) | ~l1_pre_topc(B_452) | ~v2_pre_topc(B_452) | v2_struct_0(B_452) | ~l1_pre_topc(A_448) | ~v2_pre_topc(A_448) | v2_struct_0(A_448))), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.41/1.51  tff(c_592, plain, (![D_450, F_451]: (r1_tmap_1(D_450, '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', D_450), F_451) | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', F_451) | ~m1_subset_1(F_451, u1_struct_0(D_450)) | ~m1_subset_1(F_451, u1_struct_0('#skF_2')) | ~m1_pre_topc(D_450, '#skF_2') | v2_struct_0(D_450) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_590])).
% 3.41/1.51  tff(c_595, plain, (![D_450, F_451]: (r1_tmap_1(D_450, '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', D_450), F_451) | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', F_451) | ~m1_subset_1(F_451, u1_struct_0(D_450)) | ~m1_subset_1(F_451, u1_struct_0('#skF_2')) | ~m1_pre_topc(D_450, '#skF_2') | v2_struct_0(D_450) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_52, c_50, c_592])).
% 3.41/1.51  tff(c_604, plain, (![D_459, F_460]: (r1_tmap_1(D_459, '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', D_459), F_460) | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', F_460) | ~m1_subset_1(F_460, u1_struct_0(D_459)) | ~m1_subset_1(F_460, u1_struct_0('#skF_2')) | ~m1_pre_topc(D_459, '#skF_2') | v2_struct_0(D_459))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_595])).
% 3.41/1.51  tff(c_380, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(splitRight, [status(thm)], [c_75])).
% 3.41/1.51  tff(c_607, plain, (~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_604, c_380])).
% 3.41/1.51  tff(c_610, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_74, c_38, c_381, c_607])).
% 3.41/1.51  tff(c_612, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_610])).
% 3.41/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.41/1.51  
% 3.41/1.51  Inference rules
% 3.41/1.51  ----------------------
% 3.41/1.51  #Ref     : 0
% 3.41/1.51  #Sup     : 99
% 3.41/1.51  #Fact    : 0
% 3.41/1.51  #Define  : 0
% 3.41/1.51  #Split   : 2
% 3.41/1.51  #Chain   : 0
% 3.41/1.51  #Close   : 0
% 3.41/1.51  
% 3.41/1.51  Ordering : KBO
% 3.41/1.51  
% 3.41/1.51  Simplification rules
% 3.41/1.51  ----------------------
% 3.41/1.51  #Subsume      : 20
% 3.41/1.51  #Demod        : 106
% 3.41/1.51  #Tautology    : 21
% 3.41/1.51  #SimpNegUnit  : 30
% 3.41/1.51  #BackRed      : 0
% 3.41/1.51  
% 3.41/1.51  #Partial instantiations: 0
% 3.41/1.51  #Strategies tried      : 1
% 3.41/1.51  
% 3.41/1.51  Timing (in seconds)
% 3.41/1.51  ----------------------
% 3.41/1.51  Preprocessing        : 0.38
% 3.41/1.51  Parsing              : 0.19
% 3.41/1.51  CNF conversion       : 0.05
% 3.41/1.51  Main loop            : 0.36
% 3.41/1.51  Inferencing          : 0.14
% 3.41/1.51  Reduction            : 0.11
% 3.41/1.51  Demodulation         : 0.07
% 3.41/1.51  BG Simplification    : 0.02
% 3.41/1.51  Subsumption          : 0.07
% 3.41/1.51  Abstraction          : 0.01
% 3.41/1.51  MUC search           : 0.00
% 3.41/1.51  Cooper               : 0.00
% 3.41/1.51  Total                : 0.78
% 3.41/1.51  Index Insertion      : 0.00
% 3.41/1.51  Index Deletion       : 0.00
% 3.41/1.51  Index Matching       : 0.00
% 3.41/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
