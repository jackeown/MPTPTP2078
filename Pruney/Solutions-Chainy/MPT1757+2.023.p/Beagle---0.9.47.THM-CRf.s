%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:07 EST 2020

% Result     : Theorem 3.99s
% Output     : CNFRefutation 3.99s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 482 expanded)
%              Number of leaves         :   40 ( 202 expanded)
%              Depth                    :   20
%              Number of atoms          :  364 (3500 expanded)
%              Number of equality atoms :    5 ( 170 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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

tff(f_268,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tmap_1)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_138,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_131,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

tff(f_113,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ~ ( r2_hidden(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( m1_connsp_2(D,A,C)
                            & r1_tarski(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_connsp_2)).

tff(f_225,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tmap_1)).

tff(f_178,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_64,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_52,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_91,plain,(
    ! [B_302,A_303] :
      ( l1_pre_topc(B_302)
      | ~ m1_pre_topc(B_302,A_303)
      | ~ l1_pre_topc(A_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_94,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_91])).

tff(c_97,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_94])).

tff(c_10,plain,(
    ! [A_3] :
      ( l1_struct_0(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_46,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_50,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_84,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_50])).

tff(c_48,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_100,plain,(
    ! [B_307,A_308] :
      ( v1_xboole_0(B_307)
      | ~ m1_subset_1(B_307,A_308)
      | ~ v1_xboole_0(A_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_116,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_48,c_100])).

tff(c_118,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r2_hidden(B_2,A_1)
      | ~ m1_subset_1(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_66,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_54,plain,(
    v1_tsep_1('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_38,plain,(
    ! [B_53,A_51] :
      ( m1_subset_1(u1_struct_0(B_53),k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ m1_pre_topc(B_53,A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_199,plain,(
    ! [B_334,A_335] :
      ( v3_pre_topc(u1_struct_0(B_334),A_335)
      | ~ v1_tsep_1(B_334,A_335)
      | ~ m1_subset_1(u1_struct_0(B_334),k1_zfmisc_1(u1_struct_0(A_335)))
      | ~ m1_pre_topc(B_334,A_335)
      | ~ l1_pre_topc(A_335)
      | ~ v2_pre_topc(A_335) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_206,plain,(
    ! [B_53,A_51] :
      ( v3_pre_topc(u1_struct_0(B_53),A_51)
      | ~ v1_tsep_1(B_53,A_51)
      | ~ v2_pre_topc(A_51)
      | ~ m1_pre_topc(B_53,A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_38,c_199])).

tff(c_237,plain,(
    ! [A_348,B_349,C_350] :
      ( r1_tarski('#skF_1'(A_348,B_349,C_350),B_349)
      | ~ r2_hidden(C_350,B_349)
      | ~ m1_subset_1(C_350,u1_struct_0(A_348))
      | ~ v3_pre_topc(B_349,A_348)
      | ~ m1_subset_1(B_349,k1_zfmisc_1(u1_struct_0(A_348)))
      | ~ l1_pre_topc(A_348)
      | ~ v2_pre_topc(A_348)
      | v2_struct_0(A_348) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_243,plain,(
    ! [A_51,B_53,C_350] :
      ( r1_tarski('#skF_1'(A_51,u1_struct_0(B_53),C_350),u1_struct_0(B_53))
      | ~ r2_hidden(C_350,u1_struct_0(B_53))
      | ~ m1_subset_1(C_350,u1_struct_0(A_51))
      | ~ v3_pre_topc(u1_struct_0(B_53),A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51)
      | ~ m1_pre_topc(B_53,A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_38,c_237])).

tff(c_30,plain,(
    ! [A_19,B_33,C_40] :
      ( m1_subset_1('#skF_1'(A_19,B_33,C_40),k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ r2_hidden(C_40,B_33)
      | ~ m1_subset_1(C_40,u1_struct_0(A_19))
      | ~ v3_pre_topc(B_33,A_19)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_82,plain,
    ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_7')
    | r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_83,plain,
    ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
    | r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_82])).

tff(c_126,plain,(
    r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_76,plain,
    ( ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_85,plain,
    ( ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_76])).

tff(c_134,plain,(
    ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_85])).

tff(c_72,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_70,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_60,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_358,plain,(
    ! [C_401,E_397,D_398,A_400,G_399,B_396] :
      ( r1_tmap_1(B_396,A_400,C_401,G_399)
      | ~ r1_tmap_1(D_398,A_400,k2_tmap_1(B_396,A_400,C_401,D_398),G_399)
      | ~ m1_connsp_2(E_397,B_396,G_399)
      | ~ r1_tarski(E_397,u1_struct_0(D_398))
      | ~ m1_subset_1(G_399,u1_struct_0(D_398))
      | ~ m1_subset_1(G_399,u1_struct_0(B_396))
      | ~ m1_subset_1(E_397,k1_zfmisc_1(u1_struct_0(B_396)))
      | ~ m1_pre_topc(D_398,B_396)
      | v2_struct_0(D_398)
      | ~ m1_subset_1(C_401,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_396),u1_struct_0(A_400))))
      | ~ v1_funct_2(C_401,u1_struct_0(B_396),u1_struct_0(A_400))
      | ~ v1_funct_1(C_401)
      | ~ l1_pre_topc(B_396)
      | ~ v2_pre_topc(B_396)
      | v2_struct_0(B_396)
      | ~ l1_pre_topc(A_400)
      | ~ v2_pre_topc(A_400)
      | v2_struct_0(A_400) ) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_362,plain,(
    ! [E_397] :
      ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
      | ~ m1_connsp_2(E_397,'#skF_4','#skF_8')
      | ~ r1_tarski(E_397,u1_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_397,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_6','#skF_4')
      | v2_struct_0('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_126,c_358])).

tff(c_369,plain,(
    ! [E_397] :
      ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
      | ~ m1_connsp_2(E_397,'#skF_4','#skF_8')
      | ~ r1_tarski(E_397,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(E_397,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_62,c_60,c_58,c_52,c_84,c_48,c_362])).

tff(c_371,plain,(
    ! [E_402] :
      ( ~ m1_connsp_2(E_402,'#skF_4','#skF_8')
      | ~ r1_tarski(E_402,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(E_402,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_56,c_134,c_369])).

tff(c_375,plain,(
    ! [B_33,C_40] :
      ( ~ m1_connsp_2('#skF_1'('#skF_4',B_33,C_40),'#skF_4','#skF_8')
      | ~ r1_tarski('#skF_1'('#skF_4',B_33,C_40),u1_struct_0('#skF_6'))
      | ~ r2_hidden(C_40,B_33)
      | ~ m1_subset_1(C_40,u1_struct_0('#skF_4'))
      | ~ v3_pre_topc(B_33,'#skF_4')
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_371])).

tff(c_386,plain,(
    ! [B_33,C_40] :
      ( ~ m1_connsp_2('#skF_1'('#skF_4',B_33,C_40),'#skF_4','#skF_8')
      | ~ r1_tarski('#skF_1'('#skF_4',B_33,C_40),u1_struct_0('#skF_6'))
      | ~ r2_hidden(C_40,B_33)
      | ~ m1_subset_1(C_40,u1_struct_0('#skF_4'))
      | ~ v3_pre_topc(B_33,'#skF_4')
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_375])).

tff(c_393,plain,(
    ! [B_404,C_405] :
      ( ~ m1_connsp_2('#skF_1'('#skF_4',B_404,C_405),'#skF_4','#skF_8')
      | ~ r1_tarski('#skF_1'('#skF_4',B_404,C_405),u1_struct_0('#skF_6'))
      | ~ r2_hidden(C_405,B_404)
      | ~ m1_subset_1(C_405,u1_struct_0('#skF_4'))
      | ~ v3_pre_topc(B_404,'#skF_4')
      | ~ m1_subset_1(B_404,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_386])).

tff(c_397,plain,(
    ! [C_350] :
      ( ~ m1_connsp_2('#skF_1'('#skF_4',u1_struct_0('#skF_6'),C_350),'#skF_4','#skF_8')
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(C_350,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(C_350,u1_struct_0('#skF_4'))
      | ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_6','#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_243,c_393])).

tff(c_400,plain,(
    ! [C_350] :
      ( ~ m1_connsp_2('#skF_1'('#skF_4',u1_struct_0('#skF_6'),C_350),'#skF_4','#skF_8')
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(C_350,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(C_350,u1_struct_0('#skF_4'))
      | ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_52,c_66,c_397])).

tff(c_401,plain,(
    ! [C_350] :
      ( ~ m1_connsp_2('#skF_1'('#skF_4',u1_struct_0('#skF_6'),C_350),'#skF_4','#skF_8')
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(C_350,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(C_350,u1_struct_0('#skF_4'))
      | ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_400])).

tff(c_402,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_401])).

tff(c_405,plain,
    ( ~ v1_tsep_1('#skF_6','#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_206,c_402])).

tff(c_409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_52,c_66,c_54,c_405])).

tff(c_411,plain,(
    v3_pre_topc(u1_struct_0('#skF_6'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_401])).

tff(c_257,plain,(
    ! [A_357,B_358,C_359] :
      ( m1_connsp_2('#skF_1'(A_357,B_358,C_359),A_357,C_359)
      | ~ r2_hidden(C_359,B_358)
      | ~ m1_subset_1(C_359,u1_struct_0(A_357))
      | ~ v3_pre_topc(B_358,A_357)
      | ~ m1_subset_1(B_358,k1_zfmisc_1(u1_struct_0(A_357)))
      | ~ l1_pre_topc(A_357)
      | ~ v2_pre_topc(A_357)
      | v2_struct_0(A_357) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_263,plain,(
    ! [A_51,B_53,C_359] :
      ( m1_connsp_2('#skF_1'(A_51,u1_struct_0(B_53),C_359),A_51,C_359)
      | ~ r2_hidden(C_359,u1_struct_0(B_53))
      | ~ m1_subset_1(C_359,u1_struct_0(A_51))
      | ~ v3_pre_topc(u1_struct_0(B_53),A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51)
      | ~ m1_pre_topc(B_53,A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_38,c_257])).

tff(c_410,plain,(
    ! [C_350] :
      ( ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_connsp_2('#skF_1'('#skF_4',u1_struct_0('#skF_6'),C_350),'#skF_4','#skF_8')
      | ~ r2_hidden(C_350,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(C_350,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_401])).

tff(c_418,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_410])).

tff(c_421,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_418])).

tff(c_428,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_52,c_421])).

tff(c_485,plain,(
    ! [C_410] :
      ( ~ m1_connsp_2('#skF_1'('#skF_4',u1_struct_0('#skF_6'),C_410),'#skF_4','#skF_8')
      | ~ r2_hidden(C_410,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(C_410,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_410])).

tff(c_493,plain,
    ( ~ r2_hidden('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_263,c_485])).

tff(c_499,plain,
    ( ~ r2_hidden('#skF_8',u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_52,c_66,c_411,c_84,c_493])).

tff(c_500,plain,(
    ~ r2_hidden('#skF_8',u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_499])).

tff(c_503,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_4,c_500])).

tff(c_506,plain,(
    v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_503])).

tff(c_508,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_506])).

tff(c_509,plain,(
    r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_686,plain,(
    ! [C_479,F_482,D_481,B_478,A_480] :
      ( r1_tmap_1(D_481,A_480,k2_tmap_1(B_478,A_480,C_479,D_481),F_482)
      | ~ r1_tmap_1(B_478,A_480,C_479,F_482)
      | ~ m1_subset_1(F_482,u1_struct_0(D_481))
      | ~ m1_subset_1(F_482,u1_struct_0(B_478))
      | ~ m1_pre_topc(D_481,B_478)
      | v2_struct_0(D_481)
      | ~ m1_subset_1(C_479,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_478),u1_struct_0(A_480))))
      | ~ v1_funct_2(C_479,u1_struct_0(B_478),u1_struct_0(A_480))
      | ~ v1_funct_1(C_479)
      | ~ l1_pre_topc(B_478)
      | ~ v2_pre_topc(B_478)
      | v2_struct_0(B_478)
      | ~ l1_pre_topc(A_480)
      | ~ v2_pre_topc(A_480)
      | v2_struct_0(A_480) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_688,plain,(
    ! [D_481,F_482] :
      ( r1_tmap_1(D_481,'#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5',D_481),F_482)
      | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5',F_482)
      | ~ m1_subset_1(F_482,u1_struct_0(D_481))
      | ~ m1_subset_1(F_482,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_481,'#skF_4')
      | v2_struct_0(D_481)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_58,c_686])).

tff(c_694,plain,(
    ! [D_481,F_482] :
      ( r1_tmap_1(D_481,'#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5',D_481),F_482)
      | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5',F_482)
      | ~ m1_subset_1(F_482,u1_struct_0(D_481))
      | ~ m1_subset_1(F_482,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_481,'#skF_4')
      | v2_struct_0(D_481)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_62,c_60,c_688])).

tff(c_697,plain,(
    ! [D_483,F_484] :
      ( r1_tmap_1(D_483,'#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5',D_483),F_484)
      | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5',F_484)
      | ~ m1_subset_1(F_484,u1_struct_0(D_483))
      | ~ m1_subset_1(F_484,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_483,'#skF_4')
      | v2_struct_0(D_483) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_694])).

tff(c_510,plain,(
    ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_700,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_697,c_510])).

tff(c_703,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_84,c_48,c_509,c_700])).

tff(c_705,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_703])).

tff(c_707,plain,(
    v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_14,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0(u1_struct_0(A_7))
      | ~ l1_struct_0(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_710,plain,
    ( ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_707,c_14])).

tff(c_713,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_710])).

tff(c_716,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_10,c_713])).

tff(c_720,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_716])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:25:32 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.99/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.99/1.72  
% 3.99/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.99/1.72  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2
% 3.99/1.72  
% 3.99/1.72  %Foreground sorts:
% 3.99/1.72  
% 3.99/1.72  
% 3.99/1.72  %Background operators:
% 3.99/1.72  
% 3.99/1.72  
% 3.99/1.72  %Foreground operators:
% 3.99/1.72  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.99/1.72  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.99/1.72  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.99/1.72  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.99/1.72  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.99/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.99/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.99/1.72  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.99/1.72  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.99/1.72  tff('#skF_7', type, '#skF_7': $i).
% 3.99/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.99/1.72  tff('#skF_5', type, '#skF_5': $i).
% 3.99/1.72  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.99/1.72  tff('#skF_6', type, '#skF_6': $i).
% 3.99/1.72  tff('#skF_3', type, '#skF_3': $i).
% 3.99/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.99/1.72  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.99/1.72  tff('#skF_8', type, '#skF_8': $i).
% 3.99/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.99/1.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.99/1.72  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.99/1.72  tff('#skF_4', type, '#skF_4': $i).
% 3.99/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.99/1.72  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.99/1.72  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.99/1.72  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.99/1.72  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.99/1.72  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.99/1.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.99/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.99/1.72  
% 3.99/1.74  tff(f_268, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_tmap_1)).
% 3.99/1.74  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.99/1.74  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.99/1.74  tff(f_38, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.99/1.74  tff(f_138, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.99/1.74  tff(f_131, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 3.99/1.74  tff(f_113, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(D, A, C) & r1_tarski(D, B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_connsp_2)).
% 3.99/1.74  tff(f_225, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tmap_1)).
% 3.99/1.74  tff(f_178, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tmap_1)).
% 3.99/1.74  tff(f_57, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.99/1.74  tff(c_64, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_268])).
% 3.99/1.74  tff(c_52, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_268])).
% 3.99/1.74  tff(c_91, plain, (![B_302, A_303]: (l1_pre_topc(B_302) | ~m1_pre_topc(B_302, A_303) | ~l1_pre_topc(A_303))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.99/1.74  tff(c_94, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_52, c_91])).
% 3.99/1.74  tff(c_97, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_94])).
% 3.99/1.74  tff(c_10, plain, (![A_3]: (l1_struct_0(A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.99/1.74  tff(c_56, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_268])).
% 3.99/1.74  tff(c_46, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_268])).
% 3.99/1.74  tff(c_50, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_268])).
% 3.99/1.74  tff(c_84, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_50])).
% 3.99/1.74  tff(c_48, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_268])).
% 3.99/1.74  tff(c_100, plain, (![B_307, A_308]: (v1_xboole_0(B_307) | ~m1_subset_1(B_307, A_308) | ~v1_xboole_0(A_308))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.99/1.74  tff(c_116, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0(u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_48, c_100])).
% 3.99/1.74  tff(c_118, plain, (~v1_xboole_0(u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_116])).
% 3.99/1.74  tff(c_4, plain, (![B_2, A_1]: (r2_hidden(B_2, A_1) | ~m1_subset_1(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.99/1.74  tff(c_68, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_268])).
% 3.99/1.74  tff(c_66, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_268])).
% 3.99/1.74  tff(c_54, plain, (v1_tsep_1('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_268])).
% 3.99/1.74  tff(c_38, plain, (![B_53, A_51]: (m1_subset_1(u1_struct_0(B_53), k1_zfmisc_1(u1_struct_0(A_51))) | ~m1_pre_topc(B_53, A_51) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.99/1.74  tff(c_199, plain, (![B_334, A_335]: (v3_pre_topc(u1_struct_0(B_334), A_335) | ~v1_tsep_1(B_334, A_335) | ~m1_subset_1(u1_struct_0(B_334), k1_zfmisc_1(u1_struct_0(A_335))) | ~m1_pre_topc(B_334, A_335) | ~l1_pre_topc(A_335) | ~v2_pre_topc(A_335))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.99/1.74  tff(c_206, plain, (![B_53, A_51]: (v3_pre_topc(u1_struct_0(B_53), A_51) | ~v1_tsep_1(B_53, A_51) | ~v2_pre_topc(A_51) | ~m1_pre_topc(B_53, A_51) | ~l1_pre_topc(A_51))), inference(resolution, [status(thm)], [c_38, c_199])).
% 3.99/1.74  tff(c_237, plain, (![A_348, B_349, C_350]: (r1_tarski('#skF_1'(A_348, B_349, C_350), B_349) | ~r2_hidden(C_350, B_349) | ~m1_subset_1(C_350, u1_struct_0(A_348)) | ~v3_pre_topc(B_349, A_348) | ~m1_subset_1(B_349, k1_zfmisc_1(u1_struct_0(A_348))) | ~l1_pre_topc(A_348) | ~v2_pre_topc(A_348) | v2_struct_0(A_348))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.99/1.74  tff(c_243, plain, (![A_51, B_53, C_350]: (r1_tarski('#skF_1'(A_51, u1_struct_0(B_53), C_350), u1_struct_0(B_53)) | ~r2_hidden(C_350, u1_struct_0(B_53)) | ~m1_subset_1(C_350, u1_struct_0(A_51)) | ~v3_pre_topc(u1_struct_0(B_53), A_51) | ~v2_pre_topc(A_51) | v2_struct_0(A_51) | ~m1_pre_topc(B_53, A_51) | ~l1_pre_topc(A_51))), inference(resolution, [status(thm)], [c_38, c_237])).
% 3.99/1.74  tff(c_30, plain, (![A_19, B_33, C_40]: (m1_subset_1('#skF_1'(A_19, B_33, C_40), k1_zfmisc_1(u1_struct_0(A_19))) | ~r2_hidden(C_40, B_33) | ~m1_subset_1(C_40, u1_struct_0(A_19)) | ~v3_pre_topc(B_33, A_19) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.99/1.74  tff(c_74, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_268])).
% 3.99/1.74  tff(c_82, plain, (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_7') | r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_268])).
% 3.99/1.74  tff(c_83, plain, (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_82])).
% 3.99/1.74  tff(c_126, plain, (r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(splitLeft, [status(thm)], [c_83])).
% 3.99/1.74  tff(c_76, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_268])).
% 3.99/1.74  tff(c_85, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_76])).
% 3.99/1.74  tff(c_134, plain, (~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_85])).
% 3.99/1.74  tff(c_72, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_268])).
% 3.99/1.74  tff(c_70, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_268])).
% 3.99/1.74  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_268])).
% 3.99/1.74  tff(c_60, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_268])).
% 3.99/1.74  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_268])).
% 3.99/1.74  tff(c_358, plain, (![C_401, E_397, D_398, A_400, G_399, B_396]: (r1_tmap_1(B_396, A_400, C_401, G_399) | ~r1_tmap_1(D_398, A_400, k2_tmap_1(B_396, A_400, C_401, D_398), G_399) | ~m1_connsp_2(E_397, B_396, G_399) | ~r1_tarski(E_397, u1_struct_0(D_398)) | ~m1_subset_1(G_399, u1_struct_0(D_398)) | ~m1_subset_1(G_399, u1_struct_0(B_396)) | ~m1_subset_1(E_397, k1_zfmisc_1(u1_struct_0(B_396))) | ~m1_pre_topc(D_398, B_396) | v2_struct_0(D_398) | ~m1_subset_1(C_401, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_396), u1_struct_0(A_400)))) | ~v1_funct_2(C_401, u1_struct_0(B_396), u1_struct_0(A_400)) | ~v1_funct_1(C_401) | ~l1_pre_topc(B_396) | ~v2_pre_topc(B_396) | v2_struct_0(B_396) | ~l1_pre_topc(A_400) | ~v2_pre_topc(A_400) | v2_struct_0(A_400))), inference(cnfTransformation, [status(thm)], [f_225])).
% 3.99/1.74  tff(c_362, plain, (![E_397]: (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | ~m1_connsp_2(E_397, '#skF_4', '#skF_8') | ~r1_tarski(E_397, u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1(E_397, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_126, c_358])).
% 3.99/1.74  tff(c_369, plain, (![E_397]: (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | ~m1_connsp_2(E_397, '#skF_4', '#skF_8') | ~r1_tarski(E_397, u1_struct_0('#skF_6')) | ~m1_subset_1(E_397, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_6') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_62, c_60, c_58, c_52, c_84, c_48, c_362])).
% 3.99/1.74  tff(c_371, plain, (![E_402]: (~m1_connsp_2(E_402, '#skF_4', '#skF_8') | ~r1_tarski(E_402, u1_struct_0('#skF_6')) | ~m1_subset_1(E_402, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_56, c_134, c_369])).
% 3.99/1.74  tff(c_375, plain, (![B_33, C_40]: (~m1_connsp_2('#skF_1'('#skF_4', B_33, C_40), '#skF_4', '#skF_8') | ~r1_tarski('#skF_1'('#skF_4', B_33, C_40), u1_struct_0('#skF_6')) | ~r2_hidden(C_40, B_33) | ~m1_subset_1(C_40, u1_struct_0('#skF_4')) | ~v3_pre_topc(B_33, '#skF_4') | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_371])).
% 3.99/1.74  tff(c_386, plain, (![B_33, C_40]: (~m1_connsp_2('#skF_1'('#skF_4', B_33, C_40), '#skF_4', '#skF_8') | ~r1_tarski('#skF_1'('#skF_4', B_33, C_40), u1_struct_0('#skF_6')) | ~r2_hidden(C_40, B_33) | ~m1_subset_1(C_40, u1_struct_0('#skF_4')) | ~v3_pre_topc(B_33, '#skF_4') | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_375])).
% 3.99/1.74  tff(c_393, plain, (![B_404, C_405]: (~m1_connsp_2('#skF_1'('#skF_4', B_404, C_405), '#skF_4', '#skF_8') | ~r1_tarski('#skF_1'('#skF_4', B_404, C_405), u1_struct_0('#skF_6')) | ~r2_hidden(C_405, B_404) | ~m1_subset_1(C_405, u1_struct_0('#skF_4')) | ~v3_pre_topc(B_404, '#skF_4') | ~m1_subset_1(B_404, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_386])).
% 3.99/1.74  tff(c_397, plain, (![C_350]: (~m1_connsp_2('#skF_1'('#skF_4', u1_struct_0('#skF_6'), C_350), '#skF_4', '#skF_8') | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r2_hidden(C_350, u1_struct_0('#skF_6')) | ~m1_subset_1(C_350, u1_struct_0('#skF_4')) | ~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_243, c_393])).
% 3.99/1.74  tff(c_400, plain, (![C_350]: (~m1_connsp_2('#skF_1'('#skF_4', u1_struct_0('#skF_6'), C_350), '#skF_4', '#skF_8') | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r2_hidden(C_350, u1_struct_0('#skF_6')) | ~m1_subset_1(C_350, u1_struct_0('#skF_4')) | ~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_4') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_52, c_66, c_397])).
% 3.99/1.74  tff(c_401, plain, (![C_350]: (~m1_connsp_2('#skF_1'('#skF_4', u1_struct_0('#skF_6'), C_350), '#skF_4', '#skF_8') | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r2_hidden(C_350, u1_struct_0('#skF_6')) | ~m1_subset_1(C_350, u1_struct_0('#skF_4')) | ~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_68, c_400])).
% 3.99/1.74  tff(c_402, plain, (~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_4')), inference(splitLeft, [status(thm)], [c_401])).
% 3.99/1.74  tff(c_405, plain, (~v1_tsep_1('#skF_6', '#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_206, c_402])).
% 3.99/1.74  tff(c_409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_52, c_66, c_54, c_405])).
% 3.99/1.74  tff(c_411, plain, (v3_pre_topc(u1_struct_0('#skF_6'), '#skF_4')), inference(splitRight, [status(thm)], [c_401])).
% 3.99/1.74  tff(c_257, plain, (![A_357, B_358, C_359]: (m1_connsp_2('#skF_1'(A_357, B_358, C_359), A_357, C_359) | ~r2_hidden(C_359, B_358) | ~m1_subset_1(C_359, u1_struct_0(A_357)) | ~v3_pre_topc(B_358, A_357) | ~m1_subset_1(B_358, k1_zfmisc_1(u1_struct_0(A_357))) | ~l1_pre_topc(A_357) | ~v2_pre_topc(A_357) | v2_struct_0(A_357))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.99/1.74  tff(c_263, plain, (![A_51, B_53, C_359]: (m1_connsp_2('#skF_1'(A_51, u1_struct_0(B_53), C_359), A_51, C_359) | ~r2_hidden(C_359, u1_struct_0(B_53)) | ~m1_subset_1(C_359, u1_struct_0(A_51)) | ~v3_pre_topc(u1_struct_0(B_53), A_51) | ~v2_pre_topc(A_51) | v2_struct_0(A_51) | ~m1_pre_topc(B_53, A_51) | ~l1_pre_topc(A_51))), inference(resolution, [status(thm)], [c_38, c_257])).
% 3.99/1.74  tff(c_410, plain, (![C_350]: (~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_connsp_2('#skF_1'('#skF_4', u1_struct_0('#skF_6'), C_350), '#skF_4', '#skF_8') | ~r2_hidden(C_350, u1_struct_0('#skF_6')) | ~m1_subset_1(C_350, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_401])).
% 3.99/1.74  tff(c_418, plain, (~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_410])).
% 3.99/1.74  tff(c_421, plain, (~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_38, c_418])).
% 3.99/1.74  tff(c_428, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_52, c_421])).
% 3.99/1.74  tff(c_485, plain, (![C_410]: (~m1_connsp_2('#skF_1'('#skF_4', u1_struct_0('#skF_6'), C_410), '#skF_4', '#skF_8') | ~r2_hidden(C_410, u1_struct_0('#skF_6')) | ~m1_subset_1(C_410, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_410])).
% 3.99/1.74  tff(c_493, plain, (~r2_hidden('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_263, c_485])).
% 3.99/1.74  tff(c_499, plain, (~r2_hidden('#skF_8', u1_struct_0('#skF_6')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_52, c_66, c_411, c_84, c_493])).
% 3.99/1.74  tff(c_500, plain, (~r2_hidden('#skF_8', u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_68, c_499])).
% 3.99/1.74  tff(c_503, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | v1_xboole_0(u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_4, c_500])).
% 3.99/1.74  tff(c_506, plain, (v1_xboole_0(u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_503])).
% 3.99/1.74  tff(c_508, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118, c_506])).
% 3.99/1.74  tff(c_509, plain, (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_83])).
% 3.99/1.74  tff(c_686, plain, (![C_479, F_482, D_481, B_478, A_480]: (r1_tmap_1(D_481, A_480, k2_tmap_1(B_478, A_480, C_479, D_481), F_482) | ~r1_tmap_1(B_478, A_480, C_479, F_482) | ~m1_subset_1(F_482, u1_struct_0(D_481)) | ~m1_subset_1(F_482, u1_struct_0(B_478)) | ~m1_pre_topc(D_481, B_478) | v2_struct_0(D_481) | ~m1_subset_1(C_479, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_478), u1_struct_0(A_480)))) | ~v1_funct_2(C_479, u1_struct_0(B_478), u1_struct_0(A_480)) | ~v1_funct_1(C_479) | ~l1_pre_topc(B_478) | ~v2_pre_topc(B_478) | v2_struct_0(B_478) | ~l1_pre_topc(A_480) | ~v2_pre_topc(A_480) | v2_struct_0(A_480))), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.99/1.74  tff(c_688, plain, (![D_481, F_482]: (r1_tmap_1(D_481, '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_481), F_482) | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', F_482) | ~m1_subset_1(F_482, u1_struct_0(D_481)) | ~m1_subset_1(F_482, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_481, '#skF_4') | v2_struct_0(D_481) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_58, c_686])).
% 3.99/1.74  tff(c_694, plain, (![D_481, F_482]: (r1_tmap_1(D_481, '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_481), F_482) | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', F_482) | ~m1_subset_1(F_482, u1_struct_0(D_481)) | ~m1_subset_1(F_482, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_481, '#skF_4') | v2_struct_0(D_481) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_62, c_60, c_688])).
% 3.99/1.74  tff(c_697, plain, (![D_483, F_484]: (r1_tmap_1(D_483, '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_483), F_484) | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', F_484) | ~m1_subset_1(F_484, u1_struct_0(D_483)) | ~m1_subset_1(F_484, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_483, '#skF_4') | v2_struct_0(D_483))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_694])).
% 3.99/1.74  tff(c_510, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(splitRight, [status(thm)], [c_83])).
% 3.99/1.74  tff(c_700, plain, (~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_697, c_510])).
% 3.99/1.74  tff(c_703, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_84, c_48, c_509, c_700])).
% 3.99/1.74  tff(c_705, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_703])).
% 3.99/1.74  tff(c_707, plain, (v1_xboole_0(u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_116])).
% 3.99/1.74  tff(c_14, plain, (![A_7]: (~v1_xboole_0(u1_struct_0(A_7)) | ~l1_struct_0(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.99/1.74  tff(c_710, plain, (~l1_struct_0('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_707, c_14])).
% 3.99/1.74  tff(c_713, plain, (~l1_struct_0('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_56, c_710])).
% 3.99/1.74  tff(c_716, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_10, c_713])).
% 3.99/1.74  tff(c_720, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_97, c_716])).
% 3.99/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.99/1.74  
% 3.99/1.74  Inference rules
% 3.99/1.74  ----------------------
% 3.99/1.74  #Ref     : 0
% 3.99/1.74  #Sup     : 119
% 3.99/1.74  #Fact    : 0
% 3.99/1.74  #Define  : 0
% 3.99/1.74  #Split   : 12
% 3.99/1.74  #Chain   : 0
% 3.99/1.74  #Close   : 0
% 3.99/1.74  
% 3.99/1.74  Ordering : KBO
% 3.99/1.74  
% 3.99/1.74  Simplification rules
% 3.99/1.74  ----------------------
% 3.99/1.74  #Subsume      : 15
% 3.99/1.74  #Demod        : 98
% 3.99/1.74  #Tautology    : 20
% 3.99/1.74  #SimpNegUnit  : 29
% 3.99/1.74  #BackRed      : 0
% 3.99/1.74  
% 3.99/1.74  #Partial instantiations: 0
% 3.99/1.74  #Strategies tried      : 1
% 3.99/1.74  
% 3.99/1.74  Timing (in seconds)
% 3.99/1.74  ----------------------
% 3.99/1.75  Preprocessing        : 0.44
% 3.99/1.75  Parsing              : 0.23
% 3.99/1.75  CNF conversion       : 0.06
% 3.99/1.75  Main loop            : 0.42
% 3.99/1.75  Inferencing          : 0.15
% 3.99/1.75  Reduction            : 0.12
% 3.99/1.75  Demodulation         : 0.08
% 3.99/1.75  BG Simplification    : 0.03
% 3.99/1.75  Subsumption          : 0.09
% 3.99/1.75  Abstraction          : 0.02
% 3.99/1.75  MUC search           : 0.00
% 3.99/1.75  Cooper               : 0.00
% 3.99/1.75  Total                : 0.90
% 3.99/1.75  Index Insertion      : 0.00
% 3.99/1.75  Index Deletion       : 0.00
% 3.99/1.75  Index Matching       : 0.00
% 3.99/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
