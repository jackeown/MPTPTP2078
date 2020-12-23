%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:28 EST 2020

% Result     : Theorem 3.96s
% Output     : CNFRefutation 4.31s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 665 expanded)
%              Number of leaves         :   42 ( 272 expanded)
%              Depth                    :   20
%              Number of atoms          :  420 (5226 expanded)
%              Number of equality atoms :    5 ( 220 expanded)
%              Maximal formula depth    :   29 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_9',type,(
    '#skF_9': $i )).

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
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(D),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                       => ( ( v1_tsep_1(C,D)
                            & m1_pre_topc(C,D) )
                         => ! [F] :
                              ( m1_subset_1(F,u1_struct_0(D))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(C))
                                 => ( F = G
                                   => ( r1_tmap_1(D,B,E,F)
                                    <=> r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),G) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tmap_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_51,axiom,(
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

tff(f_47,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_117,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_110,axiom,(
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

tff(f_92,axiom,(
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

tff(f_232,axiom,(
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
                        & v1_funct_2(E,u1_struct_0(D),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                     => ( m1_pre_topc(C,D)
                       => ! [F] :
                            ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(D)))
                           => ! [G] :
                                ( m1_subset_1(G,u1_struct_0(D))
                               => ! [H] :
                                    ( m1_subset_1(H,u1_struct_0(C))
                                   => ( ( r1_tarski(F,u1_struct_0(C))
                                        & m1_connsp_2(F,D,G)
                                        & G = H )
                                     => ( r1_tmap_1(D,B,E,G)
                                      <=> r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),H) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_tmap_1)).

tff(f_177,axiom,(
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
                          ( m1_subset_1(F,u1_struct_0(C))
                         => ! [G] :
                              ( m1_subset_1(G,u1_struct_0(D))
                             => ( ( F = G
                                  & m1_pre_topc(D,C)
                                  & r1_tmap_1(C,B,E,F) )
                               => r1_tmap_1(D,B,k3_tmap_1(A,B,C,D,E),G) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tmap_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_76,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_66,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_99,plain,(
    ! [B_559,A_560] :
      ( l1_pre_topc(B_559)
      | ~ m1_pre_topc(B_559,A_560)
      | ~ l1_pre_topc(A_560) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_108,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_99])).

tff(c_115,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_108])).

tff(c_12,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_78,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_62,plain,(
    m1_pre_topc('#skF_6','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_50,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_46,plain,(
    '#skF_9' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_48,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_91,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48])).

tff(c_52,plain,(
    m1_pre_topc('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_118,plain,(
    ! [B_561,A_562] :
      ( v1_xboole_0(B_561)
      | ~ m1_subset_1(B_561,A_562)
      | ~ v1_xboole_0(A_562) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_133,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_91,c_118])).

tff(c_135,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r2_hidden(B_2,A_1)
      | ~ m1_subset_1(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_105,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_99])).

tff(c_112,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_105])).

tff(c_144,plain,(
    ! [B_567,A_568] :
      ( v2_pre_topc(B_567)
      | ~ m1_pre_topc(B_567,A_568)
      | ~ l1_pre_topc(A_568)
      | ~ v2_pre_topc(A_568) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_150,plain,
    ( v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_144])).

tff(c_159,plain,(
    v2_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_150])).

tff(c_54,plain,(
    v1_tsep_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_36,plain,(
    ! [B_45,A_43] :
      ( m1_subset_1(u1_struct_0(B_45),k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ m1_pre_topc(B_45,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_343,plain,(
    ! [B_593,A_594] :
      ( v3_pre_topc(u1_struct_0(B_593),A_594)
      | ~ v1_tsep_1(B_593,A_594)
      | ~ m1_subset_1(u1_struct_0(B_593),k1_zfmisc_1(u1_struct_0(A_594)))
      | ~ m1_pre_topc(B_593,A_594)
      | ~ l1_pre_topc(A_594)
      | ~ v2_pre_topc(A_594) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_350,plain,(
    ! [B_45,A_43] :
      ( v3_pre_topc(u1_struct_0(B_45),A_43)
      | ~ v1_tsep_1(B_45,A_43)
      | ~ v2_pre_topc(A_43)
      | ~ m1_pre_topc(B_45,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(resolution,[status(thm)],[c_36,c_343])).

tff(c_362,plain,(
    ! [A_599,B_600,C_601] :
      ( r1_tarski('#skF_1'(A_599,B_600,C_601),B_600)
      | ~ r2_hidden(C_601,B_600)
      | ~ m1_subset_1(C_601,u1_struct_0(A_599))
      | ~ v3_pre_topc(B_600,A_599)
      | ~ m1_subset_1(B_600,k1_zfmisc_1(u1_struct_0(A_599)))
      | ~ l1_pre_topc(A_599)
      | ~ v2_pre_topc(A_599)
      | v2_struct_0(A_599) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_368,plain,(
    ! [A_43,B_45,C_601] :
      ( r1_tarski('#skF_1'(A_43,u1_struct_0(B_45),C_601),u1_struct_0(B_45))
      | ~ r2_hidden(C_601,u1_struct_0(B_45))
      | ~ m1_subset_1(C_601,u1_struct_0(A_43))
      | ~ v3_pre_topc(u1_struct_0(B_45),A_43)
      | ~ v2_pre_topc(A_43)
      | v2_struct_0(A_43)
      | ~ m1_pre_topc(B_45,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(resolution,[status(thm)],[c_36,c_362])).

tff(c_28,plain,(
    ! [A_11,B_25,C_32] :
      ( m1_subset_1('#skF_1'(A_11,B_25,C_32),k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ r2_hidden(C_32,B_25)
      | ~ m1_subset_1(C_32,u1_struct_0(A_11))
      | ~ v3_pre_topc(B_25,A_11)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_88,plain,
    ( r1_tmap_1('#skF_6','#skF_4','#skF_7','#skF_8')
    | r1_tmap_1('#skF_5','#skF_4',k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_7'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_89,plain,
    ( r1_tmap_1('#skF_6','#skF_4','#skF_7','#skF_8')
    | r1_tmap_1('#skF_5','#skF_4',k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_7'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_88])).

tff(c_170,plain,(
    r1_tmap_1('#skF_5','#skF_4',k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_7'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_82,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_4',k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_7'),'#skF_9')
    | ~ r1_tmap_1('#skF_6','#skF_4','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_90,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_4',k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_7'),'#skF_8')
    | ~ r1_tmap_1('#skF_6','#skF_4','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_82])).

tff(c_211,plain,(
    ~ r1_tmap_1('#skF_6','#skF_4','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_90])).

tff(c_72,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_70,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_60,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_58,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_56,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_283])).

tff(c_484,plain,(
    ! [B_661,D_659,A_663,H_662,E_658,F_657,C_660] :
      ( r1_tmap_1(D_659,B_661,E_658,H_662)
      | ~ r1_tmap_1(C_660,B_661,k3_tmap_1(A_663,B_661,D_659,C_660,E_658),H_662)
      | ~ m1_connsp_2(F_657,D_659,H_662)
      | ~ r1_tarski(F_657,u1_struct_0(C_660))
      | ~ m1_subset_1(H_662,u1_struct_0(C_660))
      | ~ m1_subset_1(H_662,u1_struct_0(D_659))
      | ~ m1_subset_1(F_657,k1_zfmisc_1(u1_struct_0(D_659)))
      | ~ m1_pre_topc(C_660,D_659)
      | ~ m1_subset_1(E_658,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_659),u1_struct_0(B_661))))
      | ~ v1_funct_2(E_658,u1_struct_0(D_659),u1_struct_0(B_661))
      | ~ v1_funct_1(E_658)
      | ~ m1_pre_topc(D_659,A_663)
      | v2_struct_0(D_659)
      | ~ m1_pre_topc(C_660,A_663)
      | v2_struct_0(C_660)
      | ~ l1_pre_topc(B_661)
      | ~ v2_pre_topc(B_661)
      | v2_struct_0(B_661)
      | ~ l1_pre_topc(A_663)
      | ~ v2_pre_topc(A_663)
      | v2_struct_0(A_663) ) ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_488,plain,(
    ! [F_657] :
      ( r1_tmap_1('#skF_6','#skF_4','#skF_7','#skF_8')
      | ~ m1_connsp_2(F_657,'#skF_6','#skF_8')
      | ~ r1_tarski(F_657,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
      | ~ m1_subset_1(F_657,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_pre_topc('#skF_5','#skF_6')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_pre_topc('#skF_6','#skF_3')
      | v2_struct_0('#skF_6')
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_170,c_484])).

tff(c_495,plain,(
    ! [F_657] :
      ( r1_tmap_1('#skF_6','#skF_4','#skF_7','#skF_8')
      | ~ m1_connsp_2(F_657,'#skF_6','#skF_8')
      | ~ r1_tarski(F_657,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_657,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_70,c_66,c_62,c_60,c_58,c_56,c_52,c_50,c_91,c_488])).

tff(c_497,plain,(
    ! [F_664] :
      ( ~ m1_connsp_2(F_664,'#skF_6','#skF_8')
      | ~ r1_tarski(F_664,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_664,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_68,c_64,c_211,c_495])).

tff(c_501,plain,(
    ! [B_25,C_32] :
      ( ~ m1_connsp_2('#skF_1'('#skF_6',B_25,C_32),'#skF_6','#skF_8')
      | ~ r1_tarski('#skF_1'('#skF_6',B_25,C_32),u1_struct_0('#skF_5'))
      | ~ r2_hidden(C_32,B_25)
      | ~ m1_subset_1(C_32,u1_struct_0('#skF_6'))
      | ~ v3_pre_topc(B_25,'#skF_6')
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_28,c_497])).

tff(c_512,plain,(
    ! [B_25,C_32] :
      ( ~ m1_connsp_2('#skF_1'('#skF_6',B_25,C_32),'#skF_6','#skF_8')
      | ~ r1_tarski('#skF_1'('#skF_6',B_25,C_32),u1_struct_0('#skF_5'))
      | ~ r2_hidden(C_32,B_25)
      | ~ m1_subset_1(C_32,u1_struct_0('#skF_6'))
      | ~ v3_pre_topc(B_25,'#skF_6')
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_112,c_501])).

tff(c_519,plain,(
    ! [B_666,C_667] :
      ( ~ m1_connsp_2('#skF_1'('#skF_6',B_666,C_667),'#skF_6','#skF_8')
      | ~ r1_tarski('#skF_1'('#skF_6',B_666,C_667),u1_struct_0('#skF_5'))
      | ~ r2_hidden(C_667,B_666)
      | ~ m1_subset_1(C_667,u1_struct_0('#skF_6'))
      | ~ v3_pre_topc(B_666,'#skF_6')
      | ~ m1_subset_1(B_666,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_512])).

tff(c_523,plain,(
    ! [C_601] :
      ( ~ m1_connsp_2('#skF_1'('#skF_6',u1_struct_0('#skF_5'),C_601),'#skF_6','#skF_8')
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ r2_hidden(C_601,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_601,u1_struct_0('#skF_6'))
      | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ m1_pre_topc('#skF_5','#skF_6')
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_368,c_519])).

tff(c_526,plain,(
    ! [C_601] :
      ( ~ m1_connsp_2('#skF_1'('#skF_6',u1_struct_0('#skF_5'),C_601),'#skF_6','#skF_8')
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ r2_hidden(C_601,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_601,u1_struct_0('#skF_6'))
      | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_52,c_159,c_523])).

tff(c_527,plain,(
    ! [C_601] :
      ( ~ m1_connsp_2('#skF_1'('#skF_6',u1_struct_0('#skF_5'),C_601),'#skF_6','#skF_8')
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ r2_hidden(C_601,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_601,u1_struct_0('#skF_6'))
      | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_526])).

tff(c_528,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_527])).

tff(c_531,plain,
    ( ~ v1_tsep_1('#skF_5','#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_350,c_528])).

tff(c_535,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_52,c_159,c_54,c_531])).

tff(c_537,plain,(
    v3_pre_topc(u1_struct_0('#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_527])).

tff(c_389,plain,(
    ! [A_615,B_616,C_617] :
      ( m1_connsp_2('#skF_1'(A_615,B_616,C_617),A_615,C_617)
      | ~ r2_hidden(C_617,B_616)
      | ~ m1_subset_1(C_617,u1_struct_0(A_615))
      | ~ v3_pre_topc(B_616,A_615)
      | ~ m1_subset_1(B_616,k1_zfmisc_1(u1_struct_0(A_615)))
      | ~ l1_pre_topc(A_615)
      | ~ v2_pre_topc(A_615)
      | v2_struct_0(A_615) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_395,plain,(
    ! [A_43,B_45,C_617] :
      ( m1_connsp_2('#skF_1'(A_43,u1_struct_0(B_45),C_617),A_43,C_617)
      | ~ r2_hidden(C_617,u1_struct_0(B_45))
      | ~ m1_subset_1(C_617,u1_struct_0(A_43))
      | ~ v3_pre_topc(u1_struct_0(B_45),A_43)
      | ~ v2_pre_topc(A_43)
      | v2_struct_0(A_43)
      | ~ m1_pre_topc(B_45,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(resolution,[status(thm)],[c_36,c_389])).

tff(c_536,plain,(
    ! [C_601] :
      ( ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_connsp_2('#skF_1'('#skF_6',u1_struct_0('#skF_5'),C_601),'#skF_6','#skF_8')
      | ~ r2_hidden(C_601,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_601,u1_struct_0('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_527])).

tff(c_544,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_536])).

tff(c_547,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_544])).

tff(c_554,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_52,c_547])).

tff(c_609,plain,(
    ! [C_671] :
      ( ~ m1_connsp_2('#skF_1'('#skF_6',u1_struct_0('#skF_5'),C_671),'#skF_6','#skF_8')
      | ~ r2_hidden(C_671,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_671,u1_struct_0('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_536])).

tff(c_613,plain,
    ( ~ r2_hidden('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ v3_pre_topc(u1_struct_0('#skF_5'),'#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_395,c_609])).

tff(c_616,plain,
    ( ~ r2_hidden('#skF_8',u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_52,c_159,c_537,c_50,c_613])).

tff(c_617,plain,(
    ~ r2_hidden('#skF_8',u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_616])).

tff(c_620,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_4,c_617])).

tff(c_623,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_620])).

tff(c_625,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_623])).

tff(c_626,plain,(
    r1_tmap_1('#skF_6','#skF_4','#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_880,plain,(
    ! [E_739,B_735,A_734,D_738,C_736,G_737] :
      ( r1_tmap_1(D_738,B_735,k3_tmap_1(A_734,B_735,C_736,D_738,E_739),G_737)
      | ~ r1_tmap_1(C_736,B_735,E_739,G_737)
      | ~ m1_pre_topc(D_738,C_736)
      | ~ m1_subset_1(G_737,u1_struct_0(D_738))
      | ~ m1_subset_1(G_737,u1_struct_0(C_736))
      | ~ m1_subset_1(E_739,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_736),u1_struct_0(B_735))))
      | ~ v1_funct_2(E_739,u1_struct_0(C_736),u1_struct_0(B_735))
      | ~ v1_funct_1(E_739)
      | ~ m1_pre_topc(D_738,A_734)
      | v2_struct_0(D_738)
      | ~ m1_pre_topc(C_736,A_734)
      | v2_struct_0(C_736)
      | ~ l1_pre_topc(B_735)
      | ~ v2_pre_topc(B_735)
      | v2_struct_0(B_735)
      | ~ l1_pre_topc(A_734)
      | ~ v2_pre_topc(A_734)
      | v2_struct_0(A_734) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_885,plain,(
    ! [D_738,A_734,G_737] :
      ( r1_tmap_1(D_738,'#skF_4',k3_tmap_1(A_734,'#skF_4','#skF_6',D_738,'#skF_7'),G_737)
      | ~ r1_tmap_1('#skF_6','#skF_4','#skF_7',G_737)
      | ~ m1_pre_topc(D_738,'#skF_6')
      | ~ m1_subset_1(G_737,u1_struct_0(D_738))
      | ~ m1_subset_1(G_737,u1_struct_0('#skF_6'))
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_pre_topc(D_738,A_734)
      | v2_struct_0(D_738)
      | ~ m1_pre_topc('#skF_6',A_734)
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_734)
      | ~ v2_pre_topc(A_734)
      | v2_struct_0(A_734) ) ),
    inference(resolution,[status(thm)],[c_56,c_880])).

tff(c_889,plain,(
    ! [D_738,A_734,G_737] :
      ( r1_tmap_1(D_738,'#skF_4',k3_tmap_1(A_734,'#skF_4','#skF_6',D_738,'#skF_7'),G_737)
      | ~ r1_tmap_1('#skF_6','#skF_4','#skF_7',G_737)
      | ~ m1_pre_topc(D_738,'#skF_6')
      | ~ m1_subset_1(G_737,u1_struct_0(D_738))
      | ~ m1_subset_1(G_737,u1_struct_0('#skF_6'))
      | ~ m1_pre_topc(D_738,A_734)
      | v2_struct_0(D_738)
      | ~ m1_pre_topc('#skF_6',A_734)
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_734)
      | ~ v2_pre_topc(A_734)
      | v2_struct_0(A_734) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_60,c_58,c_885])).

tff(c_968,plain,(
    ! [D_771,A_772,G_773] :
      ( r1_tmap_1(D_771,'#skF_4',k3_tmap_1(A_772,'#skF_4','#skF_6',D_771,'#skF_7'),G_773)
      | ~ r1_tmap_1('#skF_6','#skF_4','#skF_7',G_773)
      | ~ m1_pre_topc(D_771,'#skF_6')
      | ~ m1_subset_1(G_773,u1_struct_0(D_771))
      | ~ m1_subset_1(G_773,u1_struct_0('#skF_6'))
      | ~ m1_pre_topc(D_771,A_772)
      | v2_struct_0(D_771)
      | ~ m1_pre_topc('#skF_6',A_772)
      | ~ l1_pre_topc(A_772)
      | ~ v2_pre_topc(A_772)
      | v2_struct_0(A_772) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_64,c_889])).

tff(c_627,plain,(
    ~ r1_tmap_1('#skF_5','#skF_4',k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_7'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_973,plain,
    ( ~ r1_tmap_1('#skF_6','#skF_4','#skF_7','#skF_8')
    | ~ m1_pre_topc('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_6','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_968,c_627])).

tff(c_980,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_62,c_66,c_50,c_91,c_52,c_626,c_973])).

tff(c_982,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_68,c_980])).

tff(c_984,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_16,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(u1_struct_0(A_10))
      | ~ l1_struct_0(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_987,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_984,c_16])).

tff(c_990,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_987])).

tff(c_993,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_990])).

tff(c_997,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_993])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:41:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.96/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.31/1.72  
% 4.31/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.31/1.72  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2
% 4.31/1.72  
% 4.31/1.72  %Foreground sorts:
% 4.31/1.72  
% 4.31/1.72  
% 4.31/1.72  %Background operators:
% 4.31/1.72  
% 4.31/1.72  
% 4.31/1.72  %Foreground operators:
% 4.31/1.72  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.31/1.72  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 4.31/1.72  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.31/1.72  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.31/1.72  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.31/1.72  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.31/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.31/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.31/1.72  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.31/1.72  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.31/1.72  tff('#skF_7', type, '#skF_7': $i).
% 4.31/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.31/1.72  tff('#skF_5', type, '#skF_5': $i).
% 4.31/1.72  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.31/1.72  tff('#skF_6', type, '#skF_6': $i).
% 4.31/1.72  tff('#skF_3', type, '#skF_3': $i).
% 4.31/1.72  tff('#skF_9', type, '#skF_9': $i).
% 4.31/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.31/1.72  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.31/1.72  tff('#skF_8', type, '#skF_8': $i).
% 4.31/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.31/1.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.31/1.72  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 4.31/1.72  tff('#skF_4', type, '#skF_4': $i).
% 4.31/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.31/1.72  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.31/1.72  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.31/1.72  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.31/1.72  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.31/1.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.31/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.31/1.72  
% 4.31/1.74  tff(f_283, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tmap_1)).
% 4.31/1.74  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.31/1.74  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.31/1.74  tff(f_38, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 4.31/1.74  tff(f_47, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.31/1.74  tff(f_117, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.31/1.74  tff(f_110, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 4.31/1.74  tff(f_92, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(D, A, C) & r1_tarski(D, B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_connsp_2)).
% 4.31/1.74  tff(f_232, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_tmap_1)).
% 4.31/1.74  tff(f_177, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((F = G) & m1_pre_topc(D, C)) & r1_tmap_1(C, B, E, F)) => r1_tmap_1(D, B, k3_tmap_1(A, B, C, D, E), G)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_tmap_1)).
% 4.31/1.74  tff(f_66, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.31/1.74  tff(c_76, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.31/1.74  tff(c_66, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.31/1.74  tff(c_99, plain, (![B_559, A_560]: (l1_pre_topc(B_559) | ~m1_pre_topc(B_559, A_560) | ~l1_pre_topc(A_560))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.31/1.74  tff(c_108, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_66, c_99])).
% 4.31/1.74  tff(c_115, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_108])).
% 4.31/1.74  tff(c_12, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.31/1.74  tff(c_68, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.31/1.74  tff(c_80, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.31/1.74  tff(c_78, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.31/1.74  tff(c_62, plain, (m1_pre_topc('#skF_6', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.31/1.74  tff(c_50, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.31/1.74  tff(c_46, plain, ('#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.31/1.74  tff(c_48, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.31/1.74  tff(c_91, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48])).
% 4.31/1.74  tff(c_52, plain, (m1_pre_topc('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.31/1.74  tff(c_118, plain, (![B_561, A_562]: (v1_xboole_0(B_561) | ~m1_subset_1(B_561, A_562) | ~v1_xboole_0(A_562))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.31/1.74  tff(c_133, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_91, c_118])).
% 4.31/1.74  tff(c_135, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_133])).
% 4.31/1.74  tff(c_4, plain, (![B_2, A_1]: (r2_hidden(B_2, A_1) | ~m1_subset_1(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.31/1.74  tff(c_64, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.31/1.74  tff(c_105, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_62, c_99])).
% 4.31/1.74  tff(c_112, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_105])).
% 4.31/1.74  tff(c_144, plain, (![B_567, A_568]: (v2_pre_topc(B_567) | ~m1_pre_topc(B_567, A_568) | ~l1_pre_topc(A_568) | ~v2_pre_topc(A_568))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.31/1.74  tff(c_150, plain, (v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_62, c_144])).
% 4.31/1.74  tff(c_159, plain, (v2_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_150])).
% 4.31/1.74  tff(c_54, plain, (v1_tsep_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.31/1.74  tff(c_36, plain, (![B_45, A_43]: (m1_subset_1(u1_struct_0(B_45), k1_zfmisc_1(u1_struct_0(A_43))) | ~m1_pre_topc(B_45, A_43) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.31/1.74  tff(c_343, plain, (![B_593, A_594]: (v3_pre_topc(u1_struct_0(B_593), A_594) | ~v1_tsep_1(B_593, A_594) | ~m1_subset_1(u1_struct_0(B_593), k1_zfmisc_1(u1_struct_0(A_594))) | ~m1_pre_topc(B_593, A_594) | ~l1_pre_topc(A_594) | ~v2_pre_topc(A_594))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.31/1.74  tff(c_350, plain, (![B_45, A_43]: (v3_pre_topc(u1_struct_0(B_45), A_43) | ~v1_tsep_1(B_45, A_43) | ~v2_pre_topc(A_43) | ~m1_pre_topc(B_45, A_43) | ~l1_pre_topc(A_43))), inference(resolution, [status(thm)], [c_36, c_343])).
% 4.31/1.74  tff(c_362, plain, (![A_599, B_600, C_601]: (r1_tarski('#skF_1'(A_599, B_600, C_601), B_600) | ~r2_hidden(C_601, B_600) | ~m1_subset_1(C_601, u1_struct_0(A_599)) | ~v3_pre_topc(B_600, A_599) | ~m1_subset_1(B_600, k1_zfmisc_1(u1_struct_0(A_599))) | ~l1_pre_topc(A_599) | ~v2_pre_topc(A_599) | v2_struct_0(A_599))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.31/1.74  tff(c_368, plain, (![A_43, B_45, C_601]: (r1_tarski('#skF_1'(A_43, u1_struct_0(B_45), C_601), u1_struct_0(B_45)) | ~r2_hidden(C_601, u1_struct_0(B_45)) | ~m1_subset_1(C_601, u1_struct_0(A_43)) | ~v3_pre_topc(u1_struct_0(B_45), A_43) | ~v2_pre_topc(A_43) | v2_struct_0(A_43) | ~m1_pre_topc(B_45, A_43) | ~l1_pre_topc(A_43))), inference(resolution, [status(thm)], [c_36, c_362])).
% 4.31/1.74  tff(c_28, plain, (![A_11, B_25, C_32]: (m1_subset_1('#skF_1'(A_11, B_25, C_32), k1_zfmisc_1(u1_struct_0(A_11))) | ~r2_hidden(C_32, B_25) | ~m1_subset_1(C_32, u1_struct_0(A_11)) | ~v3_pre_topc(B_25, A_11) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.31/1.74  tff(c_74, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.31/1.74  tff(c_88, plain, (r1_tmap_1('#skF_6', '#skF_4', '#skF_7', '#skF_8') | r1_tmap_1('#skF_5', '#skF_4', k3_tmap_1('#skF_3', '#skF_4', '#skF_6', '#skF_5', '#skF_7'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.31/1.74  tff(c_89, plain, (r1_tmap_1('#skF_6', '#skF_4', '#skF_7', '#skF_8') | r1_tmap_1('#skF_5', '#skF_4', k3_tmap_1('#skF_3', '#skF_4', '#skF_6', '#skF_5', '#skF_7'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_88])).
% 4.31/1.74  tff(c_170, plain, (r1_tmap_1('#skF_5', '#skF_4', k3_tmap_1('#skF_3', '#skF_4', '#skF_6', '#skF_5', '#skF_7'), '#skF_8')), inference(splitLeft, [status(thm)], [c_89])).
% 4.31/1.74  tff(c_82, plain, (~r1_tmap_1('#skF_5', '#skF_4', k3_tmap_1('#skF_3', '#skF_4', '#skF_6', '#skF_5', '#skF_7'), '#skF_9') | ~r1_tmap_1('#skF_6', '#skF_4', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.31/1.74  tff(c_90, plain, (~r1_tmap_1('#skF_5', '#skF_4', k3_tmap_1('#skF_3', '#skF_4', '#skF_6', '#skF_5', '#skF_7'), '#skF_8') | ~r1_tmap_1('#skF_6', '#skF_4', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_82])).
% 4.31/1.74  tff(c_211, plain, (~r1_tmap_1('#skF_6', '#skF_4', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_170, c_90])).
% 4.31/1.74  tff(c_72, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.31/1.74  tff(c_70, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.31/1.74  tff(c_60, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.31/1.74  tff(c_58, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.31/1.74  tff(c_56, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_283])).
% 4.31/1.74  tff(c_484, plain, (![B_661, D_659, A_663, H_662, E_658, F_657, C_660]: (r1_tmap_1(D_659, B_661, E_658, H_662) | ~r1_tmap_1(C_660, B_661, k3_tmap_1(A_663, B_661, D_659, C_660, E_658), H_662) | ~m1_connsp_2(F_657, D_659, H_662) | ~r1_tarski(F_657, u1_struct_0(C_660)) | ~m1_subset_1(H_662, u1_struct_0(C_660)) | ~m1_subset_1(H_662, u1_struct_0(D_659)) | ~m1_subset_1(F_657, k1_zfmisc_1(u1_struct_0(D_659))) | ~m1_pre_topc(C_660, D_659) | ~m1_subset_1(E_658, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_659), u1_struct_0(B_661)))) | ~v1_funct_2(E_658, u1_struct_0(D_659), u1_struct_0(B_661)) | ~v1_funct_1(E_658) | ~m1_pre_topc(D_659, A_663) | v2_struct_0(D_659) | ~m1_pre_topc(C_660, A_663) | v2_struct_0(C_660) | ~l1_pre_topc(B_661) | ~v2_pre_topc(B_661) | v2_struct_0(B_661) | ~l1_pre_topc(A_663) | ~v2_pre_topc(A_663) | v2_struct_0(A_663))), inference(cnfTransformation, [status(thm)], [f_232])).
% 4.31/1.74  tff(c_488, plain, (![F_657]: (r1_tmap_1('#skF_6', '#skF_4', '#skF_7', '#skF_8') | ~m1_connsp_2(F_657, '#skF_6', '#skF_8') | ~r1_tarski(F_657, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1(F_657, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_pre_topc('#skF_5', '#skF_6') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_7') | ~m1_pre_topc('#skF_6', '#skF_3') | v2_struct_0('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_170, c_484])).
% 4.31/1.74  tff(c_495, plain, (![F_657]: (r1_tmap_1('#skF_6', '#skF_4', '#skF_7', '#skF_8') | ~m1_connsp_2(F_657, '#skF_6', '#skF_8') | ~r1_tarski(F_657, u1_struct_0('#skF_5')) | ~m1_subset_1(F_657, k1_zfmisc_1(u1_struct_0('#skF_6'))) | v2_struct_0('#skF_6') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_70, c_66, c_62, c_60, c_58, c_56, c_52, c_50, c_91, c_488])).
% 4.31/1.74  tff(c_497, plain, (![F_664]: (~m1_connsp_2(F_664, '#skF_6', '#skF_8') | ~r1_tarski(F_664, u1_struct_0('#skF_5')) | ~m1_subset_1(F_664, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_68, c_64, c_211, c_495])).
% 4.31/1.74  tff(c_501, plain, (![B_25, C_32]: (~m1_connsp_2('#skF_1'('#skF_6', B_25, C_32), '#skF_6', '#skF_8') | ~r1_tarski('#skF_1'('#skF_6', B_25, C_32), u1_struct_0('#skF_5')) | ~r2_hidden(C_32, B_25) | ~m1_subset_1(C_32, u1_struct_0('#skF_6')) | ~v3_pre_topc(B_25, '#skF_6') | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_28, c_497])).
% 4.31/1.74  tff(c_512, plain, (![B_25, C_32]: (~m1_connsp_2('#skF_1'('#skF_6', B_25, C_32), '#skF_6', '#skF_8') | ~r1_tarski('#skF_1'('#skF_6', B_25, C_32), u1_struct_0('#skF_5')) | ~r2_hidden(C_32, B_25) | ~m1_subset_1(C_32, u1_struct_0('#skF_6')) | ~v3_pre_topc(B_25, '#skF_6') | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0('#skF_6'))) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_112, c_501])).
% 4.31/1.74  tff(c_519, plain, (![B_666, C_667]: (~m1_connsp_2('#skF_1'('#skF_6', B_666, C_667), '#skF_6', '#skF_8') | ~r1_tarski('#skF_1'('#skF_6', B_666, C_667), u1_struct_0('#skF_5')) | ~r2_hidden(C_667, B_666) | ~m1_subset_1(C_667, u1_struct_0('#skF_6')) | ~v3_pre_topc(B_666, '#skF_6') | ~m1_subset_1(B_666, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_512])).
% 4.31/1.74  tff(c_523, plain, (![C_601]: (~m1_connsp_2('#skF_1'('#skF_6', u1_struct_0('#skF_5'), C_601), '#skF_6', '#skF_8') | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~r2_hidden(C_601, u1_struct_0('#skF_5')) | ~m1_subset_1(C_601, u1_struct_0('#skF_6')) | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_6'))), inference(resolution, [status(thm)], [c_368, c_519])).
% 4.31/1.74  tff(c_526, plain, (![C_601]: (~m1_connsp_2('#skF_1'('#skF_6', u1_struct_0('#skF_5'), C_601), '#skF_6', '#skF_8') | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~r2_hidden(C_601, u1_struct_0('#skF_5')) | ~m1_subset_1(C_601, u1_struct_0('#skF_6')) | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_6') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_52, c_159, c_523])).
% 4.31/1.74  tff(c_527, plain, (![C_601]: (~m1_connsp_2('#skF_1'('#skF_6', u1_struct_0('#skF_5'), C_601), '#skF_6', '#skF_8') | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~r2_hidden(C_601, u1_struct_0('#skF_5')) | ~m1_subset_1(C_601, u1_struct_0('#skF_6')) | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_64, c_526])).
% 4.31/1.74  tff(c_528, plain, (~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_527])).
% 4.31/1.74  tff(c_531, plain, (~v1_tsep_1('#skF_5', '#skF_6') | ~v2_pre_topc('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_350, c_528])).
% 4.31/1.74  tff(c_535, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_52, c_159, c_54, c_531])).
% 4.31/1.74  tff(c_537, plain, (v3_pre_topc(u1_struct_0('#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_527])).
% 4.31/1.74  tff(c_389, plain, (![A_615, B_616, C_617]: (m1_connsp_2('#skF_1'(A_615, B_616, C_617), A_615, C_617) | ~r2_hidden(C_617, B_616) | ~m1_subset_1(C_617, u1_struct_0(A_615)) | ~v3_pre_topc(B_616, A_615) | ~m1_subset_1(B_616, k1_zfmisc_1(u1_struct_0(A_615))) | ~l1_pre_topc(A_615) | ~v2_pre_topc(A_615) | v2_struct_0(A_615))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.31/1.74  tff(c_395, plain, (![A_43, B_45, C_617]: (m1_connsp_2('#skF_1'(A_43, u1_struct_0(B_45), C_617), A_43, C_617) | ~r2_hidden(C_617, u1_struct_0(B_45)) | ~m1_subset_1(C_617, u1_struct_0(A_43)) | ~v3_pre_topc(u1_struct_0(B_45), A_43) | ~v2_pre_topc(A_43) | v2_struct_0(A_43) | ~m1_pre_topc(B_45, A_43) | ~l1_pre_topc(A_43))), inference(resolution, [status(thm)], [c_36, c_389])).
% 4.31/1.74  tff(c_536, plain, (![C_601]: (~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_connsp_2('#skF_1'('#skF_6', u1_struct_0('#skF_5'), C_601), '#skF_6', '#skF_8') | ~r2_hidden(C_601, u1_struct_0('#skF_5')) | ~m1_subset_1(C_601, u1_struct_0('#skF_6')))), inference(splitRight, [status(thm)], [c_527])).
% 4.31/1.74  tff(c_544, plain, (~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(splitLeft, [status(thm)], [c_536])).
% 4.31/1.74  tff(c_547, plain, (~m1_pre_topc('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_36, c_544])).
% 4.31/1.74  tff(c_554, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_52, c_547])).
% 4.31/1.74  tff(c_609, plain, (![C_671]: (~m1_connsp_2('#skF_1'('#skF_6', u1_struct_0('#skF_5'), C_671), '#skF_6', '#skF_8') | ~r2_hidden(C_671, u1_struct_0('#skF_5')) | ~m1_subset_1(C_671, u1_struct_0('#skF_6')))), inference(splitRight, [status(thm)], [c_536])).
% 4.31/1.74  tff(c_613, plain, (~r2_hidden('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~v3_pre_topc(u1_struct_0('#skF_5'), '#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_395, c_609])).
% 4.31/1.74  tff(c_616, plain, (~r2_hidden('#skF_8', u1_struct_0('#skF_5')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_52, c_159, c_537, c_50, c_613])).
% 4.31/1.74  tff(c_617, plain, (~r2_hidden('#skF_8', u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_64, c_616])).
% 4.31/1.74  tff(c_620, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_4, c_617])).
% 4.31/1.74  tff(c_623, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_620])).
% 4.31/1.74  tff(c_625, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135, c_623])).
% 4.31/1.74  tff(c_626, plain, (r1_tmap_1('#skF_6', '#skF_4', '#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_89])).
% 4.31/1.74  tff(c_880, plain, (![E_739, B_735, A_734, D_738, C_736, G_737]: (r1_tmap_1(D_738, B_735, k3_tmap_1(A_734, B_735, C_736, D_738, E_739), G_737) | ~r1_tmap_1(C_736, B_735, E_739, G_737) | ~m1_pre_topc(D_738, C_736) | ~m1_subset_1(G_737, u1_struct_0(D_738)) | ~m1_subset_1(G_737, u1_struct_0(C_736)) | ~m1_subset_1(E_739, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_736), u1_struct_0(B_735)))) | ~v1_funct_2(E_739, u1_struct_0(C_736), u1_struct_0(B_735)) | ~v1_funct_1(E_739) | ~m1_pre_topc(D_738, A_734) | v2_struct_0(D_738) | ~m1_pre_topc(C_736, A_734) | v2_struct_0(C_736) | ~l1_pre_topc(B_735) | ~v2_pre_topc(B_735) | v2_struct_0(B_735) | ~l1_pre_topc(A_734) | ~v2_pre_topc(A_734) | v2_struct_0(A_734))), inference(cnfTransformation, [status(thm)], [f_177])).
% 4.31/1.74  tff(c_885, plain, (![D_738, A_734, G_737]: (r1_tmap_1(D_738, '#skF_4', k3_tmap_1(A_734, '#skF_4', '#skF_6', D_738, '#skF_7'), G_737) | ~r1_tmap_1('#skF_6', '#skF_4', '#skF_7', G_737) | ~m1_pre_topc(D_738, '#skF_6') | ~m1_subset_1(G_737, u1_struct_0(D_738)) | ~m1_subset_1(G_737, u1_struct_0('#skF_6')) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_7') | ~m1_pre_topc(D_738, A_734) | v2_struct_0(D_738) | ~m1_pre_topc('#skF_6', A_734) | v2_struct_0('#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_734) | ~v2_pre_topc(A_734) | v2_struct_0(A_734))), inference(resolution, [status(thm)], [c_56, c_880])).
% 4.31/1.74  tff(c_889, plain, (![D_738, A_734, G_737]: (r1_tmap_1(D_738, '#skF_4', k3_tmap_1(A_734, '#skF_4', '#skF_6', D_738, '#skF_7'), G_737) | ~r1_tmap_1('#skF_6', '#skF_4', '#skF_7', G_737) | ~m1_pre_topc(D_738, '#skF_6') | ~m1_subset_1(G_737, u1_struct_0(D_738)) | ~m1_subset_1(G_737, u1_struct_0('#skF_6')) | ~m1_pre_topc(D_738, A_734) | v2_struct_0(D_738) | ~m1_pre_topc('#skF_6', A_734) | v2_struct_0('#skF_6') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_734) | ~v2_pre_topc(A_734) | v2_struct_0(A_734))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_60, c_58, c_885])).
% 4.31/1.74  tff(c_968, plain, (![D_771, A_772, G_773]: (r1_tmap_1(D_771, '#skF_4', k3_tmap_1(A_772, '#skF_4', '#skF_6', D_771, '#skF_7'), G_773) | ~r1_tmap_1('#skF_6', '#skF_4', '#skF_7', G_773) | ~m1_pre_topc(D_771, '#skF_6') | ~m1_subset_1(G_773, u1_struct_0(D_771)) | ~m1_subset_1(G_773, u1_struct_0('#skF_6')) | ~m1_pre_topc(D_771, A_772) | v2_struct_0(D_771) | ~m1_pre_topc('#skF_6', A_772) | ~l1_pre_topc(A_772) | ~v2_pre_topc(A_772) | v2_struct_0(A_772))), inference(negUnitSimplification, [status(thm)], [c_74, c_64, c_889])).
% 4.31/1.74  tff(c_627, plain, (~r1_tmap_1('#skF_5', '#skF_4', k3_tmap_1('#skF_3', '#skF_4', '#skF_6', '#skF_5', '#skF_7'), '#skF_8')), inference(splitRight, [status(thm)], [c_89])).
% 4.31/1.74  tff(c_973, plain, (~r1_tmap_1('#skF_6', '#skF_4', '#skF_7', '#skF_8') | ~m1_pre_topc('#skF_5', '#skF_6') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_6', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_968, c_627])).
% 4.31/1.75  tff(c_980, plain, (v2_struct_0('#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_62, c_66, c_50, c_91, c_52, c_626, c_973])).
% 4.31/1.75  tff(c_982, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_68, c_980])).
% 4.31/1.75  tff(c_984, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_133])).
% 4.31/1.75  tff(c_16, plain, (![A_10]: (~v1_xboole_0(u1_struct_0(A_10)) | ~l1_struct_0(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.31/1.75  tff(c_987, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_984, c_16])).
% 4.31/1.75  tff(c_990, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_68, c_987])).
% 4.31/1.75  tff(c_993, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_12, c_990])).
% 4.31/1.75  tff(c_997, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_115, c_993])).
% 4.31/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.31/1.75  
% 4.31/1.75  Inference rules
% 4.31/1.75  ----------------------
% 4.31/1.75  #Ref     : 0
% 4.31/1.75  #Sup     : 176
% 4.31/1.75  #Fact    : 0
% 4.31/1.75  #Define  : 0
% 4.31/1.75  #Split   : 13
% 4.31/1.75  #Chain   : 0
% 4.31/1.75  #Close   : 0
% 4.31/1.75  
% 4.31/1.75  Ordering : KBO
% 4.31/1.75  
% 4.31/1.75  Simplification rules
% 4.31/1.75  ----------------------
% 4.31/1.75  #Subsume      : 35
% 4.31/1.75  #Demod        : 239
% 4.31/1.75  #Tautology    : 43
% 4.31/1.75  #SimpNegUnit  : 22
% 4.31/1.75  #BackRed      : 0
% 4.31/1.75  
% 4.31/1.75  #Partial instantiations: 0
% 4.31/1.75  #Strategies tried      : 1
% 4.31/1.75  
% 4.31/1.75  Timing (in seconds)
% 4.31/1.75  ----------------------
% 4.31/1.75  Preprocessing        : 0.43
% 4.31/1.75  Parsing              : 0.21
% 4.31/1.75  CNF conversion       : 0.07
% 4.31/1.75  Main loop            : 0.51
% 4.31/1.75  Inferencing          : 0.18
% 4.31/1.75  Reduction            : 0.15
% 4.31/1.75  Demodulation         : 0.10
% 4.31/1.75  BG Simplification    : 0.03
% 4.31/1.75  Subsumption          : 0.12
% 4.31/1.75  Abstraction          : 0.02
% 4.31/1.75  MUC search           : 0.00
% 4.31/1.75  Cooper               : 0.00
% 4.31/1.75  Total                : 0.99
% 4.31/1.75  Index Insertion      : 0.00
% 4.31/1.75  Index Deletion       : 0.00
% 4.31/1.75  Index Matching       : 0.00
% 4.31/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
