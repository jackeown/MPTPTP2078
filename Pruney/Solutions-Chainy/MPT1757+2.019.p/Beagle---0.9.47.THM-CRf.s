%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:06 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 216 expanded)
%              Number of leaves         :   41 (  99 expanded)
%              Depth                    :   20
%              Number of atoms          :  328 (1318 expanded)
%              Number of equality atoms :   12 (  75 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

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

tff(f_279,negated_conjecture,(
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

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_149,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_142,axiom,(
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

tff(f_93,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( ( v3_pre_topc(D,B)
                     => k1_tops_1(B,D) = D )
                    & ( k1_tops_1(A,C) = C
                     => v3_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

tff(f_110,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> r2_hidden(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_236,axiom,(
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

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_189,axiom,(
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

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_279])).

tff(c_48,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_279])).

tff(c_42,plain,(
    '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_279])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_279])).

tff(c_80,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_279])).

tff(c_60,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_279])).

tff(c_90,plain,(
    ! [B_303,A_304] :
      ( l1_pre_topc(B_303)
      | ~ m1_pre_topc(B_303,A_304)
      | ~ l1_pre_topc(A_304) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_93,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_90])).

tff(c_96,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_93])).

tff(c_10,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_279])).

tff(c_62,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_279])).

tff(c_50,plain,(
    v1_tsep_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_279])).

tff(c_34,plain,(
    ! [B_52,A_50] :
      ( m1_subset_1(u1_struct_0(B_52),k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ m1_pre_topc(B_52,A_50)
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_142,plain,(
    ! [B_323,A_324] :
      ( v3_pre_topc(u1_struct_0(B_323),A_324)
      | ~ v1_tsep_1(B_323,A_324)
      | ~ m1_subset_1(u1_struct_0(B_323),k1_zfmisc_1(u1_struct_0(A_324)))
      | ~ m1_pre_topc(B_323,A_324)
      | ~ l1_pre_topc(A_324)
      | ~ v2_pre_topc(A_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_146,plain,(
    ! [B_52,A_50] :
      ( v3_pre_topc(u1_struct_0(B_52),A_50)
      | ~ v1_tsep_1(B_52,A_50)
      | ~ v2_pre_topc(A_50)
      | ~ m1_pre_topc(B_52,A_50)
      | ~ l1_pre_topc(A_50) ) ),
    inference(resolution,[status(thm)],[c_34,c_142])).

tff(c_20,plain,(
    ! [B_25,D_31,C_29,A_17] :
      ( k1_tops_1(B_25,D_31) = D_31
      | ~ v3_pre_topc(D_31,B_25)
      | ~ m1_subset_1(D_31,k1_zfmisc_1(u1_struct_0(B_25)))
      | ~ m1_subset_1(C_29,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(B_25)
      | ~ l1_pre_topc(A_17)
      | ~ v2_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_174,plain,(
    ! [C_335,A_336] :
      ( ~ m1_subset_1(C_335,k1_zfmisc_1(u1_struct_0(A_336)))
      | ~ l1_pre_topc(A_336)
      | ~ v2_pre_topc(A_336) ) ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_179,plain,(
    ! [A_337,B_338] :
      ( ~ v2_pre_topc(A_337)
      | ~ m1_pre_topc(B_338,A_337)
      | ~ l1_pre_topc(A_337) ) ),
    inference(resolution,[status(thm)],[c_34,c_174])).

tff(c_182,plain,
    ( ~ v2_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_179])).

tff(c_186,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_62,c_182])).

tff(c_188,plain,(
    ! [B_339,D_340] :
      ( k1_tops_1(B_339,D_340) = D_340
      | ~ v3_pre_topc(D_340,B_339)
      | ~ m1_subset_1(D_340,k1_zfmisc_1(u1_struct_0(B_339)))
      | ~ l1_pre_topc(B_339) ) ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_193,plain,(
    ! [A_341,B_342] :
      ( k1_tops_1(A_341,u1_struct_0(B_342)) = u1_struct_0(B_342)
      | ~ v3_pre_topc(u1_struct_0(B_342),A_341)
      | ~ m1_pre_topc(B_342,A_341)
      | ~ l1_pre_topc(A_341) ) ),
    inference(resolution,[status(thm)],[c_34,c_188])).

tff(c_208,plain,(
    ! [A_348,B_349] :
      ( k1_tops_1(A_348,u1_struct_0(B_349)) = u1_struct_0(B_349)
      | ~ v1_tsep_1(B_349,A_348)
      | ~ v2_pre_topc(A_348)
      | ~ m1_pre_topc(B_349,A_348)
      | ~ l1_pre_topc(A_348) ) ),
    inference(resolution,[status(thm)],[c_146,c_193])).

tff(c_22,plain,(
    ! [C_38,A_32,B_36] :
      ( m1_connsp_2(C_38,A_32,B_36)
      | ~ r2_hidden(B_36,k1_tops_1(A_32,C_38))
      | ~ m1_subset_1(C_38,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ m1_subset_1(B_36,u1_struct_0(A_32))
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_253,plain,(
    ! [B_369,A_370,B_371] :
      ( m1_connsp_2(u1_struct_0(B_369),A_370,B_371)
      | ~ r2_hidden(B_371,u1_struct_0(B_369))
      | ~ m1_subset_1(u1_struct_0(B_369),k1_zfmisc_1(u1_struct_0(A_370)))
      | ~ m1_subset_1(B_371,u1_struct_0(A_370))
      | ~ l1_pre_topc(A_370)
      | ~ v2_pre_topc(A_370)
      | v2_struct_0(A_370)
      | ~ v1_tsep_1(B_369,A_370)
      | ~ v2_pre_topc(A_370)
      | ~ m1_pre_topc(B_369,A_370)
      | ~ l1_pre_topc(A_370) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_22])).

tff(c_256,plain,(
    ! [B_52,A_50,B_371] :
      ( m1_connsp_2(u1_struct_0(B_52),A_50,B_371)
      | ~ r2_hidden(B_371,u1_struct_0(B_52))
      | ~ m1_subset_1(B_371,u1_struct_0(A_50))
      | v2_struct_0(A_50)
      | ~ v1_tsep_1(B_52,A_50)
      | ~ v2_pre_topc(A_50)
      | ~ m1_pre_topc(B_52,A_50)
      | ~ l1_pre_topc(A_50) ) ),
    inference(resolution,[status(thm)],[c_34,c_253])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_279])).

tff(c_72,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6')
    | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_279])).

tff(c_81,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6')
    | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_72])).

tff(c_106,plain,(
    ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_68,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_279])).

tff(c_66,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_279])).

tff(c_58,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_279])).

tff(c_56,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_279])).

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_279])).

tff(c_78,plain,
    ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_5')
    | r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_279])).

tff(c_79,plain,
    ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
    | r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_78])).

tff(c_107,plain,(
    r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_79])).

tff(c_284,plain,(
    ! [B_386,D_390,A_389,E_388,G_387,C_385] :
      ( r1_tmap_1(B_386,A_389,C_385,G_387)
      | ~ r1_tmap_1(D_390,A_389,k2_tmap_1(B_386,A_389,C_385,D_390),G_387)
      | ~ m1_connsp_2(E_388,B_386,G_387)
      | ~ r1_tarski(E_388,u1_struct_0(D_390))
      | ~ m1_subset_1(G_387,u1_struct_0(D_390))
      | ~ m1_subset_1(G_387,u1_struct_0(B_386))
      | ~ m1_subset_1(E_388,k1_zfmisc_1(u1_struct_0(B_386)))
      | ~ m1_pre_topc(D_390,B_386)
      | v2_struct_0(D_390)
      | ~ m1_subset_1(C_385,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_386),u1_struct_0(A_389))))
      | ~ v1_funct_2(C_385,u1_struct_0(B_386),u1_struct_0(A_389))
      | ~ v1_funct_1(C_385)
      | ~ l1_pre_topc(B_386)
      | ~ v2_pre_topc(B_386)
      | v2_struct_0(B_386)
      | ~ l1_pre_topc(A_389)
      | ~ v2_pre_topc(A_389)
      | v2_struct_0(A_389) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_288,plain,(
    ! [E_388] :
      ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
      | ~ m1_connsp_2(E_388,'#skF_2','#skF_6')
      | ~ r1_tarski(E_388,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_388,k1_zfmisc_1(u1_struct_0('#skF_2')))
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
    inference(resolution,[status(thm)],[c_107,c_284])).

tff(c_295,plain,(
    ! [E_388] :
      ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
      | ~ m1_connsp_2(E_388,'#skF_2','#skF_6')
      | ~ r1_tarski(E_388,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_388,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_62,c_60,c_58,c_56,c_54,c_48,c_80,c_44,c_288])).

tff(c_297,plain,(
    ! [E_391] :
      ( ~ m1_connsp_2(E_391,'#skF_2','#skF_6')
      | ~ r1_tarski(E_391,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_391,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_52,c_106,c_295])).

tff(c_301,plain,(
    ! [B_52] :
      ( ~ m1_connsp_2(u1_struct_0(B_52),'#skF_2','#skF_6')
      | ~ r1_tarski(u1_struct_0(B_52),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_52,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_34,c_297])).

tff(c_305,plain,(
    ! [B_392] :
      ( ~ m1_connsp_2(u1_struct_0(B_392),'#skF_2','#skF_6')
      | ~ r1_tarski(u1_struct_0(B_392),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_392,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_301])).

tff(c_309,plain,
    ( ~ m1_connsp_2(u1_struct_0('#skF_4'),'#skF_2','#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_305])).

tff(c_312,plain,(
    ~ m1_connsp_2(u1_struct_0('#skF_4'),'#skF_2','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_309])).

tff(c_316,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2')
    | ~ v1_tsep_1('#skF_4','#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_256,c_312])).

tff(c_319,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_48,c_62,c_50,c_80,c_316])).

tff(c_320,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_319])).

tff(c_323,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_8,c_320])).

tff(c_326,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_323])).

tff(c_14,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(u1_struct_0(A_9))
      | ~ l1_struct_0(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_329,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_326,c_14])).

tff(c_332,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_329])).

tff(c_354,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_332])).

tff(c_358,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_354])).

tff(c_360,plain,(
    r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_499,plain,(
    ! [F_446,C_448,B_447,A_445,D_449] :
      ( r1_tmap_1(D_449,A_445,k2_tmap_1(B_447,A_445,C_448,D_449),F_446)
      | ~ r1_tmap_1(B_447,A_445,C_448,F_446)
      | ~ m1_subset_1(F_446,u1_struct_0(D_449))
      | ~ m1_subset_1(F_446,u1_struct_0(B_447))
      | ~ m1_pre_topc(D_449,B_447)
      | v2_struct_0(D_449)
      | ~ m1_subset_1(C_448,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_447),u1_struct_0(A_445))))
      | ~ v1_funct_2(C_448,u1_struct_0(B_447),u1_struct_0(A_445))
      | ~ v1_funct_1(C_448)
      | ~ l1_pre_topc(B_447)
      | ~ v2_pre_topc(B_447)
      | v2_struct_0(B_447)
      | ~ l1_pre_topc(A_445)
      | ~ v2_pre_topc(A_445)
      | v2_struct_0(A_445) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_501,plain,(
    ! [D_449,F_446] :
      ( r1_tmap_1(D_449,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_449),F_446)
      | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3',F_446)
      | ~ m1_subset_1(F_446,u1_struct_0(D_449))
      | ~ m1_subset_1(F_446,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_449,'#skF_2')
      | v2_struct_0(D_449)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_54,c_499])).

tff(c_504,plain,(
    ! [D_449,F_446] :
      ( r1_tmap_1(D_449,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_449),F_446)
      | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3',F_446)
      | ~ m1_subset_1(F_446,u1_struct_0(D_449))
      | ~ m1_subset_1(F_446,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_449,'#skF_2')
      | v2_struct_0(D_449)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_62,c_60,c_58,c_56,c_501])).

tff(c_506,plain,(
    ! [D_450,F_451] :
      ( r1_tmap_1(D_450,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_450),F_451)
      | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3',F_451)
      | ~ m1_subset_1(F_451,u1_struct_0(D_450))
      | ~ m1_subset_1(F_451,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_450,'#skF_2')
      | v2_struct_0(D_450) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_504])).

tff(c_359,plain,(
    ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_509,plain,
    ( ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_506,c_359])).

tff(c_512,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_80,c_44,c_360,c_509])).

tff(c_514,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_512])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:57:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.29/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.48  
% 3.29/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.48  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.29/1.48  
% 3.29/1.48  %Foreground sorts:
% 3.29/1.48  
% 3.29/1.48  
% 3.29/1.48  %Background operators:
% 3.29/1.48  
% 3.29/1.48  
% 3.29/1.48  %Foreground operators:
% 3.29/1.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.29/1.48  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.29/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.29/1.48  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.29/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.29/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.29/1.48  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.29/1.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.29/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.29/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.29/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.29/1.48  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.29/1.48  tff('#skF_6', type, '#skF_6': $i).
% 3.29/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.29/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.29/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.29/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.29/1.48  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.29/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.29/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.29/1.48  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.29/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.29/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.29/1.48  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.29/1.48  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.29/1.48  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.29/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.29/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.29/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.29/1.48  
% 3.29/1.50  tff(f_279, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_tmap_1)).
% 3.29/1.50  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.29/1.50  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.29/1.50  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.29/1.50  tff(f_149, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.29/1.50  tff(f_142, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 3.29/1.50  tff(f_93, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 3.29/1.50  tff(f_110, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 3.29/1.50  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.29/1.50  tff(f_236, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tmap_1)).
% 3.29/1.50  tff(f_56, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.29/1.50  tff(f_189, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 3.29/1.50  tff(c_52, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_279])).
% 3.29/1.50  tff(c_48, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_279])).
% 3.29/1.50  tff(c_42, plain, ('#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_279])).
% 3.29/1.50  tff(c_46, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_279])).
% 3.29/1.50  tff(c_80, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_46])).
% 3.29/1.50  tff(c_44, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_279])).
% 3.29/1.50  tff(c_60, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_279])).
% 3.29/1.50  tff(c_90, plain, (![B_303, A_304]: (l1_pre_topc(B_303) | ~m1_pre_topc(B_303, A_304) | ~l1_pre_topc(A_304))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.29/1.50  tff(c_93, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_90])).
% 3.29/1.50  tff(c_96, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_93])).
% 3.29/1.50  tff(c_10, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.29/1.50  tff(c_8, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.29/1.50  tff(c_64, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_279])).
% 3.29/1.50  tff(c_62, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_279])).
% 3.29/1.50  tff(c_50, plain, (v1_tsep_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_279])).
% 3.29/1.50  tff(c_34, plain, (![B_52, A_50]: (m1_subset_1(u1_struct_0(B_52), k1_zfmisc_1(u1_struct_0(A_50))) | ~m1_pre_topc(B_52, A_50) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.29/1.50  tff(c_142, plain, (![B_323, A_324]: (v3_pre_topc(u1_struct_0(B_323), A_324) | ~v1_tsep_1(B_323, A_324) | ~m1_subset_1(u1_struct_0(B_323), k1_zfmisc_1(u1_struct_0(A_324))) | ~m1_pre_topc(B_323, A_324) | ~l1_pre_topc(A_324) | ~v2_pre_topc(A_324))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.29/1.50  tff(c_146, plain, (![B_52, A_50]: (v3_pre_topc(u1_struct_0(B_52), A_50) | ~v1_tsep_1(B_52, A_50) | ~v2_pre_topc(A_50) | ~m1_pre_topc(B_52, A_50) | ~l1_pre_topc(A_50))), inference(resolution, [status(thm)], [c_34, c_142])).
% 3.29/1.50  tff(c_20, plain, (![B_25, D_31, C_29, A_17]: (k1_tops_1(B_25, D_31)=D_31 | ~v3_pre_topc(D_31, B_25) | ~m1_subset_1(D_31, k1_zfmisc_1(u1_struct_0(B_25))) | ~m1_subset_1(C_29, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(B_25) | ~l1_pre_topc(A_17) | ~v2_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.29/1.50  tff(c_174, plain, (![C_335, A_336]: (~m1_subset_1(C_335, k1_zfmisc_1(u1_struct_0(A_336))) | ~l1_pre_topc(A_336) | ~v2_pre_topc(A_336))), inference(splitLeft, [status(thm)], [c_20])).
% 3.29/1.50  tff(c_179, plain, (![A_337, B_338]: (~v2_pre_topc(A_337) | ~m1_pre_topc(B_338, A_337) | ~l1_pre_topc(A_337))), inference(resolution, [status(thm)], [c_34, c_174])).
% 3.29/1.50  tff(c_182, plain, (~v2_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_179])).
% 3.29/1.50  tff(c_186, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_62, c_182])).
% 3.29/1.50  tff(c_188, plain, (![B_339, D_340]: (k1_tops_1(B_339, D_340)=D_340 | ~v3_pre_topc(D_340, B_339) | ~m1_subset_1(D_340, k1_zfmisc_1(u1_struct_0(B_339))) | ~l1_pre_topc(B_339))), inference(splitRight, [status(thm)], [c_20])).
% 3.29/1.50  tff(c_193, plain, (![A_341, B_342]: (k1_tops_1(A_341, u1_struct_0(B_342))=u1_struct_0(B_342) | ~v3_pre_topc(u1_struct_0(B_342), A_341) | ~m1_pre_topc(B_342, A_341) | ~l1_pre_topc(A_341))), inference(resolution, [status(thm)], [c_34, c_188])).
% 3.29/1.50  tff(c_208, plain, (![A_348, B_349]: (k1_tops_1(A_348, u1_struct_0(B_349))=u1_struct_0(B_349) | ~v1_tsep_1(B_349, A_348) | ~v2_pre_topc(A_348) | ~m1_pre_topc(B_349, A_348) | ~l1_pre_topc(A_348))), inference(resolution, [status(thm)], [c_146, c_193])).
% 3.29/1.50  tff(c_22, plain, (![C_38, A_32, B_36]: (m1_connsp_2(C_38, A_32, B_36) | ~r2_hidden(B_36, k1_tops_1(A_32, C_38)) | ~m1_subset_1(C_38, k1_zfmisc_1(u1_struct_0(A_32))) | ~m1_subset_1(B_36, u1_struct_0(A_32)) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.29/1.50  tff(c_253, plain, (![B_369, A_370, B_371]: (m1_connsp_2(u1_struct_0(B_369), A_370, B_371) | ~r2_hidden(B_371, u1_struct_0(B_369)) | ~m1_subset_1(u1_struct_0(B_369), k1_zfmisc_1(u1_struct_0(A_370))) | ~m1_subset_1(B_371, u1_struct_0(A_370)) | ~l1_pre_topc(A_370) | ~v2_pre_topc(A_370) | v2_struct_0(A_370) | ~v1_tsep_1(B_369, A_370) | ~v2_pre_topc(A_370) | ~m1_pre_topc(B_369, A_370) | ~l1_pre_topc(A_370))), inference(superposition, [status(thm), theory('equality')], [c_208, c_22])).
% 3.29/1.50  tff(c_256, plain, (![B_52, A_50, B_371]: (m1_connsp_2(u1_struct_0(B_52), A_50, B_371) | ~r2_hidden(B_371, u1_struct_0(B_52)) | ~m1_subset_1(B_371, u1_struct_0(A_50)) | v2_struct_0(A_50) | ~v1_tsep_1(B_52, A_50) | ~v2_pre_topc(A_50) | ~m1_pre_topc(B_52, A_50) | ~l1_pre_topc(A_50))), inference(resolution, [status(thm)], [c_34, c_253])).
% 3.29/1.50  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.29/1.50  tff(c_70, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_279])).
% 3.29/1.50  tff(c_72, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6') | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_279])).
% 3.29/1.50  tff(c_81, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6') | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_72])).
% 3.29/1.50  tff(c_106, plain, (~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(splitLeft, [status(thm)], [c_81])).
% 3.29/1.50  tff(c_68, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_279])).
% 3.29/1.50  tff(c_66, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_279])).
% 3.29/1.50  tff(c_58, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_279])).
% 3.29/1.50  tff(c_56, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_279])).
% 3.29/1.50  tff(c_54, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_279])).
% 3.29/1.50  tff(c_78, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_5') | r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_279])).
% 3.29/1.50  tff(c_79, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_78])).
% 3.29/1.50  tff(c_107, plain, (r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_106, c_79])).
% 3.29/1.50  tff(c_284, plain, (![B_386, D_390, A_389, E_388, G_387, C_385]: (r1_tmap_1(B_386, A_389, C_385, G_387) | ~r1_tmap_1(D_390, A_389, k2_tmap_1(B_386, A_389, C_385, D_390), G_387) | ~m1_connsp_2(E_388, B_386, G_387) | ~r1_tarski(E_388, u1_struct_0(D_390)) | ~m1_subset_1(G_387, u1_struct_0(D_390)) | ~m1_subset_1(G_387, u1_struct_0(B_386)) | ~m1_subset_1(E_388, k1_zfmisc_1(u1_struct_0(B_386))) | ~m1_pre_topc(D_390, B_386) | v2_struct_0(D_390) | ~m1_subset_1(C_385, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_386), u1_struct_0(A_389)))) | ~v1_funct_2(C_385, u1_struct_0(B_386), u1_struct_0(A_389)) | ~v1_funct_1(C_385) | ~l1_pre_topc(B_386) | ~v2_pre_topc(B_386) | v2_struct_0(B_386) | ~l1_pre_topc(A_389) | ~v2_pre_topc(A_389) | v2_struct_0(A_389))), inference(cnfTransformation, [status(thm)], [f_236])).
% 3.29/1.50  tff(c_288, plain, (![E_388]: (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | ~m1_connsp_2(E_388, '#skF_2', '#skF_6') | ~r1_tarski(E_388, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | ~m1_subset_1(E_388, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_107, c_284])).
% 3.29/1.51  tff(c_295, plain, (![E_388]: (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | ~m1_connsp_2(E_388, '#skF_2', '#skF_6') | ~r1_tarski(E_388, u1_struct_0('#skF_4')) | ~m1_subset_1(E_388, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_62, c_60, c_58, c_56, c_54, c_48, c_80, c_44, c_288])).
% 3.29/1.51  tff(c_297, plain, (![E_391]: (~m1_connsp_2(E_391, '#skF_2', '#skF_6') | ~r1_tarski(E_391, u1_struct_0('#skF_4')) | ~m1_subset_1(E_391, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_52, c_106, c_295])).
% 3.29/1.51  tff(c_301, plain, (![B_52]: (~m1_connsp_2(u1_struct_0(B_52), '#skF_2', '#skF_6') | ~r1_tarski(u1_struct_0(B_52), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_52, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_297])).
% 3.29/1.51  tff(c_305, plain, (![B_392]: (~m1_connsp_2(u1_struct_0(B_392), '#skF_2', '#skF_6') | ~r1_tarski(u1_struct_0(B_392), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_392, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_301])).
% 3.29/1.51  tff(c_309, plain, (~m1_connsp_2(u1_struct_0('#skF_4'), '#skF_2', '#skF_6') | ~m1_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_6, c_305])).
% 3.29/1.51  tff(c_312, plain, (~m1_connsp_2(u1_struct_0('#skF_4'), '#skF_2', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_309])).
% 3.29/1.51  tff(c_316, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~v1_tsep_1('#skF_4', '#skF_2') | ~v2_pre_topc('#skF_2') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_256, c_312])).
% 3.29/1.51  tff(c_319, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_4')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_48, c_62, c_50, c_80, c_316])).
% 3.29/1.51  tff(c_320, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_64, c_319])).
% 3.29/1.51  tff(c_323, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_8, c_320])).
% 3.29/1.51  tff(c_326, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_323])).
% 3.29/1.51  tff(c_14, plain, (![A_9]: (~v1_xboole_0(u1_struct_0(A_9)) | ~l1_struct_0(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.29/1.51  tff(c_329, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_326, c_14])).
% 3.29/1.51  tff(c_332, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_52, c_329])).
% 3.29/1.51  tff(c_354, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_10, c_332])).
% 3.29/1.51  tff(c_358, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_354])).
% 3.29/1.51  tff(c_360, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(splitRight, [status(thm)], [c_81])).
% 3.29/1.51  tff(c_499, plain, (![F_446, C_448, B_447, A_445, D_449]: (r1_tmap_1(D_449, A_445, k2_tmap_1(B_447, A_445, C_448, D_449), F_446) | ~r1_tmap_1(B_447, A_445, C_448, F_446) | ~m1_subset_1(F_446, u1_struct_0(D_449)) | ~m1_subset_1(F_446, u1_struct_0(B_447)) | ~m1_pre_topc(D_449, B_447) | v2_struct_0(D_449) | ~m1_subset_1(C_448, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_447), u1_struct_0(A_445)))) | ~v1_funct_2(C_448, u1_struct_0(B_447), u1_struct_0(A_445)) | ~v1_funct_1(C_448) | ~l1_pre_topc(B_447) | ~v2_pre_topc(B_447) | v2_struct_0(B_447) | ~l1_pre_topc(A_445) | ~v2_pre_topc(A_445) | v2_struct_0(A_445))), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.29/1.51  tff(c_501, plain, (![D_449, F_446]: (r1_tmap_1(D_449, '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', D_449), F_446) | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', F_446) | ~m1_subset_1(F_446, u1_struct_0(D_449)) | ~m1_subset_1(F_446, u1_struct_0('#skF_2')) | ~m1_pre_topc(D_449, '#skF_2') | v2_struct_0(D_449) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_54, c_499])).
% 3.29/1.51  tff(c_504, plain, (![D_449, F_446]: (r1_tmap_1(D_449, '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', D_449), F_446) | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', F_446) | ~m1_subset_1(F_446, u1_struct_0(D_449)) | ~m1_subset_1(F_446, u1_struct_0('#skF_2')) | ~m1_pre_topc(D_449, '#skF_2') | v2_struct_0(D_449) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_62, c_60, c_58, c_56, c_501])).
% 3.29/1.51  tff(c_506, plain, (![D_450, F_451]: (r1_tmap_1(D_450, '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', D_450), F_451) | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', F_451) | ~m1_subset_1(F_451, u1_struct_0(D_450)) | ~m1_subset_1(F_451, u1_struct_0('#skF_2')) | ~m1_pre_topc(D_450, '#skF_2') | v2_struct_0(D_450))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_504])).
% 3.29/1.51  tff(c_359, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(splitRight, [status(thm)], [c_81])).
% 3.29/1.51  tff(c_509, plain, (~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_506, c_359])).
% 3.29/1.51  tff(c_512, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_80, c_44, c_360, c_509])).
% 3.29/1.51  tff(c_514, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_512])).
% 3.29/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.51  
% 3.29/1.51  Inference rules
% 3.29/1.51  ----------------------
% 3.29/1.51  #Ref     : 0
% 3.29/1.51  #Sup     : 79
% 3.29/1.51  #Fact    : 0
% 3.29/1.51  #Define  : 0
% 3.29/1.51  #Split   : 5
% 3.29/1.51  #Chain   : 0
% 3.29/1.51  #Close   : 0
% 3.29/1.51  
% 3.29/1.51  Ordering : KBO
% 3.29/1.51  
% 3.29/1.51  Simplification rules
% 3.29/1.51  ----------------------
% 3.29/1.51  #Subsume      : 32
% 3.29/1.51  #Demod        : 70
% 3.29/1.51  #Tautology    : 26
% 3.29/1.51  #SimpNegUnit  : 19
% 3.29/1.51  #BackRed      : 0
% 3.29/1.51  
% 3.29/1.51  #Partial instantiations: 0
% 3.29/1.51  #Strategies tried      : 1
% 3.29/1.51  
% 3.29/1.51  Timing (in seconds)
% 3.29/1.51  ----------------------
% 3.29/1.51  Preprocessing        : 0.40
% 3.29/1.51  Parsing              : 0.21
% 3.29/1.51  CNF conversion       : 0.05
% 3.29/1.51  Main loop            : 0.32
% 3.29/1.51  Inferencing          : 0.12
% 3.29/1.51  Reduction            : 0.10
% 3.29/1.51  Demodulation         : 0.07
% 3.29/1.51  BG Simplification    : 0.02
% 3.29/1.51  Subsumption          : 0.06
% 3.29/1.51  Abstraction          : 0.01
% 3.29/1.51  MUC search           : 0.00
% 3.29/1.51  Cooper               : 0.00
% 3.29/1.51  Total                : 0.76
% 3.29/1.51  Index Insertion      : 0.00
% 3.29/1.51  Index Deletion       : 0.00
% 3.29/1.51  Index Matching       : 0.00
% 3.29/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
