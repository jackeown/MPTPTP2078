%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:08 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 290 expanded)
%              Number of leaves         :   38 ( 126 expanded)
%              Depth                    :   19
%              Number of atoms          :  297 (1920 expanded)
%              Number of equality atoms :    5 (  97 expanded)
%              Maximal formula depth    :   26 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_241,negated_conjecture,(
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

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_84,axiom,(
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

tff(f_109,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_198,axiom,(
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

tff(f_50,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_149,axiom,(
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

tff(c_42,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_38,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_32,plain,(
    '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_70,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_36])).

tff(c_34,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_78,plain,(
    ! [B_282,A_283] :
      ( l1_pre_topc(B_282)
      | ~ m1_pre_topc(B_282,A_283)
      | ~ l1_pre_topc(A_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_84,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_78])).

tff(c_88,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_84])).

tff(c_4,plain,(
    ! [A_3] :
      ( l1_struct_0(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ! [A_25] :
      ( m1_pre_topc(A_25,A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_40,plain,(
    v1_tsep_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_18,plain,(
    ! [B_24,A_22] :
      ( m1_subset_1(u1_struct_0(B_24),k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ m1_pre_topc(B_24,A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_157,plain,(
    ! [B_309,A_310] :
      ( v3_pre_topc(u1_struct_0(B_309),A_310)
      | ~ v1_tsep_1(B_309,A_310)
      | ~ m1_subset_1(u1_struct_0(B_309),k1_zfmisc_1(u1_struct_0(A_310)))
      | ~ m1_pre_topc(B_309,A_310)
      | ~ l1_pre_topc(A_310)
      | ~ v2_pre_topc(A_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_161,plain,(
    ! [B_24,A_22] :
      ( v3_pre_topc(u1_struct_0(B_24),A_22)
      | ~ v1_tsep_1(B_24,A_22)
      | ~ v2_pre_topc(A_22)
      | ~ m1_pre_topc(B_24,A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(resolution,[status(thm)],[c_18,c_157])).

tff(c_125,plain,(
    ! [B_299,C_300,A_301] :
      ( r1_tarski(u1_struct_0(B_299),u1_struct_0(C_300))
      | ~ m1_pre_topc(B_299,C_300)
      | ~ m1_pre_topc(C_300,A_301)
      | ~ m1_pre_topc(B_299,A_301)
      | ~ l1_pre_topc(A_301)
      | ~ v2_pre_topc(A_301) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_129,plain,(
    ! [B_299] :
      ( r1_tarski(u1_struct_0(B_299),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_299,'#skF_4')
      | ~ m1_pre_topc(B_299,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_38,c_125])).

tff(c_133,plain,(
    ! [B_299] :
      ( r1_tarski(u1_struct_0(B_299),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_299,'#skF_4')
      | ~ m1_pre_topc(B_299,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_129])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_68,plain,
    ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_5')
    | r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_69,plain,
    ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
    | r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_68])).

tff(c_92,plain,(
    r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_69])).

tff(c_62,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6')
    | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_71,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6')
    | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_62])).

tff(c_94,plain,(
    ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_71])).

tff(c_58,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_56,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_48,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_46,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_176,plain,(
    ! [C_322,D_325,E_327,G_324,A_323,B_326] :
      ( r1_tmap_1(B_326,A_323,C_322,G_324)
      | ~ r1_tmap_1(D_325,A_323,k2_tmap_1(B_326,A_323,C_322,D_325),G_324)
      | ~ r1_tarski(E_327,u1_struct_0(D_325))
      | ~ r2_hidden(G_324,E_327)
      | ~ v3_pre_topc(E_327,B_326)
      | ~ m1_subset_1(G_324,u1_struct_0(D_325))
      | ~ m1_subset_1(G_324,u1_struct_0(B_326))
      | ~ m1_subset_1(E_327,k1_zfmisc_1(u1_struct_0(B_326)))
      | ~ m1_pre_topc(D_325,B_326)
      | v2_struct_0(D_325)
      | ~ m1_subset_1(C_322,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_326),u1_struct_0(A_323))))
      | ~ v1_funct_2(C_322,u1_struct_0(B_326),u1_struct_0(A_323))
      | ~ v1_funct_1(C_322)
      | ~ l1_pre_topc(B_326)
      | ~ v2_pre_topc(B_326)
      | v2_struct_0(B_326)
      | ~ l1_pre_topc(A_323)
      | ~ v2_pre_topc(A_323)
      | v2_struct_0(A_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_180,plain,(
    ! [E_327] :
      ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
      | ~ r1_tarski(E_327,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_6',E_327)
      | ~ v3_pre_topc(E_327,'#skF_2')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_327,k1_zfmisc_1(u1_struct_0('#skF_2')))
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
    inference(resolution,[status(thm)],[c_92,c_176])).

tff(c_187,plain,(
    ! [E_327] :
      ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
      | ~ r1_tarski(E_327,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_6',E_327)
      | ~ v3_pre_topc(E_327,'#skF_2')
      | ~ m1_subset_1(E_327,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_48,c_46,c_44,c_38,c_70,c_34,c_180])).

tff(c_189,plain,(
    ! [E_328] :
      ( ~ r1_tarski(E_328,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_6',E_328)
      | ~ v3_pre_topc(E_328,'#skF_2')
      | ~ m1_subset_1(E_328,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_42,c_94,c_187])).

tff(c_193,plain,(
    ! [B_24] :
      ( ~ r1_tarski(u1_struct_0(B_24),u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_6',u1_struct_0(B_24))
      | ~ v3_pre_topc(u1_struct_0(B_24),'#skF_2')
      | ~ m1_pre_topc(B_24,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_189])).

tff(c_197,plain,(
    ! [B_329] :
      ( ~ r1_tarski(u1_struct_0(B_329),u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_6',u1_struct_0(B_329))
      | ~ v3_pre_topc(u1_struct_0(B_329),'#skF_2')
      | ~ m1_pre_topc(B_329,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_193])).

tff(c_209,plain,(
    ! [B_330] :
      ( ~ r2_hidden('#skF_6',u1_struct_0(B_330))
      | ~ v3_pre_topc(u1_struct_0(B_330),'#skF_2')
      | ~ m1_pre_topc(B_330,'#skF_4')
      | ~ m1_pre_topc(B_330,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_133,c_197])).

tff(c_213,plain,(
    ! [B_24] :
      ( ~ r2_hidden('#skF_6',u1_struct_0(B_24))
      | ~ m1_pre_topc(B_24,'#skF_4')
      | ~ v1_tsep_1(B_24,'#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ m1_pre_topc(B_24,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_161,c_209])).

tff(c_217,plain,(
    ! [B_331] :
      ( ~ r2_hidden('#skF_6',u1_struct_0(B_331))
      | ~ m1_pre_topc(B_331,'#skF_4')
      | ~ v1_tsep_1(B_331,'#skF_2')
      | ~ m1_pre_topc(B_331,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_213])).

tff(c_222,plain,(
    ! [B_332] :
      ( ~ m1_pre_topc(B_332,'#skF_4')
      | ~ v1_tsep_1(B_332,'#skF_2')
      | ~ m1_pre_topc(B_332,'#skF_2')
      | v1_xboole_0(u1_struct_0(B_332))
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_332)) ) ),
    inference(resolution,[status(thm)],[c_2,c_217])).

tff(c_231,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ v1_tsep_1('#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_34,c_222])).

tff(c_239,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40,c_231])).

tff(c_241,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_239])).

tff(c_244,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_241])).

tff(c_248,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_244])).

tff(c_249,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_239])).

tff(c_8,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0(u1_struct_0(A_7))
      | ~ l1_struct_0(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_332,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_249,c_8])).

tff(c_335,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_332])).

tff(c_339,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_335])).

tff(c_343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_339])).

tff(c_344,plain,(
    r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_421,plain,(
    ! [F_361,D_362,B_360,A_359,C_363] :
      ( r1_tmap_1(D_362,A_359,k2_tmap_1(B_360,A_359,C_363,D_362),F_361)
      | ~ r1_tmap_1(B_360,A_359,C_363,F_361)
      | ~ m1_subset_1(F_361,u1_struct_0(D_362))
      | ~ m1_subset_1(F_361,u1_struct_0(B_360))
      | ~ m1_pre_topc(D_362,B_360)
      | v2_struct_0(D_362)
      | ~ m1_subset_1(C_363,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_360),u1_struct_0(A_359))))
      | ~ v1_funct_2(C_363,u1_struct_0(B_360),u1_struct_0(A_359))
      | ~ v1_funct_1(C_363)
      | ~ l1_pre_topc(B_360)
      | ~ v2_pre_topc(B_360)
      | v2_struct_0(B_360)
      | ~ l1_pre_topc(A_359)
      | ~ v2_pre_topc(A_359)
      | v2_struct_0(A_359) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_423,plain,(
    ! [D_362,F_361] :
      ( r1_tmap_1(D_362,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_362),F_361)
      | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3',F_361)
      | ~ m1_subset_1(F_361,u1_struct_0(D_362))
      | ~ m1_subset_1(F_361,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_362,'#skF_2')
      | v2_struct_0(D_362)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_421])).

tff(c_426,plain,(
    ! [D_362,F_361] :
      ( r1_tmap_1(D_362,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_362),F_361)
      | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3',F_361)
      | ~ m1_subset_1(F_361,u1_struct_0(D_362))
      | ~ m1_subset_1(F_361,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_362,'#skF_2')
      | v2_struct_0(D_362)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_48,c_46,c_423])).

tff(c_428,plain,(
    ! [D_364,F_365] :
      ( r1_tmap_1(D_364,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_364),F_365)
      | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3',F_365)
      | ~ m1_subset_1(F_365,u1_struct_0(D_364))
      | ~ m1_subset_1(F_365,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_364,'#skF_2')
      | v2_struct_0(D_364) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_426])).

tff(c_345,plain,(
    ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_431,plain,
    ( ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_428,c_345])).

tff(c_434,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_70,c_34,c_344,c_431])).

tff(c_436,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_434])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:26:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.41  
% 3.11/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.41  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.11/1.41  
% 3.11/1.41  %Foreground sorts:
% 3.11/1.41  
% 3.11/1.41  
% 3.11/1.41  %Background operators:
% 3.11/1.41  
% 3.11/1.41  
% 3.11/1.41  %Foreground operators:
% 3.11/1.41  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.11/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.11/1.41  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.11/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.11/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.11/1.41  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.11/1.41  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.11/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.11/1.41  tff('#skF_5', type, '#skF_5': $i).
% 3.11/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.11/1.41  tff('#skF_6', type, '#skF_6': $i).
% 3.11/1.41  tff('#skF_2', type, '#skF_2': $i).
% 3.11/1.41  tff('#skF_3', type, '#skF_3': $i).
% 3.11/1.41  tff('#skF_1', type, '#skF_1': $i).
% 3.11/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.11/1.41  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.11/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.11/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.11/1.41  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.11/1.41  tff('#skF_4', type, '#skF_4': $i).
% 3.11/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.11/1.41  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.11/1.41  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.11/1.41  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.11/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.11/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.11/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.11/1.41  
% 3.38/1.43  tff(f_241, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_tmap_1)).
% 3.38/1.43  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.38/1.43  tff(f_35, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.38/1.43  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 3.38/1.43  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.38/1.43  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.38/1.43  tff(f_84, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 3.38/1.43  tff(f_109, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 3.38/1.43  tff(f_198, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((v3_pre_topc(E, B) & r2_hidden(F, E)) & r1_tarski(E, u1_struct_0(D))) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tmap_1)).
% 3.38/1.43  tff(f_50, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.38/1.43  tff(f_149, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 3.38/1.43  tff(c_42, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_241])).
% 3.38/1.43  tff(c_38, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_241])).
% 3.38/1.43  tff(c_32, plain, ('#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_241])).
% 3.38/1.43  tff(c_36, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_241])).
% 3.38/1.43  tff(c_70, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_36])).
% 3.38/1.43  tff(c_34, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_241])).
% 3.38/1.43  tff(c_50, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_241])).
% 3.38/1.43  tff(c_78, plain, (![B_282, A_283]: (l1_pre_topc(B_282) | ~m1_pre_topc(B_282, A_283) | ~l1_pre_topc(A_283))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.38/1.43  tff(c_84, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_78])).
% 3.38/1.43  tff(c_88, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_84])).
% 3.38/1.43  tff(c_4, plain, (![A_3]: (l1_struct_0(A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.38/1.43  tff(c_20, plain, (![A_25]: (m1_pre_topc(A_25, A_25) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.38/1.43  tff(c_40, plain, (v1_tsep_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_241])).
% 3.38/1.43  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.38/1.43  tff(c_52, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_241])).
% 3.38/1.43  tff(c_18, plain, (![B_24, A_22]: (m1_subset_1(u1_struct_0(B_24), k1_zfmisc_1(u1_struct_0(A_22))) | ~m1_pre_topc(B_24, A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.38/1.43  tff(c_157, plain, (![B_309, A_310]: (v3_pre_topc(u1_struct_0(B_309), A_310) | ~v1_tsep_1(B_309, A_310) | ~m1_subset_1(u1_struct_0(B_309), k1_zfmisc_1(u1_struct_0(A_310))) | ~m1_pre_topc(B_309, A_310) | ~l1_pre_topc(A_310) | ~v2_pre_topc(A_310))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.38/1.43  tff(c_161, plain, (![B_24, A_22]: (v3_pre_topc(u1_struct_0(B_24), A_22) | ~v1_tsep_1(B_24, A_22) | ~v2_pre_topc(A_22) | ~m1_pre_topc(B_24, A_22) | ~l1_pre_topc(A_22))), inference(resolution, [status(thm)], [c_18, c_157])).
% 3.38/1.43  tff(c_125, plain, (![B_299, C_300, A_301]: (r1_tarski(u1_struct_0(B_299), u1_struct_0(C_300)) | ~m1_pre_topc(B_299, C_300) | ~m1_pre_topc(C_300, A_301) | ~m1_pre_topc(B_299, A_301) | ~l1_pre_topc(A_301) | ~v2_pre_topc(A_301))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.38/1.43  tff(c_129, plain, (![B_299]: (r1_tarski(u1_struct_0(B_299), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_299, '#skF_4') | ~m1_pre_topc(B_299, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_125])).
% 3.38/1.43  tff(c_133, plain, (![B_299]: (r1_tarski(u1_struct_0(B_299), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_299, '#skF_4') | ~m1_pre_topc(B_299, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_129])).
% 3.38/1.43  tff(c_60, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_241])).
% 3.38/1.43  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_241])).
% 3.38/1.43  tff(c_68, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_5') | r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_241])).
% 3.38/1.43  tff(c_69, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_68])).
% 3.38/1.43  tff(c_92, plain, (r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_69])).
% 3.38/1.43  tff(c_62, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6') | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_241])).
% 3.38/1.43  tff(c_71, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6') | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_62])).
% 3.38/1.43  tff(c_94, plain, (~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_71])).
% 3.38/1.43  tff(c_58, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_241])).
% 3.38/1.43  tff(c_56, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_241])).
% 3.38/1.43  tff(c_48, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_241])).
% 3.38/1.43  tff(c_46, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_241])).
% 3.38/1.43  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_241])).
% 3.38/1.43  tff(c_176, plain, (![C_322, D_325, E_327, G_324, A_323, B_326]: (r1_tmap_1(B_326, A_323, C_322, G_324) | ~r1_tmap_1(D_325, A_323, k2_tmap_1(B_326, A_323, C_322, D_325), G_324) | ~r1_tarski(E_327, u1_struct_0(D_325)) | ~r2_hidden(G_324, E_327) | ~v3_pre_topc(E_327, B_326) | ~m1_subset_1(G_324, u1_struct_0(D_325)) | ~m1_subset_1(G_324, u1_struct_0(B_326)) | ~m1_subset_1(E_327, k1_zfmisc_1(u1_struct_0(B_326))) | ~m1_pre_topc(D_325, B_326) | v2_struct_0(D_325) | ~m1_subset_1(C_322, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_326), u1_struct_0(A_323)))) | ~v1_funct_2(C_322, u1_struct_0(B_326), u1_struct_0(A_323)) | ~v1_funct_1(C_322) | ~l1_pre_topc(B_326) | ~v2_pre_topc(B_326) | v2_struct_0(B_326) | ~l1_pre_topc(A_323) | ~v2_pre_topc(A_323) | v2_struct_0(A_323))), inference(cnfTransformation, [status(thm)], [f_198])).
% 3.38/1.43  tff(c_180, plain, (![E_327]: (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | ~r1_tarski(E_327, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_6', E_327) | ~v3_pre_topc(E_327, '#skF_2') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | ~m1_subset_1(E_327, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_92, c_176])).
% 3.38/1.43  tff(c_187, plain, (![E_327]: (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | ~r1_tarski(E_327, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_6', E_327) | ~v3_pre_topc(E_327, '#skF_2') | ~m1_subset_1(E_327, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_48, c_46, c_44, c_38, c_70, c_34, c_180])).
% 3.38/1.43  tff(c_189, plain, (![E_328]: (~r1_tarski(E_328, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_6', E_328) | ~v3_pre_topc(E_328, '#skF_2') | ~m1_subset_1(E_328, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_42, c_94, c_187])).
% 3.38/1.43  tff(c_193, plain, (![B_24]: (~r1_tarski(u1_struct_0(B_24), u1_struct_0('#skF_4')) | ~r2_hidden('#skF_6', u1_struct_0(B_24)) | ~v3_pre_topc(u1_struct_0(B_24), '#skF_2') | ~m1_pre_topc(B_24, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_18, c_189])).
% 3.38/1.43  tff(c_197, plain, (![B_329]: (~r1_tarski(u1_struct_0(B_329), u1_struct_0('#skF_4')) | ~r2_hidden('#skF_6', u1_struct_0(B_329)) | ~v3_pre_topc(u1_struct_0(B_329), '#skF_2') | ~m1_pre_topc(B_329, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_193])).
% 3.38/1.43  tff(c_209, plain, (![B_330]: (~r2_hidden('#skF_6', u1_struct_0(B_330)) | ~v3_pre_topc(u1_struct_0(B_330), '#skF_2') | ~m1_pre_topc(B_330, '#skF_4') | ~m1_pre_topc(B_330, '#skF_2'))), inference(resolution, [status(thm)], [c_133, c_197])).
% 3.38/1.43  tff(c_213, plain, (![B_24]: (~r2_hidden('#skF_6', u1_struct_0(B_24)) | ~m1_pre_topc(B_24, '#skF_4') | ~v1_tsep_1(B_24, '#skF_2') | ~v2_pre_topc('#skF_2') | ~m1_pre_topc(B_24, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_161, c_209])).
% 3.38/1.43  tff(c_217, plain, (![B_331]: (~r2_hidden('#skF_6', u1_struct_0(B_331)) | ~m1_pre_topc(B_331, '#skF_4') | ~v1_tsep_1(B_331, '#skF_2') | ~m1_pre_topc(B_331, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_213])).
% 3.38/1.43  tff(c_222, plain, (![B_332]: (~m1_pre_topc(B_332, '#skF_4') | ~v1_tsep_1(B_332, '#skF_2') | ~m1_pre_topc(B_332, '#skF_2') | v1_xboole_0(u1_struct_0(B_332)) | ~m1_subset_1('#skF_6', u1_struct_0(B_332)))), inference(resolution, [status(thm)], [c_2, c_217])).
% 3.38/1.43  tff(c_231, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~v1_tsep_1('#skF_4', '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_2') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_222])).
% 3.38/1.43  tff(c_239, plain, (~m1_pre_topc('#skF_4', '#skF_4') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40, c_231])).
% 3.38/1.43  tff(c_241, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_239])).
% 3.38/1.43  tff(c_244, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_20, c_241])).
% 3.38/1.43  tff(c_248, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_244])).
% 3.38/1.43  tff(c_249, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_239])).
% 3.38/1.43  tff(c_8, plain, (![A_7]: (~v1_xboole_0(u1_struct_0(A_7)) | ~l1_struct_0(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.38/1.43  tff(c_332, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_249, c_8])).
% 3.38/1.43  tff(c_335, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_42, c_332])).
% 3.38/1.43  tff(c_339, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_4, c_335])).
% 3.38/1.43  tff(c_343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_339])).
% 3.38/1.43  tff(c_344, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(splitRight, [status(thm)], [c_69])).
% 3.38/1.43  tff(c_421, plain, (![F_361, D_362, B_360, A_359, C_363]: (r1_tmap_1(D_362, A_359, k2_tmap_1(B_360, A_359, C_363, D_362), F_361) | ~r1_tmap_1(B_360, A_359, C_363, F_361) | ~m1_subset_1(F_361, u1_struct_0(D_362)) | ~m1_subset_1(F_361, u1_struct_0(B_360)) | ~m1_pre_topc(D_362, B_360) | v2_struct_0(D_362) | ~m1_subset_1(C_363, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_360), u1_struct_0(A_359)))) | ~v1_funct_2(C_363, u1_struct_0(B_360), u1_struct_0(A_359)) | ~v1_funct_1(C_363) | ~l1_pre_topc(B_360) | ~v2_pre_topc(B_360) | v2_struct_0(B_360) | ~l1_pre_topc(A_359) | ~v2_pre_topc(A_359) | v2_struct_0(A_359))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.38/1.43  tff(c_423, plain, (![D_362, F_361]: (r1_tmap_1(D_362, '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', D_362), F_361) | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', F_361) | ~m1_subset_1(F_361, u1_struct_0(D_362)) | ~m1_subset_1(F_361, u1_struct_0('#skF_2')) | ~m1_pre_topc(D_362, '#skF_2') | v2_struct_0(D_362) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_421])).
% 3.38/1.43  tff(c_426, plain, (![D_362, F_361]: (r1_tmap_1(D_362, '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', D_362), F_361) | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', F_361) | ~m1_subset_1(F_361, u1_struct_0(D_362)) | ~m1_subset_1(F_361, u1_struct_0('#skF_2')) | ~m1_pre_topc(D_362, '#skF_2') | v2_struct_0(D_362) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_48, c_46, c_423])).
% 3.38/1.43  tff(c_428, plain, (![D_364, F_365]: (r1_tmap_1(D_364, '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', D_364), F_365) | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', F_365) | ~m1_subset_1(F_365, u1_struct_0(D_364)) | ~m1_subset_1(F_365, u1_struct_0('#skF_2')) | ~m1_pre_topc(D_364, '#skF_2') | v2_struct_0(D_364))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_426])).
% 3.38/1.43  tff(c_345, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(splitRight, [status(thm)], [c_69])).
% 3.38/1.43  tff(c_431, plain, (~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_428, c_345])).
% 3.38/1.43  tff(c_434, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_70, c_34, c_344, c_431])).
% 3.38/1.43  tff(c_436, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_434])).
% 3.38/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.43  
% 3.38/1.43  Inference rules
% 3.38/1.43  ----------------------
% 3.38/1.43  #Ref     : 0
% 3.38/1.43  #Sup     : 64
% 3.38/1.43  #Fact    : 0
% 3.38/1.43  #Define  : 0
% 3.38/1.43  #Split   : 4
% 3.38/1.43  #Chain   : 0
% 3.38/1.43  #Close   : 0
% 3.38/1.43  
% 3.38/1.43  Ordering : KBO
% 3.38/1.43  
% 3.38/1.43  Simplification rules
% 3.38/1.43  ----------------------
% 3.38/1.43  #Subsume      : 11
% 3.38/1.43  #Demod        : 90
% 3.38/1.43  #Tautology    : 26
% 3.38/1.43  #SimpNegUnit  : 20
% 3.38/1.43  #BackRed      : 0
% 3.38/1.43  
% 3.38/1.43  #Partial instantiations: 0
% 3.38/1.43  #Strategies tried      : 1
% 3.38/1.43  
% 3.38/1.43  Timing (in seconds)
% 3.38/1.43  ----------------------
% 3.38/1.43  Preprocessing        : 0.38
% 3.38/1.43  Parsing              : 0.19
% 3.38/1.43  CNF conversion       : 0.05
% 3.38/1.44  Main loop            : 0.29
% 3.38/1.44  Inferencing          : 0.10
% 3.38/1.44  Reduction            : 0.09
% 3.38/1.44  Demodulation         : 0.06
% 3.38/1.44  BG Simplification    : 0.02
% 3.38/1.44  Subsumption          : 0.06
% 3.38/1.44  Abstraction          : 0.01
% 3.38/1.44  MUC search           : 0.00
% 3.38/1.44  Cooper               : 0.00
% 3.38/1.44  Total                : 0.72
% 3.38/1.44  Index Insertion      : 0.00
% 3.38/1.44  Index Deletion       : 0.00
% 3.38/1.44  Index Matching       : 0.00
% 3.38/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
