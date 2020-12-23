%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:03 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 204 expanded)
%              Number of leaves         :   34 (  96 expanded)
%              Depth                    :   13
%              Number of atoms          :  286 (1577 expanded)
%              Number of equality atoms :    4 (  70 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2

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

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_208,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tmap_1)).

tff(f_71,axiom,(
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

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_158,axiom,(
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

tff(f_111,axiom,(
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

tff(c_40,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_38,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_34,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_24,plain,(
    '#skF_9' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_32,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_69,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_32])).

tff(c_28,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_50,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_48,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_30,plain,(
    v3_pre_topc('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_36,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_102,plain,(
    ! [A_356,B_357,C_358] :
      ( r1_tarski('#skF_1'(A_356,B_357,C_358),B_357)
      | ~ r2_hidden(C_358,B_357)
      | ~ m1_subset_1(C_358,u1_struct_0(A_356))
      | ~ v3_pre_topc(B_357,A_356)
      | ~ m1_subset_1(B_357,k1_zfmisc_1(u1_struct_0(A_356)))
      | ~ l1_pre_topc(A_356)
      | ~ v2_pre_topc(A_356)
      | v2_struct_0(A_356) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_104,plain,(
    ! [C_358] :
      ( r1_tarski('#skF_1'('#skF_4','#skF_7',C_358),'#skF_7')
      | ~ r2_hidden(C_358,'#skF_7')
      | ~ m1_subset_1(C_358,u1_struct_0('#skF_4'))
      | ~ v3_pre_topc('#skF_7','#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_102])).

tff(c_107,plain,(
    ! [C_358] :
      ( r1_tarski('#skF_1'('#skF_4','#skF_7',C_358),'#skF_7')
      | ~ r2_hidden(C_358,'#skF_7')
      | ~ m1_subset_1(C_358,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_30,c_104])).

tff(c_108,plain,(
    ! [C_358] :
      ( r1_tarski('#skF_1'('#skF_4','#skF_7',C_358),'#skF_7')
      | ~ r2_hidden(C_358,'#skF_7')
      | ~ m1_subset_1(C_358,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_107])).

tff(c_119,plain,(
    ! [A_365,B_366,C_367] :
      ( m1_connsp_2('#skF_1'(A_365,B_366,C_367),A_365,C_367)
      | ~ r2_hidden(C_367,B_366)
      | ~ m1_subset_1(C_367,u1_struct_0(A_365))
      | ~ v3_pre_topc(B_366,A_365)
      | ~ m1_subset_1(B_366,k1_zfmisc_1(u1_struct_0(A_365)))
      | ~ l1_pre_topc(A_365)
      | ~ v2_pre_topc(A_365)
      | v2_struct_0(A_365) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_121,plain,(
    ! [C_367] :
      ( m1_connsp_2('#skF_1'('#skF_4','#skF_7',C_367),'#skF_4',C_367)
      | ~ r2_hidden(C_367,'#skF_7')
      | ~ m1_subset_1(C_367,u1_struct_0('#skF_4'))
      | ~ v3_pre_topc('#skF_7','#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_119])).

tff(c_124,plain,(
    ! [C_367] :
      ( m1_connsp_2('#skF_1'('#skF_4','#skF_7',C_367),'#skF_4',C_367)
      | ~ r2_hidden(C_367,'#skF_7')
      | ~ m1_subset_1(C_367,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_30,c_121])).

tff(c_125,plain,(
    ! [C_367] :
      ( m1_connsp_2('#skF_1'('#skF_4','#skF_7',C_367),'#skF_4',C_367)
      | ~ r2_hidden(C_367,'#skF_7')
      | ~ m1_subset_1(C_367,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_124])).

tff(c_26,plain,(
    r1_tarski('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_74,plain,(
    ! [A_343,C_344,B_345] :
      ( r1_tarski(A_343,C_344)
      | ~ r1_tarski(B_345,C_344)
      | ~ r1_tarski(A_343,B_345) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_77,plain,(
    ! [A_343] :
      ( r1_tarski(A_343,u1_struct_0('#skF_6'))
      | ~ r1_tarski(A_343,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_26,c_74])).

tff(c_126,plain,(
    ! [C_368] :
      ( m1_connsp_2('#skF_1'('#skF_4','#skF_7',C_368),'#skF_4',C_368)
      | ~ r2_hidden(C_368,'#skF_7')
      | ~ m1_subset_1(C_368,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_124])).

tff(c_4,plain,(
    ! [C_7,A_4,B_5] :
      ( m1_subset_1(C_7,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ m1_connsp_2(C_7,A_4,B_5)
      | ~ m1_subset_1(B_5,u1_struct_0(A_4))
      | ~ l1_pre_topc(A_4)
      | ~ v2_pre_topc(A_4)
      | v2_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_131,plain,(
    ! [C_368] :
      ( m1_subset_1('#skF_1'('#skF_4','#skF_7',C_368),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r2_hidden(C_368,'#skF_7')
      | ~ m1_subset_1(C_368,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_126,c_4])).

tff(c_138,plain,(
    ! [C_368] :
      ( m1_subset_1('#skF_1'('#skF_4','#skF_7',C_368),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | ~ r2_hidden(C_368,'#skF_7')
      | ~ m1_subset_1(C_368,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_131])).

tff(c_139,plain,(
    ! [C_368] :
      ( m1_subset_1('#skF_1'('#skF_4','#skF_7',C_368),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(C_368,'#skF_7')
      | ~ m1_subset_1(C_368,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_138])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_66,plain,
    ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
    | r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_67,plain,
    ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
    | r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_66])).

tff(c_90,plain,(
    r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_60,plain,
    ( ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_9')
    | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_68,plain,
    ( ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_60])).

tff(c_92,plain,(
    ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_68])).

tff(c_56,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_54,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_46,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_44,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_265,plain,(
    ! [C_406,D_409,B_410,G_408,A_407,E_411] :
      ( r1_tmap_1(B_410,A_407,C_406,G_408)
      | ~ r1_tmap_1(D_409,A_407,k2_tmap_1(B_410,A_407,C_406,D_409),G_408)
      | ~ m1_connsp_2(E_411,B_410,G_408)
      | ~ r1_tarski(E_411,u1_struct_0(D_409))
      | ~ m1_subset_1(G_408,u1_struct_0(D_409))
      | ~ m1_subset_1(G_408,u1_struct_0(B_410))
      | ~ m1_subset_1(E_411,k1_zfmisc_1(u1_struct_0(B_410)))
      | ~ m1_pre_topc(D_409,B_410)
      | v2_struct_0(D_409)
      | ~ m1_subset_1(C_406,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_410),u1_struct_0(A_407))))
      | ~ v1_funct_2(C_406,u1_struct_0(B_410),u1_struct_0(A_407))
      | ~ v1_funct_1(C_406)
      | ~ l1_pre_topc(B_410)
      | ~ v2_pre_topc(B_410)
      | v2_struct_0(B_410)
      | ~ l1_pre_topc(A_407)
      | ~ v2_pre_topc(A_407)
      | v2_struct_0(A_407) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_269,plain,(
    ! [E_411] :
      ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
      | ~ m1_connsp_2(E_411,'#skF_4','#skF_8')
      | ~ r1_tarski(E_411,u1_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_411,k1_zfmisc_1(u1_struct_0('#skF_4')))
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
    inference(resolution,[status(thm)],[c_90,c_265])).

tff(c_276,plain,(
    ! [E_411] :
      ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
      | ~ m1_connsp_2(E_411,'#skF_4','#skF_8')
      | ~ r1_tarski(E_411,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(E_411,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_48,c_46,c_44,c_42,c_38,c_34,c_69,c_269])).

tff(c_279,plain,(
    ! [E_412] :
      ( ~ m1_connsp_2(E_412,'#skF_4','#skF_8')
      | ~ r1_tarski(E_412,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(E_412,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_52,c_40,c_92,c_276])).

tff(c_311,plain,(
    ! [C_415] :
      ( ~ m1_connsp_2('#skF_1'('#skF_4','#skF_7',C_415),'#skF_4','#skF_8')
      | ~ r1_tarski('#skF_1'('#skF_4','#skF_7',C_415),u1_struct_0('#skF_6'))
      | ~ r2_hidden(C_415,'#skF_7')
      | ~ m1_subset_1(C_415,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_139,c_279])).

tff(c_316,plain,(
    ! [C_416] :
      ( ~ m1_connsp_2('#skF_1'('#skF_4','#skF_7',C_416),'#skF_4','#skF_8')
      | ~ r2_hidden(C_416,'#skF_7')
      | ~ m1_subset_1(C_416,u1_struct_0('#skF_4'))
      | ~ r1_tarski('#skF_1'('#skF_4','#skF_7',C_416),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_77,c_311])).

tff(c_320,plain,
    ( ~ r1_tarski('#skF_1'('#skF_4','#skF_7','#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_8','#skF_7')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_125,c_316])).

tff(c_323,plain,(
    ~ r1_tarski('#skF_1'('#skF_4','#skF_7','#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_320])).

tff(c_326,plain,
    ( ~ r2_hidden('#skF_8','#skF_7')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_108,c_323])).

tff(c_330,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_326])).

tff(c_331,plain,(
    r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_463,plain,(
    ! [C_454,F_452,B_451,A_450,D_453] :
      ( r1_tmap_1(D_453,A_450,k2_tmap_1(B_451,A_450,C_454,D_453),F_452)
      | ~ r1_tmap_1(B_451,A_450,C_454,F_452)
      | ~ m1_subset_1(F_452,u1_struct_0(D_453))
      | ~ m1_subset_1(F_452,u1_struct_0(B_451))
      | ~ m1_pre_topc(D_453,B_451)
      | v2_struct_0(D_453)
      | ~ m1_subset_1(C_454,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_451),u1_struct_0(A_450))))
      | ~ v1_funct_2(C_454,u1_struct_0(B_451),u1_struct_0(A_450))
      | ~ v1_funct_1(C_454)
      | ~ l1_pre_topc(B_451)
      | ~ v2_pre_topc(B_451)
      | v2_struct_0(B_451)
      | ~ l1_pre_topc(A_450)
      | ~ v2_pre_topc(A_450)
      | v2_struct_0(A_450) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_465,plain,(
    ! [D_453,F_452] :
      ( r1_tmap_1(D_453,'#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5',D_453),F_452)
      | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5',F_452)
      | ~ m1_subset_1(F_452,u1_struct_0(D_453))
      | ~ m1_subset_1(F_452,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_453,'#skF_4')
      | v2_struct_0(D_453)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_42,c_463])).

tff(c_468,plain,(
    ! [D_453,F_452] :
      ( r1_tmap_1(D_453,'#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5',D_453),F_452)
      | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5',F_452)
      | ~ m1_subset_1(F_452,u1_struct_0(D_453))
      | ~ m1_subset_1(F_452,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_453,'#skF_4')
      | v2_struct_0(D_453)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_48,c_46,c_44,c_465])).

tff(c_470,plain,(
    ! [D_455,F_456] :
      ( r1_tmap_1(D_455,'#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5',D_455),F_456)
      | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5',F_456)
      | ~ m1_subset_1(F_456,u1_struct_0(D_455))
      | ~ m1_subset_1(F_456,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_455,'#skF_4')
      | v2_struct_0(D_455) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_52,c_468])).

tff(c_332,plain,(
    ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_473,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_470,c_332])).

tff(c_476,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_69,c_331,c_473])).

tff(c_478,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_476])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n001.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 15:18:45 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.46  
% 3.11/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.46  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2
% 3.26/1.46  
% 3.26/1.46  %Foreground sorts:
% 3.26/1.46  
% 3.26/1.46  
% 3.26/1.46  %Background operators:
% 3.26/1.46  
% 3.26/1.46  
% 3.26/1.46  %Foreground operators:
% 3.26/1.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.26/1.46  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.26/1.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.26/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.26/1.46  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.26/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.26/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.26/1.46  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.26/1.46  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.26/1.46  tff('#skF_7', type, '#skF_7': $i).
% 3.26/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.26/1.46  tff('#skF_5', type, '#skF_5': $i).
% 3.26/1.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.26/1.46  tff('#skF_6', type, '#skF_6': $i).
% 3.26/1.46  tff('#skF_3', type, '#skF_3': $i).
% 3.26/1.46  tff('#skF_9', type, '#skF_9': $i).
% 3.26/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.26/1.46  tff('#skF_8', type, '#skF_8': $i).
% 3.26/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.26/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.26/1.46  tff('#skF_4', type, '#skF_4': $i).
% 3.26/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.26/1.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.26/1.46  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.26/1.46  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.26/1.46  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.26/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.26/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.26/1.46  
% 3.26/1.48  tff(f_208, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((v3_pre_topc(E, B) & r2_hidden(F, E)) & r1_tarski(E, u1_struct_0(D))) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_tmap_1)).
% 3.26/1.48  tff(f_71, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(D, A, C) & r1_tarski(D, B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_connsp_2)).
% 3.26/1.48  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.26/1.48  tff(f_45, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 3.26/1.48  tff(f_158, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tmap_1)).
% 3.26/1.48  tff(f_111, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tmap_1)).
% 3.26/1.48  tff(c_40, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.26/1.48  tff(c_38, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.26/1.48  tff(c_34, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.26/1.48  tff(c_24, plain, ('#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.26/1.48  tff(c_32, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.26/1.48  tff(c_69, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_32])).
% 3.26/1.48  tff(c_28, plain, (r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.26/1.48  tff(c_52, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.26/1.48  tff(c_50, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.26/1.48  tff(c_48, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.26/1.48  tff(c_30, plain, (v3_pre_topc('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.26/1.48  tff(c_36, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.26/1.48  tff(c_102, plain, (![A_356, B_357, C_358]: (r1_tarski('#skF_1'(A_356, B_357, C_358), B_357) | ~r2_hidden(C_358, B_357) | ~m1_subset_1(C_358, u1_struct_0(A_356)) | ~v3_pre_topc(B_357, A_356) | ~m1_subset_1(B_357, k1_zfmisc_1(u1_struct_0(A_356))) | ~l1_pre_topc(A_356) | ~v2_pre_topc(A_356) | v2_struct_0(A_356))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.26/1.48  tff(c_104, plain, (![C_358]: (r1_tarski('#skF_1'('#skF_4', '#skF_7', C_358), '#skF_7') | ~r2_hidden(C_358, '#skF_7') | ~m1_subset_1(C_358, u1_struct_0('#skF_4')) | ~v3_pre_topc('#skF_7', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_36, c_102])).
% 3.26/1.48  tff(c_107, plain, (![C_358]: (r1_tarski('#skF_1'('#skF_4', '#skF_7', C_358), '#skF_7') | ~r2_hidden(C_358, '#skF_7') | ~m1_subset_1(C_358, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_30, c_104])).
% 3.26/1.48  tff(c_108, plain, (![C_358]: (r1_tarski('#skF_1'('#skF_4', '#skF_7', C_358), '#skF_7') | ~r2_hidden(C_358, '#skF_7') | ~m1_subset_1(C_358, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_52, c_107])).
% 3.26/1.48  tff(c_119, plain, (![A_365, B_366, C_367]: (m1_connsp_2('#skF_1'(A_365, B_366, C_367), A_365, C_367) | ~r2_hidden(C_367, B_366) | ~m1_subset_1(C_367, u1_struct_0(A_365)) | ~v3_pre_topc(B_366, A_365) | ~m1_subset_1(B_366, k1_zfmisc_1(u1_struct_0(A_365))) | ~l1_pre_topc(A_365) | ~v2_pre_topc(A_365) | v2_struct_0(A_365))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.26/1.48  tff(c_121, plain, (![C_367]: (m1_connsp_2('#skF_1'('#skF_4', '#skF_7', C_367), '#skF_4', C_367) | ~r2_hidden(C_367, '#skF_7') | ~m1_subset_1(C_367, u1_struct_0('#skF_4')) | ~v3_pre_topc('#skF_7', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_36, c_119])).
% 3.26/1.48  tff(c_124, plain, (![C_367]: (m1_connsp_2('#skF_1'('#skF_4', '#skF_7', C_367), '#skF_4', C_367) | ~r2_hidden(C_367, '#skF_7') | ~m1_subset_1(C_367, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_30, c_121])).
% 3.26/1.48  tff(c_125, plain, (![C_367]: (m1_connsp_2('#skF_1'('#skF_4', '#skF_7', C_367), '#skF_4', C_367) | ~r2_hidden(C_367, '#skF_7') | ~m1_subset_1(C_367, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_52, c_124])).
% 3.26/1.48  tff(c_26, plain, (r1_tarski('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.26/1.48  tff(c_74, plain, (![A_343, C_344, B_345]: (r1_tarski(A_343, C_344) | ~r1_tarski(B_345, C_344) | ~r1_tarski(A_343, B_345))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.26/1.48  tff(c_77, plain, (![A_343]: (r1_tarski(A_343, u1_struct_0('#skF_6')) | ~r1_tarski(A_343, '#skF_7'))), inference(resolution, [status(thm)], [c_26, c_74])).
% 3.26/1.48  tff(c_126, plain, (![C_368]: (m1_connsp_2('#skF_1'('#skF_4', '#skF_7', C_368), '#skF_4', C_368) | ~r2_hidden(C_368, '#skF_7') | ~m1_subset_1(C_368, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_52, c_124])).
% 3.26/1.48  tff(c_4, plain, (![C_7, A_4, B_5]: (m1_subset_1(C_7, k1_zfmisc_1(u1_struct_0(A_4))) | ~m1_connsp_2(C_7, A_4, B_5) | ~m1_subset_1(B_5, u1_struct_0(A_4)) | ~l1_pre_topc(A_4) | ~v2_pre_topc(A_4) | v2_struct_0(A_4))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.26/1.48  tff(c_131, plain, (![C_368]: (m1_subset_1('#skF_1'('#skF_4', '#skF_7', C_368), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r2_hidden(C_368, '#skF_7') | ~m1_subset_1(C_368, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_126, c_4])).
% 3.26/1.48  tff(c_138, plain, (![C_368]: (m1_subset_1('#skF_1'('#skF_4', '#skF_7', C_368), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | ~r2_hidden(C_368, '#skF_7') | ~m1_subset_1(C_368, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_131])).
% 3.26/1.48  tff(c_139, plain, (![C_368]: (m1_subset_1('#skF_1'('#skF_4', '#skF_7', C_368), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r2_hidden(C_368, '#skF_7') | ~m1_subset_1(C_368, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_52, c_138])).
% 3.26/1.48  tff(c_58, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.26/1.48  tff(c_66, plain, (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.26/1.48  tff(c_67, plain, (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_66])).
% 3.26/1.48  tff(c_90, plain, (r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(splitLeft, [status(thm)], [c_67])).
% 3.26/1.48  tff(c_60, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_9') | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.26/1.48  tff(c_68, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_60])).
% 3.26/1.48  tff(c_92, plain, (~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_68])).
% 3.26/1.48  tff(c_56, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.26/1.48  tff(c_54, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.26/1.48  tff(c_46, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.26/1.48  tff(c_44, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.26/1.48  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_208])).
% 3.26/1.48  tff(c_265, plain, (![C_406, D_409, B_410, G_408, A_407, E_411]: (r1_tmap_1(B_410, A_407, C_406, G_408) | ~r1_tmap_1(D_409, A_407, k2_tmap_1(B_410, A_407, C_406, D_409), G_408) | ~m1_connsp_2(E_411, B_410, G_408) | ~r1_tarski(E_411, u1_struct_0(D_409)) | ~m1_subset_1(G_408, u1_struct_0(D_409)) | ~m1_subset_1(G_408, u1_struct_0(B_410)) | ~m1_subset_1(E_411, k1_zfmisc_1(u1_struct_0(B_410))) | ~m1_pre_topc(D_409, B_410) | v2_struct_0(D_409) | ~m1_subset_1(C_406, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_410), u1_struct_0(A_407)))) | ~v1_funct_2(C_406, u1_struct_0(B_410), u1_struct_0(A_407)) | ~v1_funct_1(C_406) | ~l1_pre_topc(B_410) | ~v2_pre_topc(B_410) | v2_struct_0(B_410) | ~l1_pre_topc(A_407) | ~v2_pre_topc(A_407) | v2_struct_0(A_407))), inference(cnfTransformation, [status(thm)], [f_158])).
% 3.26/1.48  tff(c_269, plain, (![E_411]: (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | ~m1_connsp_2(E_411, '#skF_4', '#skF_8') | ~r1_tarski(E_411, u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1(E_411, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_90, c_265])).
% 3.26/1.48  tff(c_276, plain, (![E_411]: (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | ~m1_connsp_2(E_411, '#skF_4', '#skF_8') | ~r1_tarski(E_411, u1_struct_0('#skF_6')) | ~m1_subset_1(E_411, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_6') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_48, c_46, c_44, c_42, c_38, c_34, c_69, c_269])).
% 3.26/1.48  tff(c_279, plain, (![E_412]: (~m1_connsp_2(E_412, '#skF_4', '#skF_8') | ~r1_tarski(E_412, u1_struct_0('#skF_6')) | ~m1_subset_1(E_412, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_52, c_40, c_92, c_276])).
% 3.26/1.48  tff(c_311, plain, (![C_415]: (~m1_connsp_2('#skF_1'('#skF_4', '#skF_7', C_415), '#skF_4', '#skF_8') | ~r1_tarski('#skF_1'('#skF_4', '#skF_7', C_415), u1_struct_0('#skF_6')) | ~r2_hidden(C_415, '#skF_7') | ~m1_subset_1(C_415, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_139, c_279])).
% 3.26/1.48  tff(c_316, plain, (![C_416]: (~m1_connsp_2('#skF_1'('#skF_4', '#skF_7', C_416), '#skF_4', '#skF_8') | ~r2_hidden(C_416, '#skF_7') | ~m1_subset_1(C_416, u1_struct_0('#skF_4')) | ~r1_tarski('#skF_1'('#skF_4', '#skF_7', C_416), '#skF_7'))), inference(resolution, [status(thm)], [c_77, c_311])).
% 3.26/1.48  tff(c_320, plain, (~r1_tarski('#skF_1'('#skF_4', '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden('#skF_8', '#skF_7') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_125, c_316])).
% 3.26/1.48  tff(c_323, plain, (~r1_tarski('#skF_1'('#skF_4', '#skF_7', '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_320])).
% 3.26/1.48  tff(c_326, plain, (~r2_hidden('#skF_8', '#skF_7') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_108, c_323])).
% 3.26/1.48  tff(c_330, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_326])).
% 3.26/1.48  tff(c_331, plain, (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_67])).
% 3.26/1.48  tff(c_463, plain, (![C_454, F_452, B_451, A_450, D_453]: (r1_tmap_1(D_453, A_450, k2_tmap_1(B_451, A_450, C_454, D_453), F_452) | ~r1_tmap_1(B_451, A_450, C_454, F_452) | ~m1_subset_1(F_452, u1_struct_0(D_453)) | ~m1_subset_1(F_452, u1_struct_0(B_451)) | ~m1_pre_topc(D_453, B_451) | v2_struct_0(D_453) | ~m1_subset_1(C_454, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_451), u1_struct_0(A_450)))) | ~v1_funct_2(C_454, u1_struct_0(B_451), u1_struct_0(A_450)) | ~v1_funct_1(C_454) | ~l1_pre_topc(B_451) | ~v2_pre_topc(B_451) | v2_struct_0(B_451) | ~l1_pre_topc(A_450) | ~v2_pre_topc(A_450) | v2_struct_0(A_450))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.26/1.48  tff(c_465, plain, (![D_453, F_452]: (r1_tmap_1(D_453, '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_453), F_452) | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', F_452) | ~m1_subset_1(F_452, u1_struct_0(D_453)) | ~m1_subset_1(F_452, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_453, '#skF_4') | v2_struct_0(D_453) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_42, c_463])).
% 3.26/1.48  tff(c_468, plain, (![D_453, F_452]: (r1_tmap_1(D_453, '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_453), F_452) | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', F_452) | ~m1_subset_1(F_452, u1_struct_0(D_453)) | ~m1_subset_1(F_452, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_453, '#skF_4') | v2_struct_0(D_453) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_48, c_46, c_44, c_465])).
% 3.26/1.48  tff(c_470, plain, (![D_455, F_456]: (r1_tmap_1(D_455, '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_455), F_456) | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', F_456) | ~m1_subset_1(F_456, u1_struct_0(D_455)) | ~m1_subset_1(F_456, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_455, '#skF_4') | v2_struct_0(D_455))), inference(negUnitSimplification, [status(thm)], [c_58, c_52, c_468])).
% 3.26/1.48  tff(c_332, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(splitRight, [status(thm)], [c_67])).
% 3.26/1.48  tff(c_473, plain, (~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_470, c_332])).
% 3.26/1.48  tff(c_476, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_69, c_331, c_473])).
% 3.26/1.48  tff(c_478, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_476])).
% 3.26/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.48  
% 3.26/1.48  Inference rules
% 3.26/1.48  ----------------------
% 3.26/1.48  #Ref     : 0
% 3.26/1.48  #Sup     : 72
% 3.26/1.48  #Fact    : 0
% 3.26/1.48  #Define  : 0
% 3.26/1.48  #Split   : 6
% 3.26/1.48  #Chain   : 0
% 3.26/1.48  #Close   : 0
% 3.26/1.48  
% 3.26/1.48  Ordering : KBO
% 3.26/1.48  
% 3.26/1.48  Simplification rules
% 3.26/1.49  ----------------------
% 3.26/1.49  #Subsume      : 6
% 3.26/1.49  #Demod        : 108
% 3.26/1.49  #Tautology    : 9
% 3.26/1.49  #SimpNegUnit  : 33
% 3.26/1.49  #BackRed      : 0
% 3.26/1.49  
% 3.26/1.49  #Partial instantiations: 0
% 3.26/1.49  #Strategies tried      : 1
% 3.26/1.49  
% 3.26/1.49  Timing (in seconds)
% 3.26/1.49  ----------------------
% 3.26/1.49  Preprocessing        : 0.38
% 3.26/1.49  Parsing              : 0.19
% 3.26/1.49  CNF conversion       : 0.05
% 3.26/1.49  Main loop            : 0.35
% 3.26/1.49  Inferencing          : 0.13
% 3.26/1.49  Reduction            : 0.11
% 3.26/1.49  Demodulation         : 0.07
% 3.26/1.49  BG Simplification    : 0.02
% 3.26/1.49  Subsumption          : 0.07
% 3.26/1.49  Abstraction          : 0.01
% 3.26/1.49  MUC search           : 0.00
% 3.26/1.49  Cooper               : 0.00
% 3.26/1.49  Total                : 0.77
% 3.26/1.49  Index Insertion      : 0.00
% 3.26/1.49  Index Deletion       : 0.00
% 3.26/1.49  Index Matching       : 0.00
% 3.26/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
