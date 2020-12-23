%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:02 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 166 expanded)
%              Number of leaves         :   32 (  81 expanded)
%              Depth                    :    9
%              Number of atoms          :  236 (1258 expanded)
%              Number of equality atoms :    5 (  62 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4

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

tff(f_192,negated_conjecture,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> ? [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                    & v3_pre_topc(D,A)
                    & r1_tarski(D,C)
                    & r2_hidden(B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_connsp_2)).

tff(f_142,axiom,(
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

tff(f_95,axiom,(
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
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_38,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_24,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_34,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_68,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_34])).

tff(c_32,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_26,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_50,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_48,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_30,plain,(
    v3_pre_topc('#skF_6','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_28,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_70,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28])).

tff(c_129,plain,(
    ! [C_354,A_355,B_356,D_357] :
      ( m1_connsp_2(C_354,A_355,B_356)
      | ~ r2_hidden(B_356,D_357)
      | ~ r1_tarski(D_357,C_354)
      | ~ v3_pre_topc(D_357,A_355)
      | ~ m1_subset_1(D_357,k1_zfmisc_1(u1_struct_0(A_355)))
      | ~ m1_subset_1(C_354,k1_zfmisc_1(u1_struct_0(A_355)))
      | ~ m1_subset_1(B_356,u1_struct_0(A_355))
      | ~ l1_pre_topc(A_355)
      | ~ v2_pre_topc(A_355)
      | v2_struct_0(A_355) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_136,plain,(
    ! [C_358,A_359] :
      ( m1_connsp_2(C_358,A_359,'#skF_8')
      | ~ r1_tarski('#skF_6',C_358)
      | ~ v3_pre_topc('#skF_6',A_359)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_359)))
      | ~ m1_subset_1(C_358,k1_zfmisc_1(u1_struct_0(A_359)))
      | ~ m1_subset_1('#skF_8',u1_struct_0(A_359))
      | ~ l1_pre_topc(A_359)
      | ~ v2_pre_topc(A_359)
      | v2_struct_0(A_359) ) ),
    inference(resolution,[status(thm)],[c_70,c_129])).

tff(c_138,plain,(
    ! [C_358] :
      ( m1_connsp_2(C_358,'#skF_3','#skF_8')
      | ~ r1_tarski('#skF_6',C_358)
      | ~ v3_pre_topc('#skF_6','#skF_3')
      | ~ m1_subset_1(C_358,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_136])).

tff(c_141,plain,(
    ! [C_358] :
      ( m1_connsp_2(C_358,'#skF_3','#skF_8')
      | ~ r1_tarski('#skF_6',C_358)
      | ~ m1_subset_1(C_358,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_68,c_30,c_138])).

tff(c_150,plain,(
    ! [C_365] :
      ( m1_connsp_2(C_365,'#skF_3','#skF_8')
      | ~ r1_tarski('#skF_6',C_365)
      | ~ m1_subset_1(C_365,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_141])).

tff(c_157,plain,
    ( m1_connsp_2('#skF_6','#skF_3','#skF_8')
    | ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_150])).

tff(c_164,plain,(
    m1_connsp_2('#skF_6','#skF_3','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_157])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_66,plain,
    ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_7')
    | r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_67,plain,
    ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_8')
    | r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_66])).

tff(c_88,plain,(
    r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_60,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_69,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_60])).

tff(c_90,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_69])).

tff(c_56,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_54,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_44,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_188,plain,(
    ! [C_391,B_386,D_390,E_389,G_387,A_388] :
      ( r1_tmap_1(B_386,A_388,C_391,G_387)
      | ~ r1_tmap_1(D_390,A_388,k2_tmap_1(B_386,A_388,C_391,D_390),G_387)
      | ~ m1_connsp_2(E_389,B_386,G_387)
      | ~ r1_tarski(E_389,u1_struct_0(D_390))
      | ~ m1_subset_1(G_387,u1_struct_0(D_390))
      | ~ m1_subset_1(G_387,u1_struct_0(B_386))
      | ~ m1_subset_1(E_389,k1_zfmisc_1(u1_struct_0(B_386)))
      | ~ m1_pre_topc(D_390,B_386)
      | v2_struct_0(D_390)
      | ~ m1_subset_1(C_391,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_386),u1_struct_0(A_388))))
      | ~ v1_funct_2(C_391,u1_struct_0(B_386),u1_struct_0(A_388))
      | ~ v1_funct_1(C_391)
      | ~ l1_pre_topc(B_386)
      | ~ v2_pre_topc(B_386)
      | v2_struct_0(B_386)
      | ~ l1_pre_topc(A_388)
      | ~ v2_pre_topc(A_388)
      | v2_struct_0(A_388) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_192,plain,(
    ! [E_389] :
      ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_8')
      | ~ m1_connsp_2(E_389,'#skF_3','#skF_8')
      | ~ r1_tarski(E_389,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(E_389,k1_zfmisc_1(u1_struct_0('#skF_3')))
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
    inference(resolution,[status(thm)],[c_88,c_188])).

tff(c_199,plain,(
    ! [E_389] :
      ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_8')
      | ~ m1_connsp_2(E_389,'#skF_3','#skF_8')
      | ~ r1_tarski(E_389,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(E_389,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_48,c_46,c_44,c_42,c_38,c_68,c_32,c_192])).

tff(c_201,plain,(
    ! [E_392] :
      ( ~ m1_connsp_2(E_392,'#skF_3','#skF_8')
      | ~ r1_tarski(E_392,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(E_392,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_52,c_40,c_90,c_199])).

tff(c_208,plain,
    ( ~ m1_connsp_2('#skF_6','#skF_3','#skF_8')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_36,c_201])).

tff(c_216,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_164,c_208])).

tff(c_217,plain,(
    r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_304,plain,(
    ! [A_424,F_427,D_425,C_426,B_423] :
      ( r1_tmap_1(D_425,A_424,k2_tmap_1(B_423,A_424,C_426,D_425),F_427)
      | ~ r1_tmap_1(B_423,A_424,C_426,F_427)
      | ~ m1_subset_1(F_427,u1_struct_0(D_425))
      | ~ m1_subset_1(F_427,u1_struct_0(B_423))
      | ~ m1_pre_topc(D_425,B_423)
      | v2_struct_0(D_425)
      | ~ m1_subset_1(C_426,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_423),u1_struct_0(A_424))))
      | ~ v1_funct_2(C_426,u1_struct_0(B_423),u1_struct_0(A_424))
      | ~ v1_funct_1(C_426)
      | ~ l1_pre_topc(B_423)
      | ~ v2_pre_topc(B_423)
      | v2_struct_0(B_423)
      | ~ l1_pre_topc(A_424)
      | ~ v2_pre_topc(A_424)
      | v2_struct_0(A_424) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_306,plain,(
    ! [D_425,F_427] :
      ( r1_tmap_1(D_425,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4',D_425),F_427)
      | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4',F_427)
      | ~ m1_subset_1(F_427,u1_struct_0(D_425))
      | ~ m1_subset_1(F_427,u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_425,'#skF_3')
      | v2_struct_0(D_425)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_304])).

tff(c_309,plain,(
    ! [D_425,F_427] :
      ( r1_tmap_1(D_425,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4',D_425),F_427)
      | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4',F_427)
      | ~ m1_subset_1(F_427,u1_struct_0(D_425))
      | ~ m1_subset_1(F_427,u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_425,'#skF_3')
      | v2_struct_0(D_425)
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_48,c_46,c_44,c_306])).

tff(c_311,plain,(
    ! [D_428,F_429] :
      ( r1_tmap_1(D_428,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4',D_428),F_429)
      | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4',F_429)
      | ~ m1_subset_1(F_429,u1_struct_0(D_428))
      | ~ m1_subset_1(F_429,u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_428,'#skF_3')
      | v2_struct_0(D_428) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_52,c_309])).

tff(c_218,plain,(
    ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_314,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_311,c_218])).

tff(c_317,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_68,c_32,c_217,c_314])).

tff(c_319,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_317])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:29:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.90/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.48  
% 2.90/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.48  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4
% 2.90/1.48  
% 2.90/1.48  %Foreground sorts:
% 2.90/1.48  
% 2.90/1.48  
% 2.90/1.48  %Background operators:
% 2.90/1.48  
% 2.90/1.48  
% 2.90/1.48  %Foreground operators:
% 2.90/1.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.90/1.48  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 2.90/1.48  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.90/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.90/1.48  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.90/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.90/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.90/1.48  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 2.90/1.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.90/1.48  tff('#skF_7', type, '#skF_7': $i).
% 2.90/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.90/1.48  tff('#skF_5', type, '#skF_5': $i).
% 2.90/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.90/1.48  tff('#skF_6', type, '#skF_6': $i).
% 2.90/1.48  tff('#skF_2', type, '#skF_2': $i).
% 2.90/1.48  tff('#skF_3', type, '#skF_3': $i).
% 2.90/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.90/1.48  tff('#skF_8', type, '#skF_8': $i).
% 2.90/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.90/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.90/1.48  tff('#skF_4', type, '#skF_4': $i).
% 2.90/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.90/1.48  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.90/1.48  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.90/1.48  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 2.90/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.90/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.90/1.48  
% 3.15/1.50  tff(f_192, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((v3_pre_topc(E, B) & r2_hidden(F, E)) & r1_tarski(E, u1_struct_0(D))) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_tmap_1)).
% 3.15/1.50  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.15/1.50  tff(f_55, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_connsp_2)).
% 3.15/1.50  tff(f_142, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tmap_1)).
% 3.15/1.50  tff(f_95, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tmap_1)).
% 3.15/1.50  tff(c_40, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_192])).
% 3.15/1.50  tff(c_38, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_192])).
% 3.15/1.50  tff(c_24, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_192])).
% 3.15/1.50  tff(c_34, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_192])).
% 3.15/1.50  tff(c_68, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_34])).
% 3.15/1.50  tff(c_32, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_192])).
% 3.15/1.50  tff(c_26, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_192])).
% 3.15/1.50  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.15/1.50  tff(c_36, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_192])).
% 3.15/1.50  tff(c_52, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_192])).
% 3.15/1.50  tff(c_50, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_192])).
% 3.15/1.50  tff(c_48, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_192])).
% 3.15/1.50  tff(c_30, plain, (v3_pre_topc('#skF_6', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_192])).
% 3.15/1.50  tff(c_28, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_192])).
% 3.15/1.50  tff(c_70, plain, (r2_hidden('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28])).
% 3.15/1.50  tff(c_129, plain, (![C_354, A_355, B_356, D_357]: (m1_connsp_2(C_354, A_355, B_356) | ~r2_hidden(B_356, D_357) | ~r1_tarski(D_357, C_354) | ~v3_pre_topc(D_357, A_355) | ~m1_subset_1(D_357, k1_zfmisc_1(u1_struct_0(A_355))) | ~m1_subset_1(C_354, k1_zfmisc_1(u1_struct_0(A_355))) | ~m1_subset_1(B_356, u1_struct_0(A_355)) | ~l1_pre_topc(A_355) | ~v2_pre_topc(A_355) | v2_struct_0(A_355))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.15/1.50  tff(c_136, plain, (![C_358, A_359]: (m1_connsp_2(C_358, A_359, '#skF_8') | ~r1_tarski('#skF_6', C_358) | ~v3_pre_topc('#skF_6', A_359) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_359))) | ~m1_subset_1(C_358, k1_zfmisc_1(u1_struct_0(A_359))) | ~m1_subset_1('#skF_8', u1_struct_0(A_359)) | ~l1_pre_topc(A_359) | ~v2_pre_topc(A_359) | v2_struct_0(A_359))), inference(resolution, [status(thm)], [c_70, c_129])).
% 3.15/1.50  tff(c_138, plain, (![C_358]: (m1_connsp_2(C_358, '#skF_3', '#skF_8') | ~r1_tarski('#skF_6', C_358) | ~v3_pre_topc('#skF_6', '#skF_3') | ~m1_subset_1(C_358, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_136])).
% 3.15/1.50  tff(c_141, plain, (![C_358]: (m1_connsp_2(C_358, '#skF_3', '#skF_8') | ~r1_tarski('#skF_6', C_358) | ~m1_subset_1(C_358, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_68, c_30, c_138])).
% 3.15/1.50  tff(c_150, plain, (![C_365]: (m1_connsp_2(C_365, '#skF_3', '#skF_8') | ~r1_tarski('#skF_6', C_365) | ~m1_subset_1(C_365, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_141])).
% 3.15/1.50  tff(c_157, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_8') | ~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_36, c_150])).
% 3.15/1.50  tff(c_164, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_157])).
% 3.15/1.50  tff(c_58, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 3.15/1.50  tff(c_66, plain, (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_7') | r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_192])).
% 3.15/1.50  tff(c_67, plain, (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_8') | r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_66])).
% 3.15/1.50  tff(c_88, plain, (r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_8')), inference(splitLeft, [status(thm)], [c_67])).
% 3.15/1.50  tff(c_60, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_192])).
% 3.15/1.50  tff(c_69, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_60])).
% 3.15/1.50  tff(c_90, plain, (~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_69])).
% 3.15/1.50  tff(c_56, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 3.15/1.50  tff(c_54, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 3.15/1.50  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_192])).
% 3.15/1.50  tff(c_44, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_192])).
% 3.15/1.50  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_192])).
% 3.15/1.50  tff(c_188, plain, (![C_391, B_386, D_390, E_389, G_387, A_388]: (r1_tmap_1(B_386, A_388, C_391, G_387) | ~r1_tmap_1(D_390, A_388, k2_tmap_1(B_386, A_388, C_391, D_390), G_387) | ~m1_connsp_2(E_389, B_386, G_387) | ~r1_tarski(E_389, u1_struct_0(D_390)) | ~m1_subset_1(G_387, u1_struct_0(D_390)) | ~m1_subset_1(G_387, u1_struct_0(B_386)) | ~m1_subset_1(E_389, k1_zfmisc_1(u1_struct_0(B_386))) | ~m1_pre_topc(D_390, B_386) | v2_struct_0(D_390) | ~m1_subset_1(C_391, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_386), u1_struct_0(A_388)))) | ~v1_funct_2(C_391, u1_struct_0(B_386), u1_struct_0(A_388)) | ~v1_funct_1(C_391) | ~l1_pre_topc(B_386) | ~v2_pre_topc(B_386) | v2_struct_0(B_386) | ~l1_pre_topc(A_388) | ~v2_pre_topc(A_388) | v2_struct_0(A_388))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.15/1.50  tff(c_192, plain, (![E_389]: (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_8') | ~m1_connsp_2(E_389, '#skF_3', '#skF_8') | ~r1_tarski(E_389, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1(E_389, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_88, c_188])).
% 3.15/1.50  tff(c_199, plain, (![E_389]: (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_8') | ~m1_connsp_2(E_389, '#skF_3', '#skF_8') | ~r1_tarski(E_389, u1_struct_0('#skF_5')) | ~m1_subset_1(E_389, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_5') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_48, c_46, c_44, c_42, c_38, c_68, c_32, c_192])).
% 3.15/1.50  tff(c_201, plain, (![E_392]: (~m1_connsp_2(E_392, '#skF_3', '#skF_8') | ~r1_tarski(E_392, u1_struct_0('#skF_5')) | ~m1_subset_1(E_392, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_52, c_40, c_90, c_199])).
% 3.15/1.50  tff(c_208, plain, (~m1_connsp_2('#skF_6', '#skF_3', '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_36, c_201])).
% 3.15/1.50  tff(c_216, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_164, c_208])).
% 3.15/1.50  tff(c_217, plain, (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_67])).
% 3.15/1.50  tff(c_304, plain, (![A_424, F_427, D_425, C_426, B_423]: (r1_tmap_1(D_425, A_424, k2_tmap_1(B_423, A_424, C_426, D_425), F_427) | ~r1_tmap_1(B_423, A_424, C_426, F_427) | ~m1_subset_1(F_427, u1_struct_0(D_425)) | ~m1_subset_1(F_427, u1_struct_0(B_423)) | ~m1_pre_topc(D_425, B_423) | v2_struct_0(D_425) | ~m1_subset_1(C_426, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_423), u1_struct_0(A_424)))) | ~v1_funct_2(C_426, u1_struct_0(B_423), u1_struct_0(A_424)) | ~v1_funct_1(C_426) | ~l1_pre_topc(B_423) | ~v2_pre_topc(B_423) | v2_struct_0(B_423) | ~l1_pre_topc(A_424) | ~v2_pre_topc(A_424) | v2_struct_0(A_424))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.15/1.50  tff(c_306, plain, (![D_425, F_427]: (r1_tmap_1(D_425, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_425), F_427) | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', F_427) | ~m1_subset_1(F_427, u1_struct_0(D_425)) | ~m1_subset_1(F_427, u1_struct_0('#skF_3')) | ~m1_pre_topc(D_425, '#skF_3') | v2_struct_0(D_425) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_304])).
% 3.15/1.50  tff(c_309, plain, (![D_425, F_427]: (r1_tmap_1(D_425, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_425), F_427) | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', F_427) | ~m1_subset_1(F_427, u1_struct_0(D_425)) | ~m1_subset_1(F_427, u1_struct_0('#skF_3')) | ~m1_pre_topc(D_425, '#skF_3') | v2_struct_0(D_425) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_48, c_46, c_44, c_306])).
% 3.15/1.50  tff(c_311, plain, (![D_428, F_429]: (r1_tmap_1(D_428, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_428), F_429) | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', F_429) | ~m1_subset_1(F_429, u1_struct_0(D_428)) | ~m1_subset_1(F_429, u1_struct_0('#skF_3')) | ~m1_pre_topc(D_428, '#skF_3') | v2_struct_0(D_428))), inference(negUnitSimplification, [status(thm)], [c_58, c_52, c_309])).
% 3.15/1.50  tff(c_218, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_67])).
% 3.15/1.50  tff(c_314, plain, (~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_311, c_218])).
% 3.15/1.50  tff(c_317, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_68, c_32, c_217, c_314])).
% 3.15/1.50  tff(c_319, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_317])).
% 3.15/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.50  
% 3.15/1.50  Inference rules
% 3.15/1.50  ----------------------
% 3.15/1.50  #Ref     : 0
% 3.15/1.50  #Sup     : 42
% 3.15/1.50  #Fact    : 0
% 3.15/1.50  #Define  : 0
% 3.15/1.50  #Split   : 2
% 3.15/1.50  #Chain   : 0
% 3.15/1.50  #Close   : 0
% 3.15/1.50  
% 3.15/1.50  Ordering : KBO
% 3.15/1.50  
% 3.15/1.50  Simplification rules
% 3.15/1.50  ----------------------
% 3.15/1.50  #Subsume      : 2
% 3.15/1.50  #Demod        : 75
% 3.15/1.50  #Tautology    : 7
% 3.15/1.50  #SimpNegUnit  : 18
% 3.15/1.50  #BackRed      : 0
% 3.15/1.50  
% 3.15/1.50  #Partial instantiations: 0
% 3.15/1.50  #Strategies tried      : 1
% 3.15/1.50  
% 3.15/1.50  Timing (in seconds)
% 3.15/1.50  ----------------------
% 3.15/1.50  Preprocessing        : 0.39
% 3.15/1.50  Parsing              : 0.20
% 3.15/1.50  CNF conversion       : 0.06
% 3.15/1.50  Main loop            : 0.30
% 3.15/1.50  Inferencing          : 0.11
% 3.15/1.50  Reduction            : 0.09
% 3.15/1.50  Demodulation         : 0.06
% 3.15/1.50  BG Simplification    : 0.02
% 3.15/1.50  Subsumption          : 0.06
% 3.15/1.50  Abstraction          : 0.01
% 3.15/1.50  MUC search           : 0.00
% 3.15/1.50  Cooper               : 0.00
% 3.15/1.50  Total                : 0.73
% 3.15/1.50  Index Insertion      : 0.00
% 3.15/1.50  Index Deletion       : 0.00
% 3.15/1.50  Index Matching       : 0.00
% 3.15/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
