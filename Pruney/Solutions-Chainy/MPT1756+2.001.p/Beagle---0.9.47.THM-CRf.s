%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:01 EST 2020

% Result     : Theorem 7.91s
% Output     : CNFRefutation 7.91s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 236 expanded)
%              Number of leaves         :   36 ( 108 expanded)
%              Depth                    :   19
%              Number of atoms          :  318 (1696 expanded)
%              Number of equality atoms :    4 (  78 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_4 > #skF_1

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

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_209,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tmap_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_69,axiom,(
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

tff(f_159,axiom,(
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

tff(c_52,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_50,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_36,plain,(
    '#skF_9' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_44,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_81,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_44])).

tff(c_38,plain,(
    r1_tarski('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_68,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_66,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_56,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_62,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_60,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_46,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_48,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_42,plain,(
    v3_pre_topc('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_232,plain,(
    ! [B_327,A_328,C_329] :
      ( r1_tarski(B_327,k1_tops_1(A_328,C_329))
      | ~ r1_tarski(B_327,C_329)
      | ~ v3_pre_topc(B_327,A_328)
      | ~ m1_subset_1(C_329,k1_zfmisc_1(u1_struct_0(A_328)))
      | ~ m1_subset_1(B_327,k1_zfmisc_1(u1_struct_0(A_328)))
      | ~ l1_pre_topc(A_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_234,plain,(
    ! [B_327] :
      ( r1_tarski(B_327,k1_tops_1('#skF_4','#skF_7'))
      | ~ r1_tarski(B_327,'#skF_7')
      | ~ v3_pre_topc(B_327,'#skF_4')
      | ~ m1_subset_1(B_327,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_232])).

tff(c_238,plain,(
    ! [B_330] :
      ( r1_tarski(B_330,k1_tops_1('#skF_4','#skF_7'))
      | ~ r1_tarski(B_330,'#skF_7')
      | ~ v3_pre_topc(B_330,'#skF_4')
      | ~ m1_subset_1(B_330,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_234])).

tff(c_241,plain,
    ( r1_tarski('#skF_7',k1_tops_1('#skF_4','#skF_7'))
    | ~ r1_tarski('#skF_7','#skF_7')
    | ~ v3_pre_topc('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_238])).

tff(c_244,plain,(
    r1_tarski('#skF_7',k1_tops_1('#skF_4','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_12,c_241])).

tff(c_40,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_107,plain,(
    ! [C_294,B_295,A_296] :
      ( r2_hidden(C_294,B_295)
      | ~ r2_hidden(C_294,A_296)
      | ~ r1_tarski(A_296,B_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_115,plain,(
    ! [B_297] :
      ( r2_hidden('#skF_8',B_297)
      | ~ r1_tarski('#skF_7',B_297) ) ),
    inference(resolution,[status(thm)],[c_40,c_107])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_118,plain,(
    ! [B_2,B_297] :
      ( r2_hidden('#skF_8',B_2)
      | ~ r1_tarski(B_297,B_2)
      | ~ r1_tarski('#skF_7',B_297) ) ),
    inference(resolution,[status(thm)],[c_115,c_2])).

tff(c_252,plain,
    ( r2_hidden('#skF_8',k1_tops_1('#skF_4','#skF_7'))
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_244,c_118])).

tff(c_260,plain,(
    r2_hidden('#skF_8',k1_tops_1('#skF_4','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_252])).

tff(c_427,plain,(
    ! [C_358,A_359,B_360] :
      ( m1_connsp_2(C_358,A_359,B_360)
      | ~ r2_hidden(B_360,k1_tops_1(A_359,C_358))
      | ~ m1_subset_1(C_358,k1_zfmisc_1(u1_struct_0(A_359)))
      | ~ m1_subset_1(B_360,u1_struct_0(A_359))
      | ~ l1_pre_topc(A_359)
      | ~ v2_pre_topc(A_359)
      | v2_struct_0(A_359) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_436,plain,
    ( m1_connsp_2('#skF_7','#skF_4','#skF_8')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_260,c_427])).

tff(c_460,plain,
    ( m1_connsp_2('#skF_7','#skF_4','#skF_8')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_46,c_48,c_436])).

tff(c_461,plain,(
    m1_connsp_2('#skF_7','#skF_4','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_460])).

tff(c_78,plain,
    ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
    | r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_79,plain,
    ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
    | r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_78])).

tff(c_114,plain,(
    r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_72,plain,
    ( ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_9')
    | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_80,plain,
    ( ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_72])).

tff(c_129,plain,(
    ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_80])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_815,plain,(
    ! [C_430,D_429,A_425,E_426,G_428,B_427] :
      ( r1_tmap_1(B_427,A_425,C_430,G_428)
      | ~ r1_tmap_1(D_429,A_425,k2_tmap_1(B_427,A_425,C_430,D_429),G_428)
      | ~ m1_connsp_2(E_426,B_427,G_428)
      | ~ r1_tarski(E_426,u1_struct_0(D_429))
      | ~ m1_subset_1(G_428,u1_struct_0(D_429))
      | ~ m1_subset_1(G_428,u1_struct_0(B_427))
      | ~ m1_subset_1(E_426,k1_zfmisc_1(u1_struct_0(B_427)))
      | ~ m1_pre_topc(D_429,B_427)
      | v2_struct_0(D_429)
      | ~ m1_subset_1(C_430,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_427),u1_struct_0(A_425))))
      | ~ v1_funct_2(C_430,u1_struct_0(B_427),u1_struct_0(A_425))
      | ~ v1_funct_1(C_430)
      | ~ l1_pre_topc(B_427)
      | ~ v2_pre_topc(B_427)
      | v2_struct_0(B_427)
      | ~ l1_pre_topc(A_425)
      | ~ v2_pre_topc(A_425)
      | v2_struct_0(A_425) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_817,plain,(
    ! [E_426] :
      ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
      | ~ m1_connsp_2(E_426,'#skF_4','#skF_8')
      | ~ r1_tarski(E_426,u1_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_426,k1_zfmisc_1(u1_struct_0('#skF_4')))
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
    inference(resolution,[status(thm)],[c_114,c_815])).

tff(c_820,plain,(
    ! [E_426] :
      ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
      | ~ m1_connsp_2(E_426,'#skF_4','#skF_8')
      | ~ r1_tarski(E_426,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(E_426,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_62,c_60,c_58,c_56,c_54,c_50,c_46,c_81,c_817])).

tff(c_822,plain,(
    ! [E_431] :
      ( ~ m1_connsp_2(E_431,'#skF_4','#skF_8')
      | ~ r1_tarski(E_431,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(E_431,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_52,c_129,c_820])).

tff(c_832,plain,
    ( ~ m1_connsp_2('#skF_7','#skF_4','#skF_8')
    | ~ r1_tarski('#skF_7',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_48,c_822])).

tff(c_841,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_461,c_832])).

tff(c_842,plain,(
    r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_961,plain,(
    ! [B_462,A_463,C_464] :
      ( r1_tarski(B_462,k1_tops_1(A_463,C_464))
      | ~ r1_tarski(B_462,C_464)
      | ~ v3_pre_topc(B_462,A_463)
      | ~ m1_subset_1(C_464,k1_zfmisc_1(u1_struct_0(A_463)))
      | ~ m1_subset_1(B_462,k1_zfmisc_1(u1_struct_0(A_463)))
      | ~ l1_pre_topc(A_463) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_963,plain,(
    ! [B_462] :
      ( r1_tarski(B_462,k1_tops_1('#skF_4','#skF_7'))
      | ~ r1_tarski(B_462,'#skF_7')
      | ~ v3_pre_topc(B_462,'#skF_4')
      | ~ m1_subset_1(B_462,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_961])).

tff(c_984,plain,(
    ! [B_468] :
      ( r1_tarski(B_468,k1_tops_1('#skF_4','#skF_7'))
      | ~ r1_tarski(B_468,'#skF_7')
      | ~ v3_pre_topc(B_468,'#skF_4')
      | ~ m1_subset_1(B_468,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_963])).

tff(c_987,plain,
    ( r1_tarski('#skF_7',k1_tops_1('#skF_4','#skF_7'))
    | ~ r1_tarski('#skF_7','#skF_7')
    | ~ v3_pre_topc('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_984])).

tff(c_990,plain,(
    r1_tarski('#skF_7',k1_tops_1('#skF_4','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_12,c_987])).

tff(c_844,plain,(
    ! [B_432] :
      ( r2_hidden('#skF_8',B_432)
      | ~ r1_tarski('#skF_7',B_432) ) ),
    inference(resolution,[status(thm)],[c_40,c_107])).

tff(c_847,plain,(
    ! [B_2,B_432] :
      ( r2_hidden('#skF_8',B_2)
      | ~ r1_tarski(B_432,B_2)
      | ~ r1_tarski('#skF_7',B_432) ) ),
    inference(resolution,[status(thm)],[c_844,c_2])).

tff(c_998,plain,
    ( r2_hidden('#skF_8',k1_tops_1('#skF_4','#skF_7'))
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_990,c_847])).

tff(c_1006,plain,(
    r2_hidden('#skF_8',k1_tops_1('#skF_4','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_998])).

tff(c_16,plain,(
    ! [C_21,A_15,B_19] :
      ( m1_connsp_2(C_21,A_15,B_19)
      | ~ r2_hidden(B_19,k1_tops_1(A_15,C_21))
      | ~ m1_subset_1(C_21,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ m1_subset_1(B_19,u1_struct_0(A_15))
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1009,plain,
    ( m1_connsp_2('#skF_7','#skF_4','#skF_8')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1006,c_16])).

tff(c_1014,plain,
    ( m1_connsp_2('#skF_7','#skF_4','#skF_8')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_46,c_48,c_1009])).

tff(c_1015,plain,(
    m1_connsp_2('#skF_7','#skF_4','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1014])).

tff(c_1518,plain,(
    ! [B_557,A_555,D_559,E_556,C_560,G_558] :
      ( r1_tmap_1(D_559,A_555,k2_tmap_1(B_557,A_555,C_560,D_559),G_558)
      | ~ r1_tmap_1(B_557,A_555,C_560,G_558)
      | ~ m1_connsp_2(E_556,B_557,G_558)
      | ~ r1_tarski(E_556,u1_struct_0(D_559))
      | ~ m1_subset_1(G_558,u1_struct_0(D_559))
      | ~ m1_subset_1(G_558,u1_struct_0(B_557))
      | ~ m1_subset_1(E_556,k1_zfmisc_1(u1_struct_0(B_557)))
      | ~ m1_pre_topc(D_559,B_557)
      | v2_struct_0(D_559)
      | ~ m1_subset_1(C_560,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_557),u1_struct_0(A_555))))
      | ~ v1_funct_2(C_560,u1_struct_0(B_557),u1_struct_0(A_555))
      | ~ v1_funct_1(C_560)
      | ~ l1_pre_topc(B_557)
      | ~ v2_pre_topc(B_557)
      | v2_struct_0(B_557)
      | ~ l1_pre_topc(A_555)
      | ~ v2_pre_topc(A_555)
      | v2_struct_0(A_555) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_1522,plain,(
    ! [D_559,A_555,C_560] :
      ( r1_tmap_1(D_559,A_555,k2_tmap_1('#skF_4',A_555,C_560,D_559),'#skF_8')
      | ~ r1_tmap_1('#skF_4',A_555,C_560,'#skF_8')
      | ~ r1_tarski('#skF_7',u1_struct_0(D_559))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_559))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc(D_559,'#skF_4')
      | v2_struct_0(D_559)
      | ~ m1_subset_1(C_560,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(A_555))))
      | ~ v1_funct_2(C_560,u1_struct_0('#skF_4'),u1_struct_0(A_555))
      | ~ v1_funct_1(C_560)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_555)
      | ~ v2_pre_topc(A_555)
      | v2_struct_0(A_555) ) ),
    inference(resolution,[status(thm)],[c_1015,c_1518])).

tff(c_1529,plain,(
    ! [D_559,A_555,C_560] :
      ( r1_tmap_1(D_559,A_555,k2_tmap_1('#skF_4',A_555,C_560,D_559),'#skF_8')
      | ~ r1_tmap_1('#skF_4',A_555,C_560,'#skF_8')
      | ~ r1_tarski('#skF_7',u1_struct_0(D_559))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_559))
      | ~ m1_pre_topc(D_559,'#skF_4')
      | v2_struct_0(D_559)
      | ~ m1_subset_1(C_560,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(A_555))))
      | ~ v1_funct_2(C_560,u1_struct_0('#skF_4'),u1_struct_0(A_555))
      | ~ v1_funct_1(C_560)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_555)
      | ~ v2_pre_topc(A_555)
      | v2_struct_0(A_555) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_48,c_46,c_1522])).

tff(c_4482,plain,(
    ! [D_999,A_1000,C_1001] :
      ( r1_tmap_1(D_999,A_1000,k2_tmap_1('#skF_4',A_1000,C_1001,D_999),'#skF_8')
      | ~ r1_tmap_1('#skF_4',A_1000,C_1001,'#skF_8')
      | ~ r1_tarski('#skF_7',u1_struct_0(D_999))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_999))
      | ~ m1_pre_topc(D_999,'#skF_4')
      | v2_struct_0(D_999)
      | ~ m1_subset_1(C_1001,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(A_1000))))
      | ~ v1_funct_2(C_1001,u1_struct_0('#skF_4'),u1_struct_0(A_1000))
      | ~ v1_funct_1(C_1001)
      | ~ l1_pre_topc(A_1000)
      | ~ v2_pre_topc(A_1000)
      | v2_struct_0(A_1000) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1529])).

tff(c_4484,plain,(
    ! [D_999] :
      ( r1_tmap_1(D_999,'#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5',D_999),'#skF_8')
      | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
      | ~ r1_tarski('#skF_7',u1_struct_0(D_999))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_999))
      | ~ m1_pre_topc(D_999,'#skF_4')
      | v2_struct_0(D_999)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_54,c_4482])).

tff(c_4487,plain,(
    ! [D_999] :
      ( r1_tmap_1(D_999,'#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5',D_999),'#skF_8')
      | ~ r1_tarski('#skF_7',u1_struct_0(D_999))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_999))
      | ~ m1_pre_topc(D_999,'#skF_4')
      | v2_struct_0(D_999)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_58,c_56,c_842,c_4484])).

tff(c_4489,plain,(
    ! [D_1002] :
      ( r1_tmap_1(D_1002,'#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5',D_1002),'#skF_8')
      | ~ r1_tarski('#skF_7',u1_struct_0(D_1002))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_1002))
      | ~ m1_pre_topc(D_1002,'#skF_4')
      | v2_struct_0(D_1002) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_4487])).

tff(c_849,plain,(
    ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_842,c_80])).

tff(c_4494,plain,
    ( ~ r1_tarski('#skF_7',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4489,c_849])).

tff(c_4501,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_81,c_38,c_4494])).

tff(c_4503,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_4501])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n015.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 13:20:08 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.91/2.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.91/2.74  
% 7.91/2.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.91/2.74  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_4 > #skF_1
% 7.91/2.74  
% 7.91/2.74  %Foreground sorts:
% 7.91/2.74  
% 7.91/2.74  
% 7.91/2.74  %Background operators:
% 7.91/2.74  
% 7.91/2.74  
% 7.91/2.74  %Foreground operators:
% 7.91/2.74  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.91/2.74  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 7.91/2.74  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.91/2.74  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 7.91/2.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.91/2.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.91/2.74  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 7.91/2.74  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.91/2.74  tff('#skF_7', type, '#skF_7': $i).
% 7.91/2.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.91/2.74  tff('#skF_5', type, '#skF_5': $i).
% 7.91/2.74  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.91/2.74  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 7.91/2.74  tff('#skF_6', type, '#skF_6': $i).
% 7.91/2.74  tff('#skF_3', type, '#skF_3': $i).
% 7.91/2.74  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.91/2.74  tff('#skF_9', type, '#skF_9': $i).
% 7.91/2.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.91/2.74  tff('#skF_8', type, '#skF_8': $i).
% 7.91/2.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.91/2.74  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.91/2.74  tff('#skF_4', type, '#skF_4': $i).
% 7.91/2.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.91/2.74  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.91/2.74  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.91/2.74  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 7.91/2.74  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.91/2.74  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.91/2.74  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.91/2.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.91/2.74  
% 7.91/2.76  tff(f_209, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((v3_pre_topc(E, B) & r2_hidden(F, E)) & r1_tarski(E, u1_struct_0(D))) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tmap_1)).
% 7.91/2.76  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.91/2.76  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 7.91/2.76  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.91/2.76  tff(f_69, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 7.91/2.76  tff(f_159, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tmap_1)).
% 7.91/2.76  tff(c_52, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_209])).
% 7.91/2.76  tff(c_50, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_209])).
% 7.91/2.76  tff(c_36, plain, ('#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_209])).
% 7.91/2.76  tff(c_44, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_209])).
% 7.91/2.76  tff(c_81, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_44])).
% 7.91/2.76  tff(c_38, plain, (r1_tarski('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_209])).
% 7.91/2.76  tff(c_70, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_209])).
% 7.91/2.76  tff(c_68, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_209])).
% 7.91/2.76  tff(c_66, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_209])).
% 7.91/2.76  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_209])).
% 7.91/2.76  tff(c_56, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_209])).
% 7.91/2.76  tff(c_64, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_209])).
% 7.91/2.76  tff(c_62, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_209])).
% 7.91/2.76  tff(c_60, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_209])).
% 7.91/2.76  tff(c_46, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_209])).
% 7.91/2.76  tff(c_48, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_209])).
% 7.91/2.76  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.91/2.76  tff(c_42, plain, (v3_pre_topc('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_209])).
% 7.91/2.76  tff(c_232, plain, (![B_327, A_328, C_329]: (r1_tarski(B_327, k1_tops_1(A_328, C_329)) | ~r1_tarski(B_327, C_329) | ~v3_pre_topc(B_327, A_328) | ~m1_subset_1(C_329, k1_zfmisc_1(u1_struct_0(A_328))) | ~m1_subset_1(B_327, k1_zfmisc_1(u1_struct_0(A_328))) | ~l1_pre_topc(A_328))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.91/2.76  tff(c_234, plain, (![B_327]: (r1_tarski(B_327, k1_tops_1('#skF_4', '#skF_7')) | ~r1_tarski(B_327, '#skF_7') | ~v3_pre_topc(B_327, '#skF_4') | ~m1_subset_1(B_327, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_232])).
% 7.91/2.76  tff(c_238, plain, (![B_330]: (r1_tarski(B_330, k1_tops_1('#skF_4', '#skF_7')) | ~r1_tarski(B_330, '#skF_7') | ~v3_pre_topc(B_330, '#skF_4') | ~m1_subset_1(B_330, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_234])).
% 7.91/2.76  tff(c_241, plain, (r1_tarski('#skF_7', k1_tops_1('#skF_4', '#skF_7')) | ~r1_tarski('#skF_7', '#skF_7') | ~v3_pre_topc('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_238])).
% 7.91/2.76  tff(c_244, plain, (r1_tarski('#skF_7', k1_tops_1('#skF_4', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_12, c_241])).
% 7.91/2.76  tff(c_40, plain, (r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_209])).
% 7.91/2.76  tff(c_107, plain, (![C_294, B_295, A_296]: (r2_hidden(C_294, B_295) | ~r2_hidden(C_294, A_296) | ~r1_tarski(A_296, B_295))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.91/2.76  tff(c_115, plain, (![B_297]: (r2_hidden('#skF_8', B_297) | ~r1_tarski('#skF_7', B_297))), inference(resolution, [status(thm)], [c_40, c_107])).
% 7.91/2.76  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.91/2.76  tff(c_118, plain, (![B_2, B_297]: (r2_hidden('#skF_8', B_2) | ~r1_tarski(B_297, B_2) | ~r1_tarski('#skF_7', B_297))), inference(resolution, [status(thm)], [c_115, c_2])).
% 7.91/2.76  tff(c_252, plain, (r2_hidden('#skF_8', k1_tops_1('#skF_4', '#skF_7')) | ~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_244, c_118])).
% 7.91/2.76  tff(c_260, plain, (r2_hidden('#skF_8', k1_tops_1('#skF_4', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_252])).
% 7.91/2.76  tff(c_427, plain, (![C_358, A_359, B_360]: (m1_connsp_2(C_358, A_359, B_360) | ~r2_hidden(B_360, k1_tops_1(A_359, C_358)) | ~m1_subset_1(C_358, k1_zfmisc_1(u1_struct_0(A_359))) | ~m1_subset_1(B_360, u1_struct_0(A_359)) | ~l1_pre_topc(A_359) | ~v2_pre_topc(A_359) | v2_struct_0(A_359))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.91/2.76  tff(c_436, plain, (m1_connsp_2('#skF_7', '#skF_4', '#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_260, c_427])).
% 7.91/2.76  tff(c_460, plain, (m1_connsp_2('#skF_7', '#skF_4', '#skF_8') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_46, c_48, c_436])).
% 7.91/2.76  tff(c_461, plain, (m1_connsp_2('#skF_7', '#skF_4', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_64, c_460])).
% 7.91/2.76  tff(c_78, plain, (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_209])).
% 7.91/2.76  tff(c_79, plain, (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_78])).
% 7.91/2.76  tff(c_114, plain, (r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(splitLeft, [status(thm)], [c_79])).
% 7.91/2.76  tff(c_72, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_9') | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_209])).
% 7.91/2.76  tff(c_80, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_72])).
% 7.91/2.76  tff(c_129, plain, (~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_80])).
% 7.91/2.76  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_209])).
% 7.91/2.76  tff(c_815, plain, (![C_430, D_429, A_425, E_426, G_428, B_427]: (r1_tmap_1(B_427, A_425, C_430, G_428) | ~r1_tmap_1(D_429, A_425, k2_tmap_1(B_427, A_425, C_430, D_429), G_428) | ~m1_connsp_2(E_426, B_427, G_428) | ~r1_tarski(E_426, u1_struct_0(D_429)) | ~m1_subset_1(G_428, u1_struct_0(D_429)) | ~m1_subset_1(G_428, u1_struct_0(B_427)) | ~m1_subset_1(E_426, k1_zfmisc_1(u1_struct_0(B_427))) | ~m1_pre_topc(D_429, B_427) | v2_struct_0(D_429) | ~m1_subset_1(C_430, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_427), u1_struct_0(A_425)))) | ~v1_funct_2(C_430, u1_struct_0(B_427), u1_struct_0(A_425)) | ~v1_funct_1(C_430) | ~l1_pre_topc(B_427) | ~v2_pre_topc(B_427) | v2_struct_0(B_427) | ~l1_pre_topc(A_425) | ~v2_pre_topc(A_425) | v2_struct_0(A_425))), inference(cnfTransformation, [status(thm)], [f_159])).
% 7.91/2.76  tff(c_817, plain, (![E_426]: (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | ~m1_connsp_2(E_426, '#skF_4', '#skF_8') | ~r1_tarski(E_426, u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1(E_426, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_114, c_815])).
% 7.91/2.76  tff(c_820, plain, (![E_426]: (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | ~m1_connsp_2(E_426, '#skF_4', '#skF_8') | ~r1_tarski(E_426, u1_struct_0('#skF_6')) | ~m1_subset_1(E_426, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_6') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_62, c_60, c_58, c_56, c_54, c_50, c_46, c_81, c_817])).
% 7.91/2.76  tff(c_822, plain, (![E_431]: (~m1_connsp_2(E_431, '#skF_4', '#skF_8') | ~r1_tarski(E_431, u1_struct_0('#skF_6')) | ~m1_subset_1(E_431, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_52, c_129, c_820])).
% 7.91/2.76  tff(c_832, plain, (~m1_connsp_2('#skF_7', '#skF_4', '#skF_8') | ~r1_tarski('#skF_7', u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_48, c_822])).
% 7.91/2.76  tff(c_841, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_461, c_832])).
% 7.91/2.76  tff(c_842, plain, (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_79])).
% 7.91/2.76  tff(c_961, plain, (![B_462, A_463, C_464]: (r1_tarski(B_462, k1_tops_1(A_463, C_464)) | ~r1_tarski(B_462, C_464) | ~v3_pre_topc(B_462, A_463) | ~m1_subset_1(C_464, k1_zfmisc_1(u1_struct_0(A_463))) | ~m1_subset_1(B_462, k1_zfmisc_1(u1_struct_0(A_463))) | ~l1_pre_topc(A_463))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.91/2.76  tff(c_963, plain, (![B_462]: (r1_tarski(B_462, k1_tops_1('#skF_4', '#skF_7')) | ~r1_tarski(B_462, '#skF_7') | ~v3_pre_topc(B_462, '#skF_4') | ~m1_subset_1(B_462, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_961])).
% 7.91/2.76  tff(c_984, plain, (![B_468]: (r1_tarski(B_468, k1_tops_1('#skF_4', '#skF_7')) | ~r1_tarski(B_468, '#skF_7') | ~v3_pre_topc(B_468, '#skF_4') | ~m1_subset_1(B_468, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_963])).
% 7.91/2.76  tff(c_987, plain, (r1_tarski('#skF_7', k1_tops_1('#skF_4', '#skF_7')) | ~r1_tarski('#skF_7', '#skF_7') | ~v3_pre_topc('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_984])).
% 7.91/2.76  tff(c_990, plain, (r1_tarski('#skF_7', k1_tops_1('#skF_4', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_12, c_987])).
% 7.91/2.76  tff(c_844, plain, (![B_432]: (r2_hidden('#skF_8', B_432) | ~r1_tarski('#skF_7', B_432))), inference(resolution, [status(thm)], [c_40, c_107])).
% 7.91/2.76  tff(c_847, plain, (![B_2, B_432]: (r2_hidden('#skF_8', B_2) | ~r1_tarski(B_432, B_2) | ~r1_tarski('#skF_7', B_432))), inference(resolution, [status(thm)], [c_844, c_2])).
% 7.91/2.76  tff(c_998, plain, (r2_hidden('#skF_8', k1_tops_1('#skF_4', '#skF_7')) | ~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_990, c_847])).
% 7.91/2.76  tff(c_1006, plain, (r2_hidden('#skF_8', k1_tops_1('#skF_4', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_998])).
% 7.91/2.76  tff(c_16, plain, (![C_21, A_15, B_19]: (m1_connsp_2(C_21, A_15, B_19) | ~r2_hidden(B_19, k1_tops_1(A_15, C_21)) | ~m1_subset_1(C_21, k1_zfmisc_1(u1_struct_0(A_15))) | ~m1_subset_1(B_19, u1_struct_0(A_15)) | ~l1_pre_topc(A_15) | ~v2_pre_topc(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.91/2.76  tff(c_1009, plain, (m1_connsp_2('#skF_7', '#skF_4', '#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1006, c_16])).
% 7.91/2.76  tff(c_1014, plain, (m1_connsp_2('#skF_7', '#skF_4', '#skF_8') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_46, c_48, c_1009])).
% 7.91/2.76  tff(c_1015, plain, (m1_connsp_2('#skF_7', '#skF_4', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_64, c_1014])).
% 7.91/2.76  tff(c_1518, plain, (![B_557, A_555, D_559, E_556, C_560, G_558]: (r1_tmap_1(D_559, A_555, k2_tmap_1(B_557, A_555, C_560, D_559), G_558) | ~r1_tmap_1(B_557, A_555, C_560, G_558) | ~m1_connsp_2(E_556, B_557, G_558) | ~r1_tarski(E_556, u1_struct_0(D_559)) | ~m1_subset_1(G_558, u1_struct_0(D_559)) | ~m1_subset_1(G_558, u1_struct_0(B_557)) | ~m1_subset_1(E_556, k1_zfmisc_1(u1_struct_0(B_557))) | ~m1_pre_topc(D_559, B_557) | v2_struct_0(D_559) | ~m1_subset_1(C_560, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_557), u1_struct_0(A_555)))) | ~v1_funct_2(C_560, u1_struct_0(B_557), u1_struct_0(A_555)) | ~v1_funct_1(C_560) | ~l1_pre_topc(B_557) | ~v2_pre_topc(B_557) | v2_struct_0(B_557) | ~l1_pre_topc(A_555) | ~v2_pre_topc(A_555) | v2_struct_0(A_555))), inference(cnfTransformation, [status(thm)], [f_159])).
% 7.91/2.76  tff(c_1522, plain, (![D_559, A_555, C_560]: (r1_tmap_1(D_559, A_555, k2_tmap_1('#skF_4', A_555, C_560, D_559), '#skF_8') | ~r1_tmap_1('#skF_4', A_555, C_560, '#skF_8') | ~r1_tarski('#skF_7', u1_struct_0(D_559)) | ~m1_subset_1('#skF_8', u1_struct_0(D_559)) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc(D_559, '#skF_4') | v2_struct_0(D_559) | ~m1_subset_1(C_560, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(A_555)))) | ~v1_funct_2(C_560, u1_struct_0('#skF_4'), u1_struct_0(A_555)) | ~v1_funct_1(C_560) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_555) | ~v2_pre_topc(A_555) | v2_struct_0(A_555))), inference(resolution, [status(thm)], [c_1015, c_1518])).
% 7.91/2.76  tff(c_1529, plain, (![D_559, A_555, C_560]: (r1_tmap_1(D_559, A_555, k2_tmap_1('#skF_4', A_555, C_560, D_559), '#skF_8') | ~r1_tmap_1('#skF_4', A_555, C_560, '#skF_8') | ~r1_tarski('#skF_7', u1_struct_0(D_559)) | ~m1_subset_1('#skF_8', u1_struct_0(D_559)) | ~m1_pre_topc(D_559, '#skF_4') | v2_struct_0(D_559) | ~m1_subset_1(C_560, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(A_555)))) | ~v1_funct_2(C_560, u1_struct_0('#skF_4'), u1_struct_0(A_555)) | ~v1_funct_1(C_560) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_555) | ~v2_pre_topc(A_555) | v2_struct_0(A_555))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_48, c_46, c_1522])).
% 7.91/2.76  tff(c_4482, plain, (![D_999, A_1000, C_1001]: (r1_tmap_1(D_999, A_1000, k2_tmap_1('#skF_4', A_1000, C_1001, D_999), '#skF_8') | ~r1_tmap_1('#skF_4', A_1000, C_1001, '#skF_8') | ~r1_tarski('#skF_7', u1_struct_0(D_999)) | ~m1_subset_1('#skF_8', u1_struct_0(D_999)) | ~m1_pre_topc(D_999, '#skF_4') | v2_struct_0(D_999) | ~m1_subset_1(C_1001, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(A_1000)))) | ~v1_funct_2(C_1001, u1_struct_0('#skF_4'), u1_struct_0(A_1000)) | ~v1_funct_1(C_1001) | ~l1_pre_topc(A_1000) | ~v2_pre_topc(A_1000) | v2_struct_0(A_1000))), inference(negUnitSimplification, [status(thm)], [c_64, c_1529])).
% 7.91/2.76  tff(c_4484, plain, (![D_999]: (r1_tmap_1(D_999, '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_999), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | ~r1_tarski('#skF_7', u1_struct_0(D_999)) | ~m1_subset_1('#skF_8', u1_struct_0(D_999)) | ~m1_pre_topc(D_999, '#skF_4') | v2_struct_0(D_999) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_54, c_4482])).
% 7.91/2.76  tff(c_4487, plain, (![D_999]: (r1_tmap_1(D_999, '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_999), '#skF_8') | ~r1_tarski('#skF_7', u1_struct_0(D_999)) | ~m1_subset_1('#skF_8', u1_struct_0(D_999)) | ~m1_pre_topc(D_999, '#skF_4') | v2_struct_0(D_999) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_58, c_56, c_842, c_4484])).
% 7.91/2.76  tff(c_4489, plain, (![D_1002]: (r1_tmap_1(D_1002, '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_1002), '#skF_8') | ~r1_tarski('#skF_7', u1_struct_0(D_1002)) | ~m1_subset_1('#skF_8', u1_struct_0(D_1002)) | ~m1_pre_topc(D_1002, '#skF_4') | v2_struct_0(D_1002))), inference(negUnitSimplification, [status(thm)], [c_70, c_4487])).
% 7.91/2.76  tff(c_849, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_842, c_80])).
% 7.91/2.76  tff(c_4494, plain, (~r1_tarski('#skF_7', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_4489, c_849])).
% 7.91/2.76  tff(c_4501, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_81, c_38, c_4494])).
% 7.91/2.76  tff(c_4503, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_4501])).
% 7.91/2.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.91/2.76  
% 7.91/2.76  Inference rules
% 7.91/2.76  ----------------------
% 7.91/2.76  #Ref     : 0
% 7.91/2.76  #Sup     : 1006
% 7.91/2.76  #Fact    : 0
% 7.91/2.76  #Define  : 0
% 7.91/2.76  #Split   : 7
% 7.91/2.76  #Chain   : 0
% 7.91/2.76  #Close   : 0
% 7.91/2.76  
% 7.91/2.76  Ordering : KBO
% 7.91/2.76  
% 7.91/2.76  Simplification rules
% 7.91/2.76  ----------------------
% 7.91/2.76  #Subsume      : 428
% 7.91/2.76  #Demod        : 483
% 7.91/2.76  #Tautology    : 62
% 7.91/2.76  #SimpNegUnit  : 151
% 7.91/2.76  #BackRed      : 0
% 7.91/2.76  
% 7.91/2.76  #Partial instantiations: 0
% 7.91/2.76  #Strategies tried      : 1
% 7.91/2.76  
% 7.91/2.76  Timing (in seconds)
% 7.91/2.76  ----------------------
% 7.91/2.76  Preprocessing        : 0.40
% 7.91/2.76  Parsing              : 0.21
% 7.91/2.76  CNF conversion       : 0.05
% 7.91/2.76  Main loop            : 1.61
% 7.91/2.76  Inferencing          : 0.49
% 7.91/2.76  Reduction            : 0.42
% 7.91/2.76  Demodulation         : 0.29
% 7.91/2.76  BG Simplification    : 0.04
% 7.91/2.76  Subsumption          : 0.57
% 7.91/2.76  Abstraction          : 0.06
% 7.91/2.76  MUC search           : 0.00
% 7.91/2.76  Cooper               : 0.00
% 7.91/2.76  Total                : 2.05
% 7.91/2.76  Index Insertion      : 0.00
% 7.91/2.76  Index Deletion       : 0.00
% 7.91/2.76  Index Matching       : 0.00
% 7.91/2.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
