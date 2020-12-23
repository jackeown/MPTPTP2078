%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:02 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 184 expanded)
%              Number of leaves         :   35 (  88 expanded)
%              Depth                    :   11
%              Number of atoms          :  254 (1325 expanded)
%              Number of equality atoms :    5 (  65 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_206,negated_conjecture,(
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

tff(f_156,axiom,(
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

tff(f_109,axiom,(
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
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_40,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_26,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_36,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_70,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_36])).

tff(c_34,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_28,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_52,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_50,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_32,plain,(
    v3_pre_topc('#skF_6','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_156,plain,(
    ! [B_355,A_356,C_357] :
      ( r1_tarski(B_355,k1_tops_1(A_356,C_357))
      | ~ r1_tarski(B_355,C_357)
      | ~ v3_pre_topc(B_355,A_356)
      | ~ m1_subset_1(C_357,k1_zfmisc_1(u1_struct_0(A_356)))
      | ~ m1_subset_1(B_355,k1_zfmisc_1(u1_struct_0(A_356)))
      | ~ l1_pre_topc(A_356) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_158,plain,(
    ! [B_355] :
      ( r1_tarski(B_355,k1_tops_1('#skF_3','#skF_6'))
      | ~ r1_tarski(B_355,'#skF_6')
      | ~ v3_pre_topc(B_355,'#skF_3')
      | ~ m1_subset_1(B_355,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_156])).

tff(c_199,plain,(
    ! [B_363] :
      ( r1_tarski(B_363,k1_tops_1('#skF_3','#skF_6'))
      | ~ r1_tarski(B_363,'#skF_6')
      | ~ v3_pre_topc(B_363,'#skF_3')
      | ~ m1_subset_1(B_363,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_158])).

tff(c_202,plain,
    ( r1_tarski('#skF_6',k1_tops_1('#skF_3','#skF_6'))
    | ~ r1_tarski('#skF_6','#skF_6')
    | ~ v3_pre_topc('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_199])).

tff(c_205,plain,(
    r1_tarski('#skF_6',k1_tops_1('#skF_3','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_12,c_202])).

tff(c_30,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_72,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_30])).

tff(c_98,plain,(
    ! [C_339,B_340,A_341] :
      ( r2_hidden(C_339,B_340)
      | ~ r2_hidden(C_339,A_341)
      | ~ r1_tarski(A_341,B_340) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_106,plain,(
    ! [B_342] :
      ( r2_hidden('#skF_8',B_342)
      | ~ r1_tarski('#skF_6',B_342) ) ),
    inference(resolution,[status(thm)],[c_72,c_98])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_109,plain,(
    ! [B_2,B_342] :
      ( r2_hidden('#skF_8',B_2)
      | ~ r1_tarski(B_342,B_2)
      | ~ r1_tarski('#skF_6',B_342) ) ),
    inference(resolution,[status(thm)],[c_106,c_2])).

tff(c_209,plain,
    ( r2_hidden('#skF_8',k1_tops_1('#skF_3','#skF_6'))
    | ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_205,c_109])).

tff(c_215,plain,(
    r2_hidden('#skF_8',k1_tops_1('#skF_3','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_209])).

tff(c_367,plain,(
    ! [C_385,A_386,B_387] :
      ( m1_connsp_2(C_385,A_386,B_387)
      | ~ r2_hidden(B_387,k1_tops_1(A_386,C_385))
      | ~ m1_subset_1(C_385,k1_zfmisc_1(u1_struct_0(A_386)))
      | ~ m1_subset_1(B_387,u1_struct_0(A_386))
      | ~ l1_pre_topc(A_386)
      | ~ v2_pre_topc(A_386)
      | v2_struct_0(A_386) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_376,plain,
    ( m1_connsp_2('#skF_6','#skF_3','#skF_8')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_215,c_367])).

tff(c_400,plain,
    ( m1_connsp_2('#skF_6','#skF_3','#skF_8')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_70,c_38,c_376])).

tff(c_401,plain,(
    m1_connsp_2('#skF_6','#skF_3','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_400])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_68,plain,
    ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_7')
    | r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_69,plain,
    ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_8')
    | r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_68])).

tff(c_105,plain,(
    r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_69])).

tff(c_62,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_71,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_62])).

tff(c_120,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_71])).

tff(c_58,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_56,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_46,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_483,plain,(
    ! [E_432,C_429,B_433,A_431,G_428,D_430] :
      ( r1_tmap_1(B_433,A_431,C_429,G_428)
      | ~ r1_tmap_1(D_430,A_431,k2_tmap_1(B_433,A_431,C_429,D_430),G_428)
      | ~ m1_connsp_2(E_432,B_433,G_428)
      | ~ r1_tarski(E_432,u1_struct_0(D_430))
      | ~ m1_subset_1(G_428,u1_struct_0(D_430))
      | ~ m1_subset_1(G_428,u1_struct_0(B_433))
      | ~ m1_subset_1(E_432,k1_zfmisc_1(u1_struct_0(B_433)))
      | ~ m1_pre_topc(D_430,B_433)
      | v2_struct_0(D_430)
      | ~ m1_subset_1(C_429,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_433),u1_struct_0(A_431))))
      | ~ v1_funct_2(C_429,u1_struct_0(B_433),u1_struct_0(A_431))
      | ~ v1_funct_1(C_429)
      | ~ l1_pre_topc(B_433)
      | ~ v2_pre_topc(B_433)
      | v2_struct_0(B_433)
      | ~ l1_pre_topc(A_431)
      | ~ v2_pre_topc(A_431)
      | v2_struct_0(A_431) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_487,plain,(
    ! [E_432] :
      ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_8')
      | ~ m1_connsp_2(E_432,'#skF_3','#skF_8')
      | ~ r1_tarski(E_432,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(E_432,k1_zfmisc_1(u1_struct_0('#skF_3')))
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
    inference(resolution,[status(thm)],[c_105,c_483])).

tff(c_494,plain,(
    ! [E_432] :
      ( r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_8')
      | ~ m1_connsp_2(E_432,'#skF_3','#skF_8')
      | ~ r1_tarski(E_432,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(E_432,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_48,c_46,c_44,c_40,c_70,c_34,c_487])).

tff(c_496,plain,(
    ! [E_434] :
      ( ~ m1_connsp_2(E_434,'#skF_3','#skF_8')
      | ~ r1_tarski(E_434,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(E_434,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_42,c_120,c_494])).

tff(c_499,plain,
    ( ~ m1_connsp_2('#skF_6','#skF_3','#skF_8')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_38,c_496])).

tff(c_503,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_401,c_499])).

tff(c_504,plain,(
    r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_807,plain,(
    ! [F_486,A_483,D_485,C_484,B_487] :
      ( r1_tmap_1(D_485,A_483,k2_tmap_1(B_487,A_483,C_484,D_485),F_486)
      | ~ r1_tmap_1(B_487,A_483,C_484,F_486)
      | ~ m1_subset_1(F_486,u1_struct_0(D_485))
      | ~ m1_subset_1(F_486,u1_struct_0(B_487))
      | ~ m1_pre_topc(D_485,B_487)
      | v2_struct_0(D_485)
      | ~ m1_subset_1(C_484,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_487),u1_struct_0(A_483))))
      | ~ v1_funct_2(C_484,u1_struct_0(B_487),u1_struct_0(A_483))
      | ~ v1_funct_1(C_484)
      | ~ l1_pre_topc(B_487)
      | ~ v2_pre_topc(B_487)
      | v2_struct_0(B_487)
      | ~ l1_pre_topc(A_483)
      | ~ v2_pre_topc(A_483)
      | v2_struct_0(A_483) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_809,plain,(
    ! [D_485,F_486] :
      ( r1_tmap_1(D_485,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4',D_485),F_486)
      | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4',F_486)
      | ~ m1_subset_1(F_486,u1_struct_0(D_485))
      | ~ m1_subset_1(F_486,u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_485,'#skF_3')
      | v2_struct_0(D_485)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_44,c_807])).

tff(c_812,plain,(
    ! [D_485,F_486] :
      ( r1_tmap_1(D_485,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4',D_485),F_486)
      | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4',F_486)
      | ~ m1_subset_1(F_486,u1_struct_0(D_485))
      | ~ m1_subset_1(F_486,u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_485,'#skF_3')
      | v2_struct_0(D_485)
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_50,c_48,c_46,c_809])).

tff(c_862,plain,(
    ! [D_499,F_500] :
      ( r1_tmap_1(D_499,'#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4',D_499),F_500)
      | ~ r1_tmap_1('#skF_3','#skF_2','#skF_4',F_500)
      | ~ m1_subset_1(F_500,u1_struct_0(D_499))
      | ~ m1_subset_1(F_500,u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_499,'#skF_3')
      | v2_struct_0(D_499) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_812])).

tff(c_505,plain,(
    ~ r1_tmap_1('#skF_5','#skF_2',k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_865,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2','#skF_4','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_862,c_505])).

tff(c_868,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_70,c_34,c_504,c_865])).

tff(c_870,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_868])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:10:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.70/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.63  
% 3.70/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.64  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1
% 3.70/1.64  
% 3.70/1.64  %Foreground sorts:
% 3.70/1.64  
% 3.70/1.64  
% 3.70/1.64  %Background operators:
% 3.70/1.64  
% 3.70/1.64  
% 3.70/1.64  %Foreground operators:
% 3.70/1.64  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.70/1.64  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.70/1.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.70/1.64  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.70/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.70/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.70/1.64  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.70/1.64  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.70/1.64  tff('#skF_7', type, '#skF_7': $i).
% 3.70/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.70/1.64  tff('#skF_5', type, '#skF_5': $i).
% 3.70/1.64  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.70/1.64  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.70/1.64  tff('#skF_6', type, '#skF_6': $i).
% 3.70/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.70/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.70/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.70/1.64  tff('#skF_8', type, '#skF_8': $i).
% 3.70/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.70/1.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.70/1.64  tff('#skF_4', type, '#skF_4': $i).
% 3.70/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.70/1.64  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.70/1.64  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.70/1.64  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.70/1.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.70/1.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.70/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.70/1.64  
% 3.70/1.65  tff(f_206, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((v3_pre_topc(E, B) & r2_hidden(F, E)) & r1_tarski(E, u1_struct_0(D))) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tmap_1)).
% 3.70/1.65  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.70/1.65  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 3.70/1.65  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.70/1.65  tff(f_69, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 3.70/1.65  tff(f_156, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tmap_1)).
% 3.70/1.65  tff(f_109, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 3.70/1.65  tff(c_42, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.70/1.65  tff(c_40, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.70/1.65  tff(c_26, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.70/1.65  tff(c_36, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.70/1.65  tff(c_70, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_36])).
% 3.70/1.65  tff(c_34, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.70/1.65  tff(c_28, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.70/1.65  tff(c_54, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.70/1.65  tff(c_52, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.70/1.65  tff(c_50, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.70/1.65  tff(c_38, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.70/1.65  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.70/1.65  tff(c_32, plain, (v3_pre_topc('#skF_6', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.70/1.65  tff(c_156, plain, (![B_355, A_356, C_357]: (r1_tarski(B_355, k1_tops_1(A_356, C_357)) | ~r1_tarski(B_355, C_357) | ~v3_pre_topc(B_355, A_356) | ~m1_subset_1(C_357, k1_zfmisc_1(u1_struct_0(A_356))) | ~m1_subset_1(B_355, k1_zfmisc_1(u1_struct_0(A_356))) | ~l1_pre_topc(A_356))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.70/1.65  tff(c_158, plain, (![B_355]: (r1_tarski(B_355, k1_tops_1('#skF_3', '#skF_6')) | ~r1_tarski(B_355, '#skF_6') | ~v3_pre_topc(B_355, '#skF_3') | ~m1_subset_1(B_355, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_156])).
% 3.70/1.65  tff(c_199, plain, (![B_363]: (r1_tarski(B_363, k1_tops_1('#skF_3', '#skF_6')) | ~r1_tarski(B_363, '#skF_6') | ~v3_pre_topc(B_363, '#skF_3') | ~m1_subset_1(B_363, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_158])).
% 3.70/1.65  tff(c_202, plain, (r1_tarski('#skF_6', k1_tops_1('#skF_3', '#skF_6')) | ~r1_tarski('#skF_6', '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_199])).
% 3.70/1.65  tff(c_205, plain, (r1_tarski('#skF_6', k1_tops_1('#skF_3', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_12, c_202])).
% 3.70/1.65  tff(c_30, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.70/1.65  tff(c_72, plain, (r2_hidden('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_30])).
% 3.70/1.65  tff(c_98, plain, (![C_339, B_340, A_341]: (r2_hidden(C_339, B_340) | ~r2_hidden(C_339, A_341) | ~r1_tarski(A_341, B_340))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.70/1.65  tff(c_106, plain, (![B_342]: (r2_hidden('#skF_8', B_342) | ~r1_tarski('#skF_6', B_342))), inference(resolution, [status(thm)], [c_72, c_98])).
% 3.70/1.65  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.70/1.65  tff(c_109, plain, (![B_2, B_342]: (r2_hidden('#skF_8', B_2) | ~r1_tarski(B_342, B_2) | ~r1_tarski('#skF_6', B_342))), inference(resolution, [status(thm)], [c_106, c_2])).
% 3.70/1.65  tff(c_209, plain, (r2_hidden('#skF_8', k1_tops_1('#skF_3', '#skF_6')) | ~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_205, c_109])).
% 3.70/1.65  tff(c_215, plain, (r2_hidden('#skF_8', k1_tops_1('#skF_3', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_209])).
% 3.70/1.65  tff(c_367, plain, (![C_385, A_386, B_387]: (m1_connsp_2(C_385, A_386, B_387) | ~r2_hidden(B_387, k1_tops_1(A_386, C_385)) | ~m1_subset_1(C_385, k1_zfmisc_1(u1_struct_0(A_386))) | ~m1_subset_1(B_387, u1_struct_0(A_386)) | ~l1_pre_topc(A_386) | ~v2_pre_topc(A_386) | v2_struct_0(A_386))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.70/1.65  tff(c_376, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_8') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_215, c_367])).
% 3.70/1.65  tff(c_400, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_8') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_70, c_38, c_376])).
% 3.70/1.65  tff(c_401, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_54, c_400])).
% 3.70/1.65  tff(c_60, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.70/1.65  tff(c_68, plain, (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_7') | r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.70/1.65  tff(c_69, plain, (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_8') | r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_68])).
% 3.70/1.65  tff(c_105, plain, (r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_8')), inference(splitLeft, [status(thm)], [c_69])).
% 3.70/1.65  tff(c_62, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.70/1.65  tff(c_71, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_62])).
% 3.70/1.65  tff(c_120, plain, (~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_71])).
% 3.70/1.65  tff(c_58, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.70/1.65  tff(c_56, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.70/1.65  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.70/1.65  tff(c_46, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.70/1.65  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_206])).
% 3.70/1.65  tff(c_483, plain, (![E_432, C_429, B_433, A_431, G_428, D_430]: (r1_tmap_1(B_433, A_431, C_429, G_428) | ~r1_tmap_1(D_430, A_431, k2_tmap_1(B_433, A_431, C_429, D_430), G_428) | ~m1_connsp_2(E_432, B_433, G_428) | ~r1_tarski(E_432, u1_struct_0(D_430)) | ~m1_subset_1(G_428, u1_struct_0(D_430)) | ~m1_subset_1(G_428, u1_struct_0(B_433)) | ~m1_subset_1(E_432, k1_zfmisc_1(u1_struct_0(B_433))) | ~m1_pre_topc(D_430, B_433) | v2_struct_0(D_430) | ~m1_subset_1(C_429, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_433), u1_struct_0(A_431)))) | ~v1_funct_2(C_429, u1_struct_0(B_433), u1_struct_0(A_431)) | ~v1_funct_1(C_429) | ~l1_pre_topc(B_433) | ~v2_pre_topc(B_433) | v2_struct_0(B_433) | ~l1_pre_topc(A_431) | ~v2_pre_topc(A_431) | v2_struct_0(A_431))), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.70/1.65  tff(c_487, plain, (![E_432]: (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_8') | ~m1_connsp_2(E_432, '#skF_3', '#skF_8') | ~r1_tarski(E_432, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1(E_432, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_105, c_483])).
% 3.70/1.65  tff(c_494, plain, (![E_432]: (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_8') | ~m1_connsp_2(E_432, '#skF_3', '#skF_8') | ~r1_tarski(E_432, u1_struct_0('#skF_5')) | ~m1_subset_1(E_432, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_5') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_48, c_46, c_44, c_40, c_70, c_34, c_487])).
% 3.70/1.65  tff(c_496, plain, (![E_434]: (~m1_connsp_2(E_434, '#skF_3', '#skF_8') | ~r1_tarski(E_434, u1_struct_0('#skF_5')) | ~m1_subset_1(E_434, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_42, c_120, c_494])).
% 3.70/1.65  tff(c_499, plain, (~m1_connsp_2('#skF_6', '#skF_3', '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_38, c_496])).
% 3.70/1.65  tff(c_503, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_401, c_499])).
% 3.70/1.65  tff(c_504, plain, (r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_69])).
% 3.70/1.65  tff(c_807, plain, (![F_486, A_483, D_485, C_484, B_487]: (r1_tmap_1(D_485, A_483, k2_tmap_1(B_487, A_483, C_484, D_485), F_486) | ~r1_tmap_1(B_487, A_483, C_484, F_486) | ~m1_subset_1(F_486, u1_struct_0(D_485)) | ~m1_subset_1(F_486, u1_struct_0(B_487)) | ~m1_pre_topc(D_485, B_487) | v2_struct_0(D_485) | ~m1_subset_1(C_484, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_487), u1_struct_0(A_483)))) | ~v1_funct_2(C_484, u1_struct_0(B_487), u1_struct_0(A_483)) | ~v1_funct_1(C_484) | ~l1_pre_topc(B_487) | ~v2_pre_topc(B_487) | v2_struct_0(B_487) | ~l1_pre_topc(A_483) | ~v2_pre_topc(A_483) | v2_struct_0(A_483))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.70/1.65  tff(c_809, plain, (![D_485, F_486]: (r1_tmap_1(D_485, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_485), F_486) | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', F_486) | ~m1_subset_1(F_486, u1_struct_0(D_485)) | ~m1_subset_1(F_486, u1_struct_0('#skF_3')) | ~m1_pre_topc(D_485, '#skF_3') | v2_struct_0(D_485) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_807])).
% 3.70/1.65  tff(c_812, plain, (![D_485, F_486]: (r1_tmap_1(D_485, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_485), F_486) | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', F_486) | ~m1_subset_1(F_486, u1_struct_0(D_485)) | ~m1_subset_1(F_486, u1_struct_0('#skF_3')) | ~m1_pre_topc(D_485, '#skF_3') | v2_struct_0(D_485) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_50, c_48, c_46, c_809])).
% 3.70/1.65  tff(c_862, plain, (![D_499, F_500]: (r1_tmap_1(D_499, '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_499), F_500) | ~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', F_500) | ~m1_subset_1(F_500, u1_struct_0(D_499)) | ~m1_subset_1(F_500, u1_struct_0('#skF_3')) | ~m1_pre_topc(D_499, '#skF_3') | v2_struct_0(D_499))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_812])).
% 3.70/1.65  tff(c_505, plain, (~r1_tmap_1('#skF_5', '#skF_2', k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_69])).
% 3.70/1.65  tff(c_865, plain, (~r1_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_862, c_505])).
% 3.70/1.65  tff(c_868, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_70, c_34, c_504, c_865])).
% 3.70/1.65  tff(c_870, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_868])).
% 3.70/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.65  
% 3.70/1.65  Inference rules
% 3.70/1.65  ----------------------
% 3.70/1.65  #Ref     : 0
% 3.70/1.65  #Sup     : 175
% 3.70/1.65  #Fact    : 0
% 3.70/1.65  #Define  : 0
% 3.70/1.65  #Split   : 4
% 3.70/1.65  #Chain   : 0
% 3.70/1.65  #Close   : 0
% 3.70/1.65  
% 3.70/1.65  Ordering : KBO
% 3.70/1.66  
% 3.70/1.66  Simplification rules
% 3.70/1.66  ----------------------
% 3.70/1.66  #Subsume      : 84
% 3.70/1.66  #Demod        : 101
% 3.70/1.66  #Tautology    : 23
% 3.70/1.66  #SimpNegUnit  : 15
% 3.70/1.66  #BackRed      : 0
% 3.70/1.66  
% 3.70/1.66  #Partial instantiations: 0
% 3.70/1.66  #Strategies tried      : 1
% 3.70/1.66  
% 3.70/1.66  Timing (in seconds)
% 3.70/1.66  ----------------------
% 3.70/1.66  Preprocessing        : 0.40
% 3.70/1.66  Parsing              : 0.20
% 3.70/1.66  CNF conversion       : 0.05
% 3.70/1.66  Main loop            : 0.49
% 3.70/1.66  Inferencing          : 0.17
% 3.70/1.66  Reduction            : 0.15
% 3.70/1.66  Demodulation         : 0.10
% 3.70/1.66  BG Simplification    : 0.02
% 3.70/1.66  Subsumption          : 0.12
% 3.70/1.66  Abstraction          : 0.02
% 3.70/1.66  MUC search           : 0.00
% 3.70/1.66  Cooper               : 0.00
% 3.70/1.66  Total                : 0.92
% 3.70/1.66  Index Insertion      : 0.00
% 3.70/1.66  Index Deletion       : 0.00
% 3.70/1.66  Index Matching       : 0.00
% 3.70/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
