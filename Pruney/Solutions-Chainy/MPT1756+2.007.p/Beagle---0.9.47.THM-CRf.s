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
% DateTime   : Thu Dec  3 10:27:02 EST 2020

% Result     : Theorem 4.70s
% Output     : CNFRefutation 5.09s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 382 expanded)
%              Number of leaves         :   36 ( 160 expanded)
%              Depth                    :   19
%              Number of atoms          :  363 (2470 expanded)
%              Number of equality atoms :    3 (  94 expanded)
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

tff(f_196,negated_conjecture,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_46,axiom,(
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

tff(f_63,axiom,(
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

tff(f_146,axiom,(
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

tff(c_46,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_44,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_30,plain,(
    '#skF_9' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_38,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_75,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_38])).

tff(c_32,plain,(
    r1_tarski('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_62,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_60,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_50,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_82,plain,(
    ! [A_286,B_287] :
      ( r2_hidden('#skF_1'(A_286,B_287),A_286)
      | r1_tarski(A_286,B_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_87,plain,(
    ! [A_286] : r1_tarski(A_286,A_286) ),
    inference(resolution,[status(thm)],[c_82,c_4])).

tff(c_54,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_24,plain,(
    ! [B_36,A_34] :
      ( m1_subset_1(u1_struct_0(B_36),k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ m1_pre_topc(B_36,A_34)
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_56,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_40,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_36,plain,(
    v3_pre_topc('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_42,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_89,plain,(
    ! [C_289,B_290,A_291] :
      ( r2_hidden(C_289,B_290)
      | ~ r2_hidden(C_289,A_291)
      | ~ r1_tarski(A_291,B_290) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_122,plain,(
    ! [A_298,B_299,B_300] :
      ( r2_hidden('#skF_1'(A_298,B_299),B_300)
      | ~ r1_tarski(A_298,B_300)
      | r1_tarski(A_298,B_299) ) ),
    inference(resolution,[status(thm)],[c_6,c_89])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_131,plain,(
    ! [A_301,B_302,B_303,B_304] :
      ( r2_hidden('#skF_1'(A_301,B_302),B_303)
      | ~ r1_tarski(B_304,B_303)
      | ~ r1_tarski(A_301,B_304)
      | r1_tarski(A_301,B_302) ) ),
    inference(resolution,[status(thm)],[c_122,c_2])).

tff(c_138,plain,(
    ! [A_305,B_306] :
      ( r2_hidden('#skF_1'(A_305,B_306),u1_struct_0('#skF_6'))
      | ~ r1_tarski(A_305,'#skF_7')
      | r1_tarski(A_305,B_306) ) ),
    inference(resolution,[status(thm)],[c_32,c_131])).

tff(c_146,plain,(
    ! [A_305] :
      ( ~ r1_tarski(A_305,'#skF_7')
      | r1_tarski(A_305,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_138,c_4])).

tff(c_170,plain,(
    ! [B_311,A_312,C_313] :
      ( r1_tarski(B_311,k1_tops_1(A_312,C_313))
      | ~ r1_tarski(B_311,C_313)
      | ~ v3_pre_topc(B_311,A_312)
      | ~ m1_subset_1(C_313,k1_zfmisc_1(u1_struct_0(A_312)))
      | ~ m1_subset_1(B_311,k1_zfmisc_1(u1_struct_0(A_312)))
      | ~ l1_pre_topc(A_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_382,plain,(
    ! [B_348,A_349,B_350] :
      ( r1_tarski(B_348,k1_tops_1(A_349,u1_struct_0(B_350)))
      | ~ r1_tarski(B_348,u1_struct_0(B_350))
      | ~ v3_pre_topc(B_348,A_349)
      | ~ m1_subset_1(B_348,k1_zfmisc_1(u1_struct_0(A_349)))
      | ~ m1_pre_topc(B_350,A_349)
      | ~ l1_pre_topc(A_349) ) ),
    inference(resolution,[status(thm)],[c_24,c_170])).

tff(c_34,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_96,plain,(
    ! [B_292] :
      ( r2_hidden('#skF_8',B_292)
      | ~ r1_tarski('#skF_7',B_292) ) ),
    inference(resolution,[status(thm)],[c_34,c_89])).

tff(c_99,plain,(
    ! [B_2,B_292] :
      ( r2_hidden('#skF_8',B_2)
      | ~ r1_tarski(B_292,B_2)
      | ~ r1_tarski('#skF_7',B_292) ) ),
    inference(resolution,[status(thm)],[c_96,c_2])).

tff(c_731,plain,(
    ! [A_417,B_418,B_419] :
      ( r2_hidden('#skF_8',k1_tops_1(A_417,u1_struct_0(B_418)))
      | ~ r1_tarski('#skF_7',B_419)
      | ~ r1_tarski(B_419,u1_struct_0(B_418))
      | ~ v3_pre_topc(B_419,A_417)
      | ~ m1_subset_1(B_419,k1_zfmisc_1(u1_struct_0(A_417)))
      | ~ m1_pre_topc(B_418,A_417)
      | ~ l1_pre_topc(A_417) ) ),
    inference(resolution,[status(thm)],[c_382,c_99])).

tff(c_819,plain,(
    ! [A_430,A_431] :
      ( r2_hidden('#skF_8',k1_tops_1(A_430,u1_struct_0('#skF_6')))
      | ~ r1_tarski('#skF_7',A_431)
      | ~ v3_pre_topc(A_431,A_430)
      | ~ m1_subset_1(A_431,k1_zfmisc_1(u1_struct_0(A_430)))
      | ~ m1_pre_topc('#skF_6',A_430)
      | ~ l1_pre_topc(A_430)
      | ~ r1_tarski(A_431,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_146,c_731])).

tff(c_825,plain,
    ( r2_hidden('#skF_8',k1_tops_1('#skF_4',u1_struct_0('#skF_6')))
    | ~ v3_pre_topc('#skF_7','#skF_4')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_42,c_819])).

tff(c_830,plain,(
    r2_hidden('#skF_8',k1_tops_1('#skF_4',u1_struct_0('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_54,c_44,c_36,c_825])).

tff(c_10,plain,(
    ! [C_19,A_13,B_17] :
      ( m1_connsp_2(C_19,A_13,B_17)
      | ~ r2_hidden(B_17,k1_tops_1(A_13,C_19))
      | ~ m1_subset_1(C_19,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ m1_subset_1(B_17,u1_struct_0(A_13))
      | ~ l1_pre_topc(A_13)
      | ~ v2_pre_topc(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_848,plain,
    ( m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4','#skF_8')
    | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_830,c_10])).

tff(c_853,plain,
    ( m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4','#skF_8')
    | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_40,c_848])).

tff(c_854,plain,
    ( m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4','#skF_8')
    | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_853])).

tff(c_880,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_854])).

tff(c_890,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_880])).

tff(c_894,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_44,c_890])).

tff(c_895,plain,(
    m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_854])).

tff(c_896,plain,(
    m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_854])).

tff(c_72,plain,
    ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
    | r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_73,plain,
    ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
    | r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_72])).

tff(c_81,plain,(
    r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_73])).

tff(c_66,plain,
    ( ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_9')
    | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_74,plain,
    ( ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_66])).

tff(c_121,plain,(
    ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_74])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_960,plain,(
    ! [B_446,A_444,E_448,G_447,C_445,D_449] :
      ( r1_tmap_1(B_446,A_444,C_445,G_447)
      | ~ r1_tmap_1(D_449,A_444,k2_tmap_1(B_446,A_444,C_445,D_449),G_447)
      | ~ m1_connsp_2(E_448,B_446,G_447)
      | ~ r1_tarski(E_448,u1_struct_0(D_449))
      | ~ m1_subset_1(G_447,u1_struct_0(D_449))
      | ~ m1_subset_1(G_447,u1_struct_0(B_446))
      | ~ m1_subset_1(E_448,k1_zfmisc_1(u1_struct_0(B_446)))
      | ~ m1_pre_topc(D_449,B_446)
      | v2_struct_0(D_449)
      | ~ m1_subset_1(C_445,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_446),u1_struct_0(A_444))))
      | ~ v1_funct_2(C_445,u1_struct_0(B_446),u1_struct_0(A_444))
      | ~ v1_funct_1(C_445)
      | ~ l1_pre_topc(B_446)
      | ~ v2_pre_topc(B_446)
      | v2_struct_0(B_446)
      | ~ l1_pre_topc(A_444)
      | ~ v2_pre_topc(A_444)
      | v2_struct_0(A_444) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_962,plain,(
    ! [E_448] :
      ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
      | ~ m1_connsp_2(E_448,'#skF_4','#skF_8')
      | ~ r1_tarski(E_448,u1_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_448,k1_zfmisc_1(u1_struct_0('#skF_4')))
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
    inference(resolution,[status(thm)],[c_81,c_960])).

tff(c_965,plain,(
    ! [E_448] :
      ( r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
      | ~ m1_connsp_2(E_448,'#skF_4','#skF_8')
      | ~ r1_tarski(E_448,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(E_448,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_52,c_50,c_48,c_44,c_40,c_75,c_962])).

tff(c_967,plain,(
    ! [E_450] :
      ( ~ m1_connsp_2(E_450,'#skF_4','#skF_8')
      | ~ r1_tarski(E_450,u1_struct_0('#skF_6'))
      | ~ m1_subset_1(E_450,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_46,c_121,c_965])).

tff(c_970,plain,
    ( ~ m1_connsp_2(u1_struct_0('#skF_6'),'#skF_4','#skF_8')
    | ~ r1_tarski(u1_struct_0('#skF_6'),u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_896,c_967])).

tff(c_985,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_895,c_970])).

tff(c_986,plain,(
    r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_73])).

tff(c_988,plain,(
    ! [A_451,B_452] :
      ( r2_hidden('#skF_1'(A_451,B_452),A_451)
      | r1_tarski(A_451,B_452) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_993,plain,(
    ! [A_451] : r1_tarski(A_451,A_451) ),
    inference(resolution,[status(thm)],[c_988,c_4])).

tff(c_1037,plain,(
    ! [B_466,A_467,C_468] :
      ( r1_tarski(B_466,k1_tops_1(A_467,C_468))
      | ~ r1_tarski(B_466,C_468)
      | ~ v3_pre_topc(B_466,A_467)
      | ~ m1_subset_1(C_468,k1_zfmisc_1(u1_struct_0(A_467)))
      | ~ m1_subset_1(B_466,k1_zfmisc_1(u1_struct_0(A_467)))
      | ~ l1_pre_topc(A_467) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1041,plain,(
    ! [B_466] :
      ( r1_tarski(B_466,k1_tops_1('#skF_4','#skF_7'))
      | ~ r1_tarski(B_466,'#skF_7')
      | ~ v3_pre_topc(B_466,'#skF_4')
      | ~ m1_subset_1(B_466,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_1037])).

tff(c_1124,plain,(
    ! [B_488] :
      ( r1_tarski(B_488,k1_tops_1('#skF_4','#skF_7'))
      | ~ r1_tarski(B_488,'#skF_7')
      | ~ v3_pre_topc(B_488,'#skF_4')
      | ~ m1_subset_1(B_488,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1041])).

tff(c_1131,plain,
    ( r1_tarski('#skF_7',k1_tops_1('#skF_4','#skF_7'))
    | ~ r1_tarski('#skF_7','#skF_7')
    | ~ v3_pre_topc('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_1124])).

tff(c_1137,plain,(
    r1_tarski('#skF_7',k1_tops_1('#skF_4','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_993,c_1131])).

tff(c_997,plain,(
    ! [C_454,B_455,A_456] :
      ( r2_hidden(C_454,B_455)
      | ~ r2_hidden(C_454,A_456)
      | ~ r1_tarski(A_456,B_455) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1004,plain,(
    ! [B_457] :
      ( r2_hidden('#skF_8',B_457)
      | ~ r1_tarski('#skF_7',B_457) ) ),
    inference(resolution,[status(thm)],[c_34,c_997])).

tff(c_1007,plain,(
    ! [B_2,B_457] :
      ( r2_hidden('#skF_8',B_2)
      | ~ r1_tarski(B_457,B_2)
      | ~ r1_tarski('#skF_7',B_457) ) ),
    inference(resolution,[status(thm)],[c_1004,c_2])).

tff(c_1143,plain,
    ( r2_hidden('#skF_8',k1_tops_1('#skF_4','#skF_7'))
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_1137,c_1007])).

tff(c_1148,plain,(
    r2_hidden('#skF_8',k1_tops_1('#skF_4','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_993,c_1143])).

tff(c_1270,plain,(
    ! [C_510,A_511,B_512] :
      ( m1_connsp_2(C_510,A_511,B_512)
      | ~ r2_hidden(B_512,k1_tops_1(A_511,C_510))
      | ~ m1_subset_1(C_510,k1_zfmisc_1(u1_struct_0(A_511)))
      | ~ m1_subset_1(B_512,u1_struct_0(A_511))
      | ~ l1_pre_topc(A_511)
      | ~ v2_pre_topc(A_511)
      | v2_struct_0(A_511) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1277,plain,
    ( m1_connsp_2('#skF_7','#skF_4','#skF_8')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1148,c_1270])).

tff(c_1299,plain,
    ( m1_connsp_2('#skF_7','#skF_4','#skF_8')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_40,c_42,c_1277])).

tff(c_1300,plain,(
    m1_connsp_2('#skF_7','#skF_4','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1299])).

tff(c_1916,plain,(
    ! [B_606,E_608,D_609,A_604,G_607,C_605] :
      ( r1_tmap_1(D_609,A_604,k2_tmap_1(B_606,A_604,C_605,D_609),G_607)
      | ~ r1_tmap_1(B_606,A_604,C_605,G_607)
      | ~ m1_connsp_2(E_608,B_606,G_607)
      | ~ r1_tarski(E_608,u1_struct_0(D_609))
      | ~ m1_subset_1(G_607,u1_struct_0(D_609))
      | ~ m1_subset_1(G_607,u1_struct_0(B_606))
      | ~ m1_subset_1(E_608,k1_zfmisc_1(u1_struct_0(B_606)))
      | ~ m1_pre_topc(D_609,B_606)
      | v2_struct_0(D_609)
      | ~ m1_subset_1(C_605,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_606),u1_struct_0(A_604))))
      | ~ v1_funct_2(C_605,u1_struct_0(B_606),u1_struct_0(A_604))
      | ~ v1_funct_1(C_605)
      | ~ l1_pre_topc(B_606)
      | ~ v2_pre_topc(B_606)
      | v2_struct_0(B_606)
      | ~ l1_pre_topc(A_604)
      | ~ v2_pre_topc(A_604)
      | v2_struct_0(A_604) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1926,plain,(
    ! [D_609,A_604,C_605] :
      ( r1_tmap_1(D_609,A_604,k2_tmap_1('#skF_4',A_604,C_605,D_609),'#skF_8')
      | ~ r1_tmap_1('#skF_4',A_604,C_605,'#skF_8')
      | ~ r1_tarski('#skF_7',u1_struct_0(D_609))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_609))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc(D_609,'#skF_4')
      | v2_struct_0(D_609)
      | ~ m1_subset_1(C_605,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(A_604))))
      | ~ v1_funct_2(C_605,u1_struct_0('#skF_4'),u1_struct_0(A_604))
      | ~ v1_funct_1(C_605)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_604)
      | ~ v2_pre_topc(A_604)
      | v2_struct_0(A_604) ) ),
    inference(resolution,[status(thm)],[c_1300,c_1916])).

tff(c_1942,plain,(
    ! [D_609,A_604,C_605] :
      ( r1_tmap_1(D_609,A_604,k2_tmap_1('#skF_4',A_604,C_605,D_609),'#skF_8')
      | ~ r1_tmap_1('#skF_4',A_604,C_605,'#skF_8')
      | ~ r1_tarski('#skF_7',u1_struct_0(D_609))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_609))
      | ~ m1_pre_topc(D_609,'#skF_4')
      | v2_struct_0(D_609)
      | ~ m1_subset_1(C_605,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(A_604))))
      | ~ v1_funct_2(C_605,u1_struct_0('#skF_4'),u1_struct_0(A_604))
      | ~ v1_funct_1(C_605)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_604)
      | ~ v2_pre_topc(A_604)
      | v2_struct_0(A_604) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_42,c_40,c_1926])).

tff(c_1945,plain,(
    ! [D_610,A_611,C_612] :
      ( r1_tmap_1(D_610,A_611,k2_tmap_1('#skF_4',A_611,C_612,D_610),'#skF_8')
      | ~ r1_tmap_1('#skF_4',A_611,C_612,'#skF_8')
      | ~ r1_tarski('#skF_7',u1_struct_0(D_610))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_610))
      | ~ m1_pre_topc(D_610,'#skF_4')
      | v2_struct_0(D_610)
      | ~ m1_subset_1(C_612,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(A_611))))
      | ~ v1_funct_2(C_612,u1_struct_0('#skF_4'),u1_struct_0(A_611))
      | ~ v1_funct_1(C_612)
      | ~ l1_pre_topc(A_611)
      | ~ v2_pre_topc(A_611)
      | v2_struct_0(A_611) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1942])).

tff(c_1947,plain,(
    ! [D_610] :
      ( r1_tmap_1(D_610,'#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5',D_610),'#skF_8')
      | ~ r1_tmap_1('#skF_4','#skF_3','#skF_5','#skF_8')
      | ~ r1_tarski('#skF_7',u1_struct_0(D_610))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_610))
      | ~ m1_pre_topc(D_610,'#skF_4')
      | v2_struct_0(D_610)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_1945])).

tff(c_1950,plain,(
    ! [D_610] :
      ( r1_tmap_1(D_610,'#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5',D_610),'#skF_8')
      | ~ r1_tarski('#skF_7',u1_struct_0(D_610))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_610))
      | ~ m1_pre_topc(D_610,'#skF_4')
      | v2_struct_0(D_610)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_52,c_50,c_986,c_1947])).

tff(c_1952,plain,(
    ! [D_613] :
      ( r1_tmap_1(D_613,'#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5',D_613),'#skF_8')
      | ~ r1_tarski('#skF_7',u1_struct_0(D_613))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_613))
      | ~ m1_pre_topc(D_613,'#skF_4')
      | v2_struct_0(D_613) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1950])).

tff(c_995,plain,(
    ~ r1_tmap_1('#skF_6','#skF_3',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_986,c_74])).

tff(c_1957,plain,
    ( ~ r1_tarski('#skF_7',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1952,c_995])).

tff(c_1964,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_75,c_32,c_1957])).

tff(c_1966,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1964])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:23:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.70/1.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.70/1.89  
% 4.70/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.70/1.89  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_4 > #skF_1
% 4.70/1.89  
% 4.70/1.89  %Foreground sorts:
% 4.70/1.89  
% 4.70/1.89  
% 4.70/1.89  %Background operators:
% 4.70/1.89  
% 4.70/1.89  
% 4.70/1.89  %Foreground operators:
% 4.70/1.89  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.70/1.89  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 4.70/1.89  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.70/1.89  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.70/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.70/1.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.70/1.89  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.70/1.89  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.70/1.89  tff('#skF_7', type, '#skF_7': $i).
% 4.70/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.70/1.89  tff('#skF_5', type, '#skF_5': $i).
% 4.70/1.89  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.70/1.89  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.70/1.89  tff('#skF_6', type, '#skF_6': $i).
% 4.70/1.89  tff('#skF_3', type, '#skF_3': $i).
% 4.70/1.89  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.70/1.89  tff('#skF_9', type, '#skF_9': $i).
% 4.70/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.70/1.89  tff('#skF_8', type, '#skF_8': $i).
% 4.70/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.70/1.89  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.70/1.89  tff('#skF_4', type, '#skF_4': $i).
% 4.70/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.70/1.89  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.70/1.89  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.70/1.89  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 4.70/1.89  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.70/1.89  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.70/1.89  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.70/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.70/1.89  
% 5.09/1.92  tff(f_196, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((v3_pre_topc(E, B) & r2_hidden(F, E)) & r1_tarski(E, u1_struct_0(D))) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tmap_1)).
% 5.09/1.92  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.09/1.92  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 5.09/1.92  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 5.09/1.92  tff(f_63, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 5.09/1.92  tff(f_146, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tmap_1)).
% 5.09/1.92  tff(c_46, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.09/1.92  tff(c_44, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.09/1.92  tff(c_30, plain, ('#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.09/1.92  tff(c_38, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.09/1.92  tff(c_75, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_38])).
% 5.09/1.92  tff(c_32, plain, (r1_tarski('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.09/1.92  tff(c_64, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.09/1.92  tff(c_62, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.09/1.92  tff(c_60, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.09/1.92  tff(c_52, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.09/1.92  tff(c_50, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.09/1.92  tff(c_82, plain, (![A_286, B_287]: (r2_hidden('#skF_1'(A_286, B_287), A_286) | r1_tarski(A_286, B_287))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.09/1.92  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.09/1.92  tff(c_87, plain, (![A_286]: (r1_tarski(A_286, A_286))), inference(resolution, [status(thm)], [c_82, c_4])).
% 5.09/1.92  tff(c_54, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.09/1.92  tff(c_24, plain, (![B_36, A_34]: (m1_subset_1(u1_struct_0(B_36), k1_zfmisc_1(u1_struct_0(A_34))) | ~m1_pre_topc(B_36, A_34) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.09/1.92  tff(c_58, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.09/1.92  tff(c_56, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.09/1.92  tff(c_40, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.09/1.92  tff(c_36, plain, (v3_pre_topc('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.09/1.92  tff(c_42, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.09/1.92  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.09/1.92  tff(c_89, plain, (![C_289, B_290, A_291]: (r2_hidden(C_289, B_290) | ~r2_hidden(C_289, A_291) | ~r1_tarski(A_291, B_290))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.09/1.92  tff(c_122, plain, (![A_298, B_299, B_300]: (r2_hidden('#skF_1'(A_298, B_299), B_300) | ~r1_tarski(A_298, B_300) | r1_tarski(A_298, B_299))), inference(resolution, [status(thm)], [c_6, c_89])).
% 5.09/1.92  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.09/1.92  tff(c_131, plain, (![A_301, B_302, B_303, B_304]: (r2_hidden('#skF_1'(A_301, B_302), B_303) | ~r1_tarski(B_304, B_303) | ~r1_tarski(A_301, B_304) | r1_tarski(A_301, B_302))), inference(resolution, [status(thm)], [c_122, c_2])).
% 5.09/1.92  tff(c_138, plain, (![A_305, B_306]: (r2_hidden('#skF_1'(A_305, B_306), u1_struct_0('#skF_6')) | ~r1_tarski(A_305, '#skF_7') | r1_tarski(A_305, B_306))), inference(resolution, [status(thm)], [c_32, c_131])).
% 5.09/1.92  tff(c_146, plain, (![A_305]: (~r1_tarski(A_305, '#skF_7') | r1_tarski(A_305, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_138, c_4])).
% 5.09/1.92  tff(c_170, plain, (![B_311, A_312, C_313]: (r1_tarski(B_311, k1_tops_1(A_312, C_313)) | ~r1_tarski(B_311, C_313) | ~v3_pre_topc(B_311, A_312) | ~m1_subset_1(C_313, k1_zfmisc_1(u1_struct_0(A_312))) | ~m1_subset_1(B_311, k1_zfmisc_1(u1_struct_0(A_312))) | ~l1_pre_topc(A_312))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.09/1.92  tff(c_382, plain, (![B_348, A_349, B_350]: (r1_tarski(B_348, k1_tops_1(A_349, u1_struct_0(B_350))) | ~r1_tarski(B_348, u1_struct_0(B_350)) | ~v3_pre_topc(B_348, A_349) | ~m1_subset_1(B_348, k1_zfmisc_1(u1_struct_0(A_349))) | ~m1_pre_topc(B_350, A_349) | ~l1_pre_topc(A_349))), inference(resolution, [status(thm)], [c_24, c_170])).
% 5.09/1.92  tff(c_34, plain, (r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.09/1.92  tff(c_96, plain, (![B_292]: (r2_hidden('#skF_8', B_292) | ~r1_tarski('#skF_7', B_292))), inference(resolution, [status(thm)], [c_34, c_89])).
% 5.09/1.92  tff(c_99, plain, (![B_2, B_292]: (r2_hidden('#skF_8', B_2) | ~r1_tarski(B_292, B_2) | ~r1_tarski('#skF_7', B_292))), inference(resolution, [status(thm)], [c_96, c_2])).
% 5.09/1.92  tff(c_731, plain, (![A_417, B_418, B_419]: (r2_hidden('#skF_8', k1_tops_1(A_417, u1_struct_0(B_418))) | ~r1_tarski('#skF_7', B_419) | ~r1_tarski(B_419, u1_struct_0(B_418)) | ~v3_pre_topc(B_419, A_417) | ~m1_subset_1(B_419, k1_zfmisc_1(u1_struct_0(A_417))) | ~m1_pre_topc(B_418, A_417) | ~l1_pre_topc(A_417))), inference(resolution, [status(thm)], [c_382, c_99])).
% 5.09/1.92  tff(c_819, plain, (![A_430, A_431]: (r2_hidden('#skF_8', k1_tops_1(A_430, u1_struct_0('#skF_6'))) | ~r1_tarski('#skF_7', A_431) | ~v3_pre_topc(A_431, A_430) | ~m1_subset_1(A_431, k1_zfmisc_1(u1_struct_0(A_430))) | ~m1_pre_topc('#skF_6', A_430) | ~l1_pre_topc(A_430) | ~r1_tarski(A_431, '#skF_7'))), inference(resolution, [status(thm)], [c_146, c_731])).
% 5.09/1.92  tff(c_825, plain, (r2_hidden('#skF_8', k1_tops_1('#skF_4', u1_struct_0('#skF_6'))) | ~v3_pre_topc('#skF_7', '#skF_4') | ~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4') | ~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_42, c_819])).
% 5.09/1.92  tff(c_830, plain, (r2_hidden('#skF_8', k1_tops_1('#skF_4', u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_54, c_44, c_36, c_825])).
% 5.09/1.92  tff(c_10, plain, (![C_19, A_13, B_17]: (m1_connsp_2(C_19, A_13, B_17) | ~r2_hidden(B_17, k1_tops_1(A_13, C_19)) | ~m1_subset_1(C_19, k1_zfmisc_1(u1_struct_0(A_13))) | ~m1_subset_1(B_17, u1_struct_0(A_13)) | ~l1_pre_topc(A_13) | ~v2_pre_topc(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.09/1.92  tff(c_848, plain, (m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', '#skF_8') | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_830, c_10])).
% 5.09/1.92  tff(c_853, plain, (m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', '#skF_8') | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_40, c_848])).
% 5.09/1.92  tff(c_854, plain, (m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', '#skF_8') | ~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_58, c_853])).
% 5.09/1.92  tff(c_880, plain, (~m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_854])).
% 5.09/1.92  tff(c_890, plain, (~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_24, c_880])).
% 5.09/1.92  tff(c_894, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_44, c_890])).
% 5.09/1.92  tff(c_895, plain, (m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_854])).
% 5.09/1.92  tff(c_896, plain, (m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_854])).
% 5.09/1.92  tff(c_72, plain, (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.09/1.92  tff(c_73, plain, (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_72])).
% 5.09/1.92  tff(c_81, plain, (r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(splitLeft, [status(thm)], [c_73])).
% 5.09/1.92  tff(c_66, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_9') | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.09/1.92  tff(c_74, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_66])).
% 5.09/1.92  tff(c_121, plain, (~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_74])).
% 5.09/1.92  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_196])).
% 5.09/1.92  tff(c_960, plain, (![B_446, A_444, E_448, G_447, C_445, D_449]: (r1_tmap_1(B_446, A_444, C_445, G_447) | ~r1_tmap_1(D_449, A_444, k2_tmap_1(B_446, A_444, C_445, D_449), G_447) | ~m1_connsp_2(E_448, B_446, G_447) | ~r1_tarski(E_448, u1_struct_0(D_449)) | ~m1_subset_1(G_447, u1_struct_0(D_449)) | ~m1_subset_1(G_447, u1_struct_0(B_446)) | ~m1_subset_1(E_448, k1_zfmisc_1(u1_struct_0(B_446))) | ~m1_pre_topc(D_449, B_446) | v2_struct_0(D_449) | ~m1_subset_1(C_445, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_446), u1_struct_0(A_444)))) | ~v1_funct_2(C_445, u1_struct_0(B_446), u1_struct_0(A_444)) | ~v1_funct_1(C_445) | ~l1_pre_topc(B_446) | ~v2_pre_topc(B_446) | v2_struct_0(B_446) | ~l1_pre_topc(A_444) | ~v2_pre_topc(A_444) | v2_struct_0(A_444))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.09/1.92  tff(c_962, plain, (![E_448]: (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | ~m1_connsp_2(E_448, '#skF_4', '#skF_8') | ~r1_tarski(E_448, u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1(E_448, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_81, c_960])).
% 5.09/1.92  tff(c_965, plain, (![E_448]: (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | ~m1_connsp_2(E_448, '#skF_4', '#skF_8') | ~r1_tarski(E_448, u1_struct_0('#skF_6')) | ~m1_subset_1(E_448, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_6') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_52, c_50, c_48, c_44, c_40, c_75, c_962])).
% 5.09/1.92  tff(c_967, plain, (![E_450]: (~m1_connsp_2(E_450, '#skF_4', '#skF_8') | ~r1_tarski(E_450, u1_struct_0('#skF_6')) | ~m1_subset_1(E_450, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_46, c_121, c_965])).
% 5.09/1.92  tff(c_970, plain, (~m1_connsp_2(u1_struct_0('#skF_6'), '#skF_4', '#skF_8') | ~r1_tarski(u1_struct_0('#skF_6'), u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_896, c_967])).
% 5.09/1.92  tff(c_985, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_895, c_970])).
% 5.09/1.92  tff(c_986, plain, (r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_73])).
% 5.09/1.92  tff(c_988, plain, (![A_451, B_452]: (r2_hidden('#skF_1'(A_451, B_452), A_451) | r1_tarski(A_451, B_452))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.09/1.92  tff(c_993, plain, (![A_451]: (r1_tarski(A_451, A_451))), inference(resolution, [status(thm)], [c_988, c_4])).
% 5.09/1.92  tff(c_1037, plain, (![B_466, A_467, C_468]: (r1_tarski(B_466, k1_tops_1(A_467, C_468)) | ~r1_tarski(B_466, C_468) | ~v3_pre_topc(B_466, A_467) | ~m1_subset_1(C_468, k1_zfmisc_1(u1_struct_0(A_467))) | ~m1_subset_1(B_466, k1_zfmisc_1(u1_struct_0(A_467))) | ~l1_pre_topc(A_467))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.09/1.92  tff(c_1041, plain, (![B_466]: (r1_tarski(B_466, k1_tops_1('#skF_4', '#skF_7')) | ~r1_tarski(B_466, '#skF_7') | ~v3_pre_topc(B_466, '#skF_4') | ~m1_subset_1(B_466, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_1037])).
% 5.09/1.92  tff(c_1124, plain, (![B_488]: (r1_tarski(B_488, k1_tops_1('#skF_4', '#skF_7')) | ~r1_tarski(B_488, '#skF_7') | ~v3_pre_topc(B_488, '#skF_4') | ~m1_subset_1(B_488, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1041])).
% 5.09/1.92  tff(c_1131, plain, (r1_tarski('#skF_7', k1_tops_1('#skF_4', '#skF_7')) | ~r1_tarski('#skF_7', '#skF_7') | ~v3_pre_topc('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_1124])).
% 5.09/1.92  tff(c_1137, plain, (r1_tarski('#skF_7', k1_tops_1('#skF_4', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_993, c_1131])).
% 5.09/1.92  tff(c_997, plain, (![C_454, B_455, A_456]: (r2_hidden(C_454, B_455) | ~r2_hidden(C_454, A_456) | ~r1_tarski(A_456, B_455))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.09/1.92  tff(c_1004, plain, (![B_457]: (r2_hidden('#skF_8', B_457) | ~r1_tarski('#skF_7', B_457))), inference(resolution, [status(thm)], [c_34, c_997])).
% 5.09/1.92  tff(c_1007, plain, (![B_2, B_457]: (r2_hidden('#skF_8', B_2) | ~r1_tarski(B_457, B_2) | ~r1_tarski('#skF_7', B_457))), inference(resolution, [status(thm)], [c_1004, c_2])).
% 5.09/1.92  tff(c_1143, plain, (r2_hidden('#skF_8', k1_tops_1('#skF_4', '#skF_7')) | ~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_1137, c_1007])).
% 5.09/1.92  tff(c_1148, plain, (r2_hidden('#skF_8', k1_tops_1('#skF_4', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_993, c_1143])).
% 5.09/1.92  tff(c_1270, plain, (![C_510, A_511, B_512]: (m1_connsp_2(C_510, A_511, B_512) | ~r2_hidden(B_512, k1_tops_1(A_511, C_510)) | ~m1_subset_1(C_510, k1_zfmisc_1(u1_struct_0(A_511))) | ~m1_subset_1(B_512, u1_struct_0(A_511)) | ~l1_pre_topc(A_511) | ~v2_pre_topc(A_511) | v2_struct_0(A_511))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.09/1.92  tff(c_1277, plain, (m1_connsp_2('#skF_7', '#skF_4', '#skF_8') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1148, c_1270])).
% 5.09/1.92  tff(c_1299, plain, (m1_connsp_2('#skF_7', '#skF_4', '#skF_8') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_40, c_42, c_1277])).
% 5.09/1.92  tff(c_1300, plain, (m1_connsp_2('#skF_7', '#skF_4', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_58, c_1299])).
% 5.09/1.92  tff(c_1916, plain, (![B_606, E_608, D_609, A_604, G_607, C_605]: (r1_tmap_1(D_609, A_604, k2_tmap_1(B_606, A_604, C_605, D_609), G_607) | ~r1_tmap_1(B_606, A_604, C_605, G_607) | ~m1_connsp_2(E_608, B_606, G_607) | ~r1_tarski(E_608, u1_struct_0(D_609)) | ~m1_subset_1(G_607, u1_struct_0(D_609)) | ~m1_subset_1(G_607, u1_struct_0(B_606)) | ~m1_subset_1(E_608, k1_zfmisc_1(u1_struct_0(B_606))) | ~m1_pre_topc(D_609, B_606) | v2_struct_0(D_609) | ~m1_subset_1(C_605, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_606), u1_struct_0(A_604)))) | ~v1_funct_2(C_605, u1_struct_0(B_606), u1_struct_0(A_604)) | ~v1_funct_1(C_605) | ~l1_pre_topc(B_606) | ~v2_pre_topc(B_606) | v2_struct_0(B_606) | ~l1_pre_topc(A_604) | ~v2_pre_topc(A_604) | v2_struct_0(A_604))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.09/1.92  tff(c_1926, plain, (![D_609, A_604, C_605]: (r1_tmap_1(D_609, A_604, k2_tmap_1('#skF_4', A_604, C_605, D_609), '#skF_8') | ~r1_tmap_1('#skF_4', A_604, C_605, '#skF_8') | ~r1_tarski('#skF_7', u1_struct_0(D_609)) | ~m1_subset_1('#skF_8', u1_struct_0(D_609)) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc(D_609, '#skF_4') | v2_struct_0(D_609) | ~m1_subset_1(C_605, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(A_604)))) | ~v1_funct_2(C_605, u1_struct_0('#skF_4'), u1_struct_0(A_604)) | ~v1_funct_1(C_605) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_604) | ~v2_pre_topc(A_604) | v2_struct_0(A_604))), inference(resolution, [status(thm)], [c_1300, c_1916])).
% 5.09/1.92  tff(c_1942, plain, (![D_609, A_604, C_605]: (r1_tmap_1(D_609, A_604, k2_tmap_1('#skF_4', A_604, C_605, D_609), '#skF_8') | ~r1_tmap_1('#skF_4', A_604, C_605, '#skF_8') | ~r1_tarski('#skF_7', u1_struct_0(D_609)) | ~m1_subset_1('#skF_8', u1_struct_0(D_609)) | ~m1_pre_topc(D_609, '#skF_4') | v2_struct_0(D_609) | ~m1_subset_1(C_605, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(A_604)))) | ~v1_funct_2(C_605, u1_struct_0('#skF_4'), u1_struct_0(A_604)) | ~v1_funct_1(C_605) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_604) | ~v2_pre_topc(A_604) | v2_struct_0(A_604))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_42, c_40, c_1926])).
% 5.09/1.92  tff(c_1945, plain, (![D_610, A_611, C_612]: (r1_tmap_1(D_610, A_611, k2_tmap_1('#skF_4', A_611, C_612, D_610), '#skF_8') | ~r1_tmap_1('#skF_4', A_611, C_612, '#skF_8') | ~r1_tarski('#skF_7', u1_struct_0(D_610)) | ~m1_subset_1('#skF_8', u1_struct_0(D_610)) | ~m1_pre_topc(D_610, '#skF_4') | v2_struct_0(D_610) | ~m1_subset_1(C_612, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(A_611)))) | ~v1_funct_2(C_612, u1_struct_0('#skF_4'), u1_struct_0(A_611)) | ~v1_funct_1(C_612) | ~l1_pre_topc(A_611) | ~v2_pre_topc(A_611) | v2_struct_0(A_611))), inference(negUnitSimplification, [status(thm)], [c_58, c_1942])).
% 5.09/1.92  tff(c_1947, plain, (![D_610]: (r1_tmap_1(D_610, '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_610), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_8') | ~r1_tarski('#skF_7', u1_struct_0(D_610)) | ~m1_subset_1('#skF_8', u1_struct_0(D_610)) | ~m1_pre_topc(D_610, '#skF_4') | v2_struct_0(D_610) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_1945])).
% 5.09/1.92  tff(c_1950, plain, (![D_610]: (r1_tmap_1(D_610, '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_610), '#skF_8') | ~r1_tarski('#skF_7', u1_struct_0(D_610)) | ~m1_subset_1('#skF_8', u1_struct_0(D_610)) | ~m1_pre_topc(D_610, '#skF_4') | v2_struct_0(D_610) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_52, c_50, c_986, c_1947])).
% 5.09/1.92  tff(c_1952, plain, (![D_613]: (r1_tmap_1(D_613, '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_613), '#skF_8') | ~r1_tarski('#skF_7', u1_struct_0(D_613)) | ~m1_subset_1('#skF_8', u1_struct_0(D_613)) | ~m1_pre_topc(D_613, '#skF_4') | v2_struct_0(D_613))), inference(negUnitSimplification, [status(thm)], [c_64, c_1950])).
% 5.09/1.92  tff(c_995, plain, (~r1_tmap_1('#skF_6', '#skF_3', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_986, c_74])).
% 5.09/1.92  tff(c_1957, plain, (~r1_tarski('#skF_7', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_1952, c_995])).
% 5.09/1.92  tff(c_1964, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_75, c_32, c_1957])).
% 5.09/1.92  tff(c_1966, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_1964])).
% 5.09/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.09/1.92  
% 5.09/1.92  Inference rules
% 5.09/1.92  ----------------------
% 5.09/1.92  #Ref     : 0
% 5.09/1.92  #Sup     : 425
% 5.09/1.92  #Fact    : 0
% 5.09/1.92  #Define  : 0
% 5.09/1.92  #Split   : 9
% 5.09/1.92  #Chain   : 0
% 5.09/1.92  #Close   : 0
% 5.09/1.92  
% 5.09/1.92  Ordering : KBO
% 5.09/1.92  
% 5.09/1.92  Simplification rules
% 5.09/1.92  ----------------------
% 5.09/1.92  #Subsume      : 126
% 5.09/1.92  #Demod        : 239
% 5.09/1.92  #Tautology    : 56
% 5.09/1.92  #SimpNegUnit  : 45
% 5.09/1.92  #BackRed      : 0
% 5.09/1.92  
% 5.09/1.92  #Partial instantiations: 0
% 5.09/1.92  #Strategies tried      : 1
% 5.09/1.92  
% 5.09/1.92  Timing (in seconds)
% 5.09/1.92  ----------------------
% 5.09/1.92  Preprocessing        : 0.37
% 5.09/1.92  Parsing              : 0.19
% 5.09/1.92  CNF conversion       : 0.05
% 5.09/1.92  Main loop            : 0.75
% 5.09/1.92  Inferencing          : 0.25
% 5.09/1.92  Reduction            : 0.23
% 5.09/1.92  Demodulation         : 0.16
% 5.09/1.92  BG Simplification    : 0.03
% 5.09/1.92  Subsumption          : 0.19
% 5.09/1.92  Abstraction          : 0.03
% 5.09/1.92  MUC search           : 0.00
% 5.09/1.92  Cooper               : 0.00
% 5.09/1.92  Total                : 1.17
% 5.09/1.92  Index Insertion      : 0.00
% 5.09/1.92  Index Deletion       : 0.00
% 5.09/1.92  Index Matching       : 0.00
% 5.09/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
