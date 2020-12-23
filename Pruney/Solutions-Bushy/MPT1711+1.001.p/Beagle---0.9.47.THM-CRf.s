%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1711+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:16 EST 2020

% Result     : Theorem 7.82s
% Output     : CNFRefutation 8.04s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 786 expanded)
%              Number of leaves         :   34 ( 310 expanded)
%              Depth                    :   24
%              Number of atoms          :  597 (5749 expanded)
%              Number of equality atoms :    5 ( 470 expanded)
%              Maximal formula depth    :   27 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tsep_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_185,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(k1_tsep_1(A,B,C)))
                   => ! [E] :
                        ( m1_subset_1(E,u1_struct_0(B))
                       => ! [F] :
                            ( m1_subset_1(F,u1_struct_0(C))
                           => ( ( E = D
                                & F = D )
                             => ! [G] :
                                  ( m1_connsp_2(G,B,E)
                                 => ! [H] :
                                      ( m1_connsp_2(H,C,F)
                                     => ? [I] :
                                          ( m1_subset_1(I,k1_zfmisc_1(u1_struct_0(k1_tsep_1(A,B,C))))
                                          & v3_pre_topc(I,k1_tsep_1(A,B,C))
                                          & r2_hidden(D,I)
                                          & r1_tarski(I,k2_xboole_0(G,H)) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tmap_1)).

tff(f_33,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_137,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).

tff(f_107,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(k1_tsep_1(A,B,C)))
                 => ! [E] :
                      ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(B)))
                     => ! [F] :
                          ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(C)))
                         => ~ ( v3_pre_topc(E,B)
                              & r2_hidden(D,E)
                              & v3_pre_topc(F,C)
                              & r2_hidden(D,F)
                              & ! [G] :
                                  ( m1_subset_1(G,k1_zfmisc_1(u1_struct_0(k1_tsep_1(A,B,C))))
                                 => ~ ( v3_pre_topc(G,k1_tsep_1(A,B,C))
                                      & r2_hidden(D,G)
                                      & r1_tarski(G,k2_xboole_0(E,F)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tmap_1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_36,plain,(
    '#skF_6' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_38,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_42,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_59,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42])).

tff(c_62,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_59])).

tff(c_60,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38])).

tff(c_34,plain,(
    m1_connsp_2('#skF_9','#skF_4','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_63,plain,(
    m1_connsp_2('#skF_9','#skF_4','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_34])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_56,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_54,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_50,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_86,plain,(
    ! [B_671,A_672] :
      ( v2_pre_topc(B_671)
      | ~ m1_pre_topc(B_671,A_672)
      | ~ l1_pre_topc(A_672)
      | ~ v2_pre_topc(A_672) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_89,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_86])).

tff(c_95,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_89])).

tff(c_73,plain,(
    ! [B_669,A_670] :
      ( l1_pre_topc(B_669)
      | ~ m1_pre_topc(B_669,A_670)
      | ~ l1_pre_topc(A_670) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_76,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_73])).

tff(c_82,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_76])).

tff(c_109,plain,(
    ! [C_686,A_687,B_688] :
      ( m1_subset_1(C_686,k1_zfmisc_1(u1_struct_0(A_687)))
      | ~ m1_connsp_2(C_686,A_687,B_688)
      | ~ m1_subset_1(B_688,u1_struct_0(A_687))
      | ~ l1_pre_topc(A_687)
      | ~ v2_pre_topc(A_687)
      | v2_struct_0(A_687) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_111,plain,
    ( m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_63,c_109])).

tff(c_116,plain,
    ( m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_82,c_62,c_111])).

tff(c_117,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_116])).

tff(c_24,plain,(
    ! [A_144,B_156,C_162] :
      ( r1_tarski('#skF_2'(A_144,B_156,C_162),C_162)
      | ~ m1_connsp_2(C_162,A_144,B_156)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ m1_subset_1(B_156,u1_struct_0(A_144))
      | ~ l1_pre_topc(A_144)
      | ~ v2_pre_topc(A_144)
      | v2_struct_0(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_124,plain,(
    ! [B_156] :
      ( r1_tarski('#skF_2'('#skF_4',B_156,'#skF_9'),'#skF_9')
      | ~ m1_connsp_2('#skF_9','#skF_4',B_156)
      | ~ m1_subset_1(B_156,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_117,c_24])).

tff(c_127,plain,(
    ! [B_156] :
      ( r1_tarski('#skF_2'('#skF_4',B_156,'#skF_9'),'#skF_9')
      | ~ m1_connsp_2('#skF_9','#skF_4',B_156)
      | ~ m1_subset_1(B_156,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_82,c_124])).

tff(c_128,plain,(
    ! [B_156] :
      ( r1_tarski('#skF_2'('#skF_4',B_156,'#skF_9'),'#skF_9')
      | ~ m1_connsp_2('#skF_9','#skF_4',B_156)
      | ~ m1_subset_1(B_156,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_127])).

tff(c_155,plain,(
    ! [B_704,A_705,C_706] :
      ( r2_hidden(B_704,'#skF_2'(A_705,B_704,C_706))
      | ~ m1_connsp_2(C_706,A_705,B_704)
      | ~ m1_subset_1(C_706,k1_zfmisc_1(u1_struct_0(A_705)))
      | ~ m1_subset_1(B_704,u1_struct_0(A_705))
      | ~ l1_pre_topc(A_705)
      | ~ v2_pre_topc(A_705)
      | v2_struct_0(A_705) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_159,plain,(
    ! [B_704] :
      ( r2_hidden(B_704,'#skF_2'('#skF_4',B_704,'#skF_9'))
      | ~ m1_connsp_2('#skF_9','#skF_4',B_704)
      | ~ m1_subset_1(B_704,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_117,c_155])).

tff(c_166,plain,(
    ! [B_704] :
      ( r2_hidden(B_704,'#skF_2'('#skF_4',B_704,'#skF_9'))
      | ~ m1_connsp_2('#skF_9','#skF_4',B_704)
      | ~ m1_subset_1(B_704,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_82,c_159])).

tff(c_167,plain,(
    ! [B_704] :
      ( r2_hidden(B_704,'#skF_2'('#skF_4',B_704,'#skF_9'))
      | ~ m1_connsp_2('#skF_9','#skF_4',B_704)
      | ~ m1_subset_1(B_704,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_166])).

tff(c_169,plain,(
    ! [A_708,B_709,C_710] :
      ( v3_pre_topc('#skF_2'(A_708,B_709,C_710),A_708)
      | ~ m1_connsp_2(C_710,A_708,B_709)
      | ~ m1_subset_1(C_710,k1_zfmisc_1(u1_struct_0(A_708)))
      | ~ m1_subset_1(B_709,u1_struct_0(A_708))
      | ~ l1_pre_topc(A_708)
      | ~ v2_pre_topc(A_708)
      | v2_struct_0(A_708) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_173,plain,(
    ! [B_709] :
      ( v3_pre_topc('#skF_2'('#skF_4',B_709,'#skF_9'),'#skF_4')
      | ~ m1_connsp_2('#skF_9','#skF_4',B_709)
      | ~ m1_subset_1(B_709,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_117,c_169])).

tff(c_180,plain,(
    ! [B_709] :
      ( v3_pre_topc('#skF_2'('#skF_4',B_709,'#skF_9'),'#skF_4')
      | ~ m1_connsp_2('#skF_9','#skF_4',B_709)
      | ~ m1_subset_1(B_709,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_82,c_173])).

tff(c_181,plain,(
    ! [B_709] :
      ( v3_pre_topc('#skF_2'('#skF_4',B_709,'#skF_9'),'#skF_4')
      | ~ m1_connsp_2('#skF_9','#skF_4',B_709)
      | ~ m1_subset_1(B_709,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_180])).

tff(c_28,plain,(
    ! [A_144,B_156,C_162] :
      ( m1_subset_1('#skF_2'(A_144,B_156,C_162),k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ m1_connsp_2(C_162,A_144,B_156)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ m1_subset_1(B_156,u1_struct_0(A_144))
      | ~ l1_pre_topc(A_144)
      | ~ v2_pre_topc(A_144)
      | v2_struct_0(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_40,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_32,plain,(
    m1_connsp_2('#skF_10','#skF_5','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_46,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_92,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_86])).

tff(c_98,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_92])).

tff(c_79,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_73])).

tff(c_85,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_79])).

tff(c_113,plain,
    ( m1_subset_1('#skF_10',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_109])).

tff(c_120,plain,
    ( m1_subset_1('#skF_10',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_85,c_40,c_113])).

tff(c_121,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_120])).

tff(c_130,plain,(
    ! [B_156] :
      ( r1_tarski('#skF_2'('#skF_5',B_156,'#skF_10'),'#skF_10')
      | ~ m1_connsp_2('#skF_10','#skF_5',B_156)
      | ~ m1_subset_1(B_156,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_121,c_24])).

tff(c_133,plain,(
    ! [B_156] :
      ( r1_tarski('#skF_2'('#skF_5',B_156,'#skF_10'),'#skF_10')
      | ~ m1_connsp_2('#skF_10','#skF_5',B_156)
      | ~ m1_subset_1(B_156,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_85,c_130])).

tff(c_134,plain,(
    ! [B_156] :
      ( r1_tarski('#skF_2'('#skF_5',B_156,'#skF_10'),'#skF_10')
      | ~ m1_connsp_2('#skF_10','#skF_5',B_156)
      | ~ m1_subset_1(B_156,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_133])).

tff(c_157,plain,(
    ! [B_704] :
      ( r2_hidden(B_704,'#skF_2'('#skF_5',B_704,'#skF_10'))
      | ~ m1_connsp_2('#skF_10','#skF_5',B_704)
      | ~ m1_subset_1(B_704,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_121,c_155])).

tff(c_162,plain,(
    ! [B_704] :
      ( r2_hidden(B_704,'#skF_2'('#skF_5',B_704,'#skF_10'))
      | ~ m1_connsp_2('#skF_10','#skF_5',B_704)
      | ~ m1_subset_1(B_704,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_85,c_157])).

tff(c_163,plain,(
    ! [B_704] :
      ( r2_hidden(B_704,'#skF_2'('#skF_5',B_704,'#skF_10'))
      | ~ m1_connsp_2('#skF_10','#skF_5',B_704)
      | ~ m1_subset_1(B_704,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_162])).

tff(c_171,plain,(
    ! [B_709] :
      ( v3_pre_topc('#skF_2'('#skF_5',B_709,'#skF_10'),'#skF_5')
      | ~ m1_connsp_2('#skF_10','#skF_5',B_709)
      | ~ m1_subset_1(B_709,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_121,c_169])).

tff(c_176,plain,(
    ! [B_709] :
      ( v3_pre_topc('#skF_2'('#skF_5',B_709,'#skF_10'),'#skF_5')
      | ~ m1_connsp_2('#skF_10','#skF_5',B_709)
      | ~ m1_subset_1(B_709,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_85,c_171])).

tff(c_177,plain,(
    ! [B_709] :
      ( v3_pre_topc('#skF_2'('#skF_5',B_709,'#skF_10'),'#skF_5')
      | ~ m1_connsp_2('#skF_10','#skF_5',B_709)
      | ~ m1_subset_1(B_709,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_176])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_61,plain,(
    m1_subset_1('#skF_8',u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_44])).

tff(c_241,plain,(
    ! [E_751,B_754,C_752,D_750,A_753,F_749] :
      ( r2_hidden(D_750,'#skF_1'(F_749,D_750,E_751,C_752,A_753,B_754))
      | ~ r2_hidden(D_750,F_749)
      | ~ v3_pre_topc(F_749,C_752)
      | ~ r2_hidden(D_750,E_751)
      | ~ v3_pre_topc(E_751,B_754)
      | ~ m1_subset_1(F_749,k1_zfmisc_1(u1_struct_0(C_752)))
      | ~ m1_subset_1(E_751,k1_zfmisc_1(u1_struct_0(B_754)))
      | ~ m1_subset_1(D_750,u1_struct_0(k1_tsep_1(A_753,B_754,C_752)))
      | ~ m1_pre_topc(C_752,A_753)
      | v2_struct_0(C_752)
      | ~ m1_pre_topc(B_754,A_753)
      | v2_struct_0(B_754)
      | ~ l1_pre_topc(A_753)
      | ~ v2_pre_topc(A_753)
      | v2_struct_0(A_753) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_248,plain,(
    ! [C_162,E_751,B_754,D_750,A_753,A_144,B_156] :
      ( r2_hidden(D_750,'#skF_1'('#skF_2'(A_144,B_156,C_162),D_750,E_751,A_144,A_753,B_754))
      | ~ r2_hidden(D_750,'#skF_2'(A_144,B_156,C_162))
      | ~ v3_pre_topc('#skF_2'(A_144,B_156,C_162),A_144)
      | ~ r2_hidden(D_750,E_751)
      | ~ v3_pre_topc(E_751,B_754)
      | ~ m1_subset_1(E_751,k1_zfmisc_1(u1_struct_0(B_754)))
      | ~ m1_subset_1(D_750,u1_struct_0(k1_tsep_1(A_753,B_754,A_144)))
      | ~ m1_pre_topc(A_144,A_753)
      | ~ m1_pre_topc(B_754,A_753)
      | v2_struct_0(B_754)
      | ~ l1_pre_topc(A_753)
      | ~ v2_pre_topc(A_753)
      | v2_struct_0(A_753)
      | ~ m1_connsp_2(C_162,A_144,B_156)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ m1_subset_1(B_156,u1_struct_0(A_144))
      | ~ l1_pre_topc(A_144)
      | ~ v2_pre_topc(A_144)
      | v2_struct_0(A_144) ) ),
    inference(resolution,[status(thm)],[c_28,c_241])).

tff(c_269,plain,(
    ! [F_795,B_800,A_799,D_796,E_797,C_798] :
      ( r1_tarski('#skF_1'(F_795,D_796,E_797,C_798,A_799,B_800),k2_xboole_0(E_797,F_795))
      | ~ r2_hidden(D_796,F_795)
      | ~ v3_pre_topc(F_795,C_798)
      | ~ r2_hidden(D_796,E_797)
      | ~ v3_pre_topc(E_797,B_800)
      | ~ m1_subset_1(F_795,k1_zfmisc_1(u1_struct_0(C_798)))
      | ~ m1_subset_1(E_797,k1_zfmisc_1(u1_struct_0(B_800)))
      | ~ m1_subset_1(D_796,u1_struct_0(k1_tsep_1(A_799,B_800,C_798)))
      | ~ m1_pre_topc(C_798,A_799)
      | v2_struct_0(C_798)
      | ~ m1_pre_topc(B_800,A_799)
      | v2_struct_0(B_800)
      | ~ l1_pre_topc(A_799)
      | ~ v2_pre_topc(A_799)
      | v2_struct_0(A_799) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_101,plain,(
    ! [A_677,C_678,B_679,D_680] :
      ( r1_tarski(k2_xboole_0(A_677,C_678),k2_xboole_0(B_679,D_680))
      | ~ r1_tarski(C_678,D_680)
      | ~ r1_tarski(A_677,B_679) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    ! [A_141,C_143,B_142] :
      ( r1_tarski(A_141,C_143)
      | ~ r1_tarski(B_142,C_143)
      | ~ r1_tarski(A_141,B_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_104,plain,(
    ! [D_680,A_141,C_678,A_677,B_679] :
      ( r1_tarski(A_141,k2_xboole_0(B_679,D_680))
      | ~ r1_tarski(A_141,k2_xboole_0(A_677,C_678))
      | ~ r1_tarski(C_678,D_680)
      | ~ r1_tarski(A_677,B_679) ) ),
    inference(resolution,[status(thm)],[c_101,c_18])).

tff(c_2812,plain,(
    ! [B_1576,D_1578,A_1574,E_1579,C_1577,D_1580,F_1575,B_1581] :
      ( r1_tarski('#skF_1'(F_1575,D_1580,E_1579,C_1577,A_1574,B_1576),k2_xboole_0(B_1581,D_1578))
      | ~ r1_tarski(F_1575,D_1578)
      | ~ r1_tarski(E_1579,B_1581)
      | ~ r2_hidden(D_1580,F_1575)
      | ~ v3_pre_topc(F_1575,C_1577)
      | ~ r2_hidden(D_1580,E_1579)
      | ~ v3_pre_topc(E_1579,B_1576)
      | ~ m1_subset_1(F_1575,k1_zfmisc_1(u1_struct_0(C_1577)))
      | ~ m1_subset_1(E_1579,k1_zfmisc_1(u1_struct_0(B_1576)))
      | ~ m1_subset_1(D_1580,u1_struct_0(k1_tsep_1(A_1574,B_1576,C_1577)))
      | ~ m1_pre_topc(C_1577,A_1574)
      | v2_struct_0(C_1577)
      | ~ m1_pre_topc(B_1576,A_1574)
      | v2_struct_0(B_1576)
      | ~ l1_pre_topc(A_1574)
      | ~ v2_pre_topc(A_1574)
      | v2_struct_0(A_1574) ) ),
    inference(resolution,[status(thm)],[c_269,c_104])).

tff(c_14,plain,(
    ! [A_15,D_127,B_79,C_111,F_139,E_135] :
      ( v3_pre_topc('#skF_1'(F_139,D_127,E_135,C_111,A_15,B_79),k1_tsep_1(A_15,B_79,C_111))
      | ~ r2_hidden(D_127,F_139)
      | ~ v3_pre_topc(F_139,C_111)
      | ~ r2_hidden(D_127,E_135)
      | ~ v3_pre_topc(E_135,B_79)
      | ~ m1_subset_1(F_139,k1_zfmisc_1(u1_struct_0(C_111)))
      | ~ m1_subset_1(E_135,k1_zfmisc_1(u1_struct_0(B_79)))
      | ~ m1_subset_1(D_127,u1_struct_0(k1_tsep_1(A_15,B_79,C_111)))
      | ~ m1_pre_topc(C_111,A_15)
      | v2_struct_0(C_111)
      | ~ m1_pre_topc(B_79,A_15)
      | v2_struct_0(B_79)
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_531,plain,(
    ! [D_897,E_898,C_899,A_900,F_896,B_901] :
      ( m1_subset_1('#skF_1'(F_896,D_897,E_898,C_899,A_900,B_901),k1_zfmisc_1(u1_struct_0(k1_tsep_1(A_900,B_901,C_899))))
      | ~ r2_hidden(D_897,F_896)
      | ~ v3_pre_topc(F_896,C_899)
      | ~ r2_hidden(D_897,E_898)
      | ~ v3_pre_topc(E_898,B_901)
      | ~ m1_subset_1(F_896,k1_zfmisc_1(u1_struct_0(C_899)))
      | ~ m1_subset_1(E_898,k1_zfmisc_1(u1_struct_0(B_901)))
      | ~ m1_subset_1(D_897,u1_struct_0(k1_tsep_1(A_900,B_901,C_899)))
      | ~ m1_pre_topc(C_899,A_900)
      | v2_struct_0(C_899)
      | ~ m1_pre_topc(B_901,A_900)
      | v2_struct_0(B_901)
      | ~ l1_pre_topc(A_900)
      | ~ v2_pre_topc(A_900)
      | v2_struct_0(A_900) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_30,plain,(
    ! [I_668] :
      ( ~ r1_tarski(I_668,k2_xboole_0('#skF_9','#skF_10'))
      | ~ r2_hidden('#skF_6',I_668)
      | ~ v3_pre_topc(I_668,k1_tsep_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(I_668,k1_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')))) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_64,plain,(
    ! [I_668] :
      ( ~ r1_tarski(I_668,k2_xboole_0('#skF_9','#skF_10'))
      | ~ r2_hidden('#skF_8',I_668)
      | ~ v3_pre_topc(I_668,k1_tsep_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(I_668,k1_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30])).

tff(c_543,plain,(
    ! [F_896,D_897,E_898] :
      ( ~ r1_tarski('#skF_1'(F_896,D_897,E_898,'#skF_5','#skF_3','#skF_4'),k2_xboole_0('#skF_9','#skF_10'))
      | ~ r2_hidden('#skF_8','#skF_1'(F_896,D_897,E_898,'#skF_5','#skF_3','#skF_4'))
      | ~ v3_pre_topc('#skF_1'(F_896,D_897,E_898,'#skF_5','#skF_3','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'))
      | ~ r2_hidden(D_897,F_896)
      | ~ v3_pre_topc(F_896,'#skF_5')
      | ~ r2_hidden(D_897,E_898)
      | ~ v3_pre_topc(E_898,'#skF_4')
      | ~ m1_subset_1(F_896,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(E_898,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(D_897,u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')))
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_531,c_64])).

tff(c_550,plain,(
    ! [F_896,D_897,E_898] :
      ( ~ r1_tarski('#skF_1'(F_896,D_897,E_898,'#skF_5','#skF_3','#skF_4'),k2_xboole_0('#skF_9','#skF_10'))
      | ~ r2_hidden('#skF_8','#skF_1'(F_896,D_897,E_898,'#skF_5','#skF_3','#skF_4'))
      | ~ v3_pre_topc('#skF_1'(F_896,D_897,E_898,'#skF_5','#skF_3','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'))
      | ~ r2_hidden(D_897,F_896)
      | ~ v3_pre_topc(F_896,'#skF_5')
      | ~ r2_hidden(D_897,E_898)
      | ~ v3_pre_topc(E_898,'#skF_4')
      | ~ m1_subset_1(F_896,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(E_898,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(D_897,u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_46,c_543])).

tff(c_786,plain,(
    ! [F_1026,D_1027,E_1028] :
      ( ~ r1_tarski('#skF_1'(F_1026,D_1027,E_1028,'#skF_5','#skF_3','#skF_4'),k2_xboole_0('#skF_9','#skF_10'))
      | ~ r2_hidden('#skF_8','#skF_1'(F_1026,D_1027,E_1028,'#skF_5','#skF_3','#skF_4'))
      | ~ v3_pre_topc('#skF_1'(F_1026,D_1027,E_1028,'#skF_5','#skF_3','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'))
      | ~ r2_hidden(D_1027,F_1026)
      | ~ v3_pre_topc(F_1026,'#skF_5')
      | ~ r2_hidden(D_1027,E_1028)
      | ~ v3_pre_topc(E_1028,'#skF_4')
      | ~ m1_subset_1(F_1026,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(E_1028,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(D_1027,u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_52,c_48,c_550])).

tff(c_790,plain,(
    ! [F_139,D_127,E_135] :
      ( ~ r1_tarski('#skF_1'(F_139,D_127,E_135,'#skF_5','#skF_3','#skF_4'),k2_xboole_0('#skF_9','#skF_10'))
      | ~ r2_hidden('#skF_8','#skF_1'(F_139,D_127,E_135,'#skF_5','#skF_3','#skF_4'))
      | ~ r2_hidden(D_127,F_139)
      | ~ v3_pre_topc(F_139,'#skF_5')
      | ~ r2_hidden(D_127,E_135)
      | ~ v3_pre_topc(E_135,'#skF_4')
      | ~ m1_subset_1(F_139,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(E_135,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(D_127,u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')))
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_14,c_786])).

tff(c_793,plain,(
    ! [F_139,D_127,E_135] :
      ( ~ r1_tarski('#skF_1'(F_139,D_127,E_135,'#skF_5','#skF_3','#skF_4'),k2_xboole_0('#skF_9','#skF_10'))
      | ~ r2_hidden('#skF_8','#skF_1'(F_139,D_127,E_135,'#skF_5','#skF_3','#skF_4'))
      | ~ r2_hidden(D_127,F_139)
      | ~ v3_pre_topc(F_139,'#skF_5')
      | ~ r2_hidden(D_127,E_135)
      | ~ v3_pre_topc(E_135,'#skF_4')
      | ~ m1_subset_1(F_139,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(E_135,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(D_127,u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_46,c_790])).

tff(c_794,plain,(
    ! [F_139,D_127,E_135] :
      ( ~ r1_tarski('#skF_1'(F_139,D_127,E_135,'#skF_5','#skF_3','#skF_4'),k2_xboole_0('#skF_9','#skF_10'))
      | ~ r2_hidden('#skF_8','#skF_1'(F_139,D_127,E_135,'#skF_5','#skF_3','#skF_4'))
      | ~ r2_hidden(D_127,F_139)
      | ~ v3_pre_topc(F_139,'#skF_5')
      | ~ r2_hidden(D_127,E_135)
      | ~ v3_pre_topc(E_135,'#skF_4')
      | ~ m1_subset_1(F_139,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(E_135,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(D_127,u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_52,c_48,c_793])).

tff(c_2898,plain,(
    ! [F_1575,D_1580,E_1579] :
      ( ~ r2_hidden('#skF_8','#skF_1'(F_1575,D_1580,E_1579,'#skF_5','#skF_3','#skF_4'))
      | ~ r1_tarski(F_1575,'#skF_10')
      | ~ r1_tarski(E_1579,'#skF_9')
      | ~ r2_hidden(D_1580,F_1575)
      | ~ v3_pre_topc(F_1575,'#skF_5')
      | ~ r2_hidden(D_1580,E_1579)
      | ~ v3_pre_topc(E_1579,'#skF_4')
      | ~ m1_subset_1(F_1575,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(E_1579,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(D_1580,u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')))
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2812,c_794])).

tff(c_2986,plain,(
    ! [F_1575,D_1580,E_1579] :
      ( ~ r2_hidden('#skF_8','#skF_1'(F_1575,D_1580,E_1579,'#skF_5','#skF_3','#skF_4'))
      | ~ r1_tarski(F_1575,'#skF_10')
      | ~ r1_tarski(E_1579,'#skF_9')
      | ~ r2_hidden(D_1580,F_1575)
      | ~ v3_pre_topc(F_1575,'#skF_5')
      | ~ r2_hidden(D_1580,E_1579)
      | ~ v3_pre_topc(E_1579,'#skF_4')
      | ~ m1_subset_1(F_1575,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(E_1579,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(D_1580,u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_46,c_2898])).

tff(c_3012,plain,(
    ! [F_1582,D_1583,E_1584] :
      ( ~ r2_hidden('#skF_8','#skF_1'(F_1582,D_1583,E_1584,'#skF_5','#skF_3','#skF_4'))
      | ~ r1_tarski(F_1582,'#skF_10')
      | ~ r1_tarski(E_1584,'#skF_9')
      | ~ r2_hidden(D_1583,F_1582)
      | ~ v3_pre_topc(F_1582,'#skF_5')
      | ~ r2_hidden(D_1583,E_1584)
      | ~ v3_pre_topc(E_1584,'#skF_4')
      | ~ m1_subset_1(F_1582,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(E_1584,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(D_1583,u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_52,c_48,c_2986])).

tff(c_3015,plain,(
    ! [B_156,C_162,E_751] :
      ( ~ r1_tarski('#skF_2'('#skF_5',B_156,C_162),'#skF_10')
      | ~ r1_tarski(E_751,'#skF_9')
      | ~ m1_subset_1('#skF_2'('#skF_5',B_156,C_162),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r2_hidden('#skF_8','#skF_2'('#skF_5',B_156,C_162))
      | ~ v3_pre_topc('#skF_2'('#skF_5',B_156,C_162),'#skF_5')
      | ~ r2_hidden('#skF_8',E_751)
      | ~ v3_pre_topc(E_751,'#skF_4')
      | ~ m1_subset_1(E_751,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_8',u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')))
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_connsp_2(C_162,'#skF_5',B_156)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_156,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_248,c_3012])).

tff(c_3018,plain,(
    ! [B_156,C_162,E_751] :
      ( ~ r1_tarski('#skF_2'('#skF_5',B_156,C_162),'#skF_10')
      | ~ r1_tarski(E_751,'#skF_9')
      | ~ m1_subset_1('#skF_2'('#skF_5',B_156,C_162),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r2_hidden('#skF_8','#skF_2'('#skF_5',B_156,C_162))
      | ~ v3_pre_topc('#skF_2'('#skF_5',B_156,C_162),'#skF_5')
      | ~ r2_hidden('#skF_8',E_751)
      | ~ v3_pre_topc(E_751,'#skF_4')
      | ~ m1_subset_1(E_751,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ m1_connsp_2(C_162,'#skF_5',B_156)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_156,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_85,c_56,c_54,c_50,c_46,c_61,c_3015])).

tff(c_3019,plain,(
    ! [B_156,C_162,E_751] :
      ( ~ r1_tarski('#skF_2'('#skF_5',B_156,C_162),'#skF_10')
      | ~ r1_tarski(E_751,'#skF_9')
      | ~ m1_subset_1('#skF_2'('#skF_5',B_156,C_162),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r2_hidden('#skF_8','#skF_2'('#skF_5',B_156,C_162))
      | ~ v3_pre_topc('#skF_2'('#skF_5',B_156,C_162),'#skF_5')
      | ~ r2_hidden('#skF_8',E_751)
      | ~ v3_pre_topc(E_751,'#skF_4')
      | ~ m1_subset_1(E_751,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_connsp_2(C_162,'#skF_5',B_156)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_156,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_58,c_52,c_3018])).

tff(c_3021,plain,(
    ! [B_1585,C_1586] :
      ( ~ r1_tarski('#skF_2'('#skF_5',B_1585,C_1586),'#skF_10')
      | ~ m1_subset_1('#skF_2'('#skF_5',B_1585,C_1586),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r2_hidden('#skF_8','#skF_2'('#skF_5',B_1585,C_1586))
      | ~ v3_pre_topc('#skF_2'('#skF_5',B_1585,C_1586),'#skF_5')
      | ~ m1_connsp_2(C_1586,'#skF_5',B_1585)
      | ~ m1_subset_1(C_1586,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1585,u1_struct_0('#skF_5')) ) ),
    inference(splitLeft,[status(thm)],[c_3019])).

tff(c_3025,plain,(
    ! [B_156,C_162] :
      ( ~ r1_tarski('#skF_2'('#skF_5',B_156,C_162),'#skF_10')
      | ~ r2_hidden('#skF_8','#skF_2'('#skF_5',B_156,C_162))
      | ~ v3_pre_topc('#skF_2'('#skF_5',B_156,C_162),'#skF_5')
      | ~ m1_connsp_2(C_162,'#skF_5',B_156)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_156,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_3021])).

tff(c_3028,plain,(
    ! [B_156,C_162] :
      ( ~ r1_tarski('#skF_2'('#skF_5',B_156,C_162),'#skF_10')
      | ~ r2_hidden('#skF_8','#skF_2'('#skF_5',B_156,C_162))
      | ~ v3_pre_topc('#skF_2'('#skF_5',B_156,C_162),'#skF_5')
      | ~ m1_connsp_2(C_162,'#skF_5',B_156)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_156,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_85,c_3025])).

tff(c_3030,plain,(
    ! [B_1587,C_1588] :
      ( ~ r1_tarski('#skF_2'('#skF_5',B_1587,C_1588),'#skF_10')
      | ~ r2_hidden('#skF_8','#skF_2'('#skF_5',B_1587,C_1588))
      | ~ v3_pre_topc('#skF_2'('#skF_5',B_1587,C_1588),'#skF_5')
      | ~ m1_connsp_2(C_1588,'#skF_5',B_1587)
      | ~ m1_subset_1(C_1588,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1587,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_3028])).

tff(c_3035,plain,(
    ! [B_709] :
      ( ~ r1_tarski('#skF_2'('#skF_5',B_709,'#skF_10'),'#skF_10')
      | ~ r2_hidden('#skF_8','#skF_2'('#skF_5',B_709,'#skF_10'))
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_connsp_2('#skF_10','#skF_5',B_709)
      | ~ m1_subset_1(B_709,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_177,c_3030])).

tff(c_3043,plain,(
    ! [B_1589] :
      ( ~ r1_tarski('#skF_2'('#skF_5',B_1589,'#skF_10'),'#skF_10')
      | ~ r2_hidden('#skF_8','#skF_2'('#skF_5',B_1589,'#skF_10'))
      | ~ m1_connsp_2('#skF_10','#skF_5',B_1589)
      | ~ m1_subset_1(B_1589,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_3035])).

tff(c_3047,plain,
    ( ~ r1_tarski('#skF_2'('#skF_5','#skF_8','#skF_10'),'#skF_10')
    | ~ m1_connsp_2('#skF_10','#skF_5','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_163,c_3043])).

tff(c_3050,plain,(
    ~ r1_tarski('#skF_2'('#skF_5','#skF_8','#skF_10'),'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_3047])).

tff(c_3053,plain,
    ( ~ m1_connsp_2('#skF_10','#skF_5','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_134,c_3050])).

tff(c_3057,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_3053])).

tff(c_3059,plain,(
    ! [E_1590] :
      ( ~ r1_tarski(E_1590,'#skF_9')
      | ~ r2_hidden('#skF_8',E_1590)
      | ~ v3_pre_topc(E_1590,'#skF_4')
      | ~ m1_subset_1(E_1590,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(splitRight,[status(thm)],[c_3019])).

tff(c_3063,plain,(
    ! [B_156,C_162] :
      ( ~ r1_tarski('#skF_2'('#skF_4',B_156,C_162),'#skF_9')
      | ~ r2_hidden('#skF_8','#skF_2'('#skF_4',B_156,C_162))
      | ~ v3_pre_topc('#skF_2'('#skF_4',B_156,C_162),'#skF_4')
      | ~ m1_connsp_2(C_162,'#skF_4',B_156)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_156,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_3059])).

tff(c_3069,plain,(
    ! [B_156,C_162] :
      ( ~ r1_tarski('#skF_2'('#skF_4',B_156,C_162),'#skF_9')
      | ~ r2_hidden('#skF_8','#skF_2'('#skF_4',B_156,C_162))
      | ~ v3_pre_topc('#skF_2'('#skF_4',B_156,C_162),'#skF_4')
      | ~ m1_connsp_2(C_162,'#skF_4',B_156)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_156,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_82,c_3063])).

tff(c_3072,plain,(
    ! [B_1591,C_1592] :
      ( ~ r1_tarski('#skF_2'('#skF_4',B_1591,C_1592),'#skF_9')
      | ~ r2_hidden('#skF_8','#skF_2'('#skF_4',B_1591,C_1592))
      | ~ v3_pre_topc('#skF_2'('#skF_4',B_1591,C_1592),'#skF_4')
      | ~ m1_connsp_2(C_1592,'#skF_4',B_1591)
      | ~ m1_subset_1(C_1592,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_1591,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_3069])).

tff(c_3077,plain,(
    ! [B_709] :
      ( ~ r1_tarski('#skF_2'('#skF_4',B_709,'#skF_9'),'#skF_9')
      | ~ r2_hidden('#skF_8','#skF_2'('#skF_4',B_709,'#skF_9'))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_connsp_2('#skF_9','#skF_4',B_709)
      | ~ m1_subset_1(B_709,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_181,c_3072])).

tff(c_3085,plain,(
    ! [B_1593] :
      ( ~ r1_tarski('#skF_2'('#skF_4',B_1593,'#skF_9'),'#skF_9')
      | ~ r2_hidden('#skF_8','#skF_2'('#skF_4',B_1593,'#skF_9'))
      | ~ m1_connsp_2('#skF_9','#skF_4',B_1593)
      | ~ m1_subset_1(B_1593,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_3077])).

tff(c_3089,plain,
    ( ~ r1_tarski('#skF_2'('#skF_4','#skF_8','#skF_9'),'#skF_9')
    | ~ m1_connsp_2('#skF_9','#skF_4','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_167,c_3085])).

tff(c_3092,plain,(
    ~ r1_tarski('#skF_2'('#skF_4','#skF_8','#skF_9'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_63,c_3089])).

tff(c_3123,plain,
    ( ~ m1_connsp_2('#skF_9','#skF_4','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_128,c_3092])).

tff(c_3127,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_63,c_3123])).

%------------------------------------------------------------------------------
