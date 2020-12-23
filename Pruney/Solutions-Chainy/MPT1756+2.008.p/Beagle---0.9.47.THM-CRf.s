%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:02 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 230 expanded)
%              Number of leaves         :   31 ( 103 expanded)
%              Depth                    :   18
%              Number of atoms          :  307 (1783 expanded)
%              Number of equality atoms :   12 (  96 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(f_160,negated_conjecture,(
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

tff(f_46,axiom,(
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

tff(f_110,axiom,(
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

tff(c_30,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_28,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_14,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_22,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_59,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_22])).

tff(c_16,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_36,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_34,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_56,plain,
    ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
    | r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_57,plain,
    ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
    | r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_56])).

tff(c_64,plain,(
    r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_57])).

tff(c_18,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_24,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_40,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_38,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_26,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_20,plain,(
    v3_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_4,plain,(
    ! [B_9,D_15,C_13,A_1] :
      ( k1_tops_1(B_9,D_15) = D_15
      | ~ v3_pre_topc(D_15,B_9)
      | ~ m1_subset_1(D_15,k1_zfmisc_1(u1_struct_0(B_9)))
      | ~ m1_subset_1(C_13,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(B_9)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_67,plain,(
    ! [C_270,A_271] :
      ( ~ m1_subset_1(C_270,k1_zfmisc_1(u1_struct_0(A_271)))
      | ~ l1_pre_topc(A_271)
      | ~ v2_pre_topc(A_271) ) ),
    inference(splitLeft,[status(thm)],[c_4])).

tff(c_70,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_67])).

tff(c_74,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_70])).

tff(c_76,plain,(
    ! [B_272,D_273] :
      ( k1_tops_1(B_272,D_273) = D_273
      | ~ v3_pre_topc(D_273,B_272)
      | ~ m1_subset_1(D_273,k1_zfmisc_1(u1_struct_0(B_272)))
      | ~ l1_pre_topc(B_272) ) ),
    inference(splitRight,[status(thm)],[c_4])).

tff(c_79,plain,
    ( k1_tops_1('#skF_2','#skF_5') = '#skF_5'
    | ~ v3_pre_topc('#skF_5','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_76])).

tff(c_82,plain,(
    k1_tops_1('#skF_2','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_20,c_79])).

tff(c_101,plain,(
    ! [C_276,A_277,B_278] :
      ( m1_connsp_2(C_276,A_277,B_278)
      | ~ r2_hidden(B_278,k1_tops_1(A_277,C_276))
      | ~ m1_subset_1(C_276,k1_zfmisc_1(u1_struct_0(A_277)))
      | ~ m1_subset_1(B_278,u1_struct_0(A_277))
      | ~ l1_pre_topc(A_277)
      | ~ v2_pre_topc(A_277)
      | v2_struct_0(A_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_103,plain,(
    ! [B_278] :
      ( m1_connsp_2('#skF_5','#skF_2',B_278)
      | ~ r2_hidden(B_278,'#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_278,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_101])).

tff(c_105,plain,(
    ! [B_278] :
      ( m1_connsp_2('#skF_5','#skF_2',B_278)
      | ~ r2_hidden(B_278,'#skF_5')
      | ~ m1_subset_1(B_278,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_26,c_103])).

tff(c_107,plain,(
    ! [B_279] :
      ( m1_connsp_2('#skF_5','#skF_2',B_279)
      | ~ r2_hidden(B_279,'#skF_5')
      | ~ m1_subset_1(B_279,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_105])).

tff(c_110,plain,
    ( m1_connsp_2('#skF_5','#skF_2','#skF_6')
    | ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_107])).

tff(c_113,plain,(
    m1_connsp_2('#skF_5','#skF_2','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_110])).

tff(c_50,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_7')
    | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_58,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6')
    | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_50])).

tff(c_65,plain,(
    ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_135,plain,(
    ! [G_288,A_291,E_289,D_290,B_287,C_286] :
      ( r1_tmap_1(B_287,A_291,C_286,G_288)
      | ~ r1_tmap_1(D_290,A_291,k2_tmap_1(B_287,A_291,C_286,D_290),G_288)
      | ~ m1_connsp_2(E_289,B_287,G_288)
      | ~ r1_tarski(E_289,u1_struct_0(D_290))
      | ~ m1_subset_1(G_288,u1_struct_0(D_290))
      | ~ m1_subset_1(G_288,u1_struct_0(B_287))
      | ~ m1_subset_1(E_289,k1_zfmisc_1(u1_struct_0(B_287)))
      | ~ m1_pre_topc(D_290,B_287)
      | v2_struct_0(D_290)
      | ~ m1_subset_1(C_286,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_287),u1_struct_0(A_291))))
      | ~ v1_funct_2(C_286,u1_struct_0(B_287),u1_struct_0(A_291))
      | ~ v1_funct_1(C_286)
      | ~ l1_pre_topc(B_287)
      | ~ v2_pre_topc(B_287)
      | v2_struct_0(B_287)
      | ~ l1_pre_topc(A_291)
      | ~ v2_pre_topc(A_291)
      | v2_struct_0(A_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_137,plain,(
    ! [E_289] :
      ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
      | ~ m1_connsp_2(E_289,'#skF_2','#skF_6')
      | ~ r1_tarski(E_289,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_289,k1_zfmisc_1(u1_struct_0('#skF_2')))
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
    inference(resolution,[status(thm)],[c_64,c_135])).

tff(c_140,plain,(
    ! [E_289] :
      ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
      | ~ m1_connsp_2(E_289,'#skF_2','#skF_6')
      | ~ r1_tarski(E_289,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_289,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_40,c_38,c_36,c_34,c_32,c_28,c_24,c_59,c_137])).

tff(c_142,plain,(
    ! [E_292] :
      ( ~ m1_connsp_2(E_292,'#skF_2','#skF_6')
      | ~ r1_tarski(E_292,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_292,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_42,c_30,c_65,c_140])).

tff(c_145,plain,
    ( ~ m1_connsp_2('#skF_5','#skF_2','#skF_6')
    | ~ r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_26,c_142])).

tff(c_149,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_113,c_145])).

tff(c_150,plain,(
    ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_150])).

tff(c_154,plain,(
    r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(splitRight,[status(thm)],[c_57])).

tff(c_159,plain,(
    ! [C_293,A_294] :
      ( ~ m1_subset_1(C_293,k1_zfmisc_1(u1_struct_0(A_294)))
      | ~ l1_pre_topc(A_294)
      | ~ v2_pre_topc(A_294) ) ),
    inference(splitLeft,[status(thm)],[c_4])).

tff(c_162,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_159])).

tff(c_166,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_162])).

tff(c_168,plain,(
    ! [B_295,D_296] :
      ( k1_tops_1(B_295,D_296) = D_296
      | ~ v3_pre_topc(D_296,B_295)
      | ~ m1_subset_1(D_296,k1_zfmisc_1(u1_struct_0(B_295)))
      | ~ l1_pre_topc(B_295) ) ),
    inference(splitRight,[status(thm)],[c_4])).

tff(c_171,plain,
    ( k1_tops_1('#skF_2','#skF_5') = '#skF_5'
    | ~ v3_pre_topc('#skF_5','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_168])).

tff(c_174,plain,(
    k1_tops_1('#skF_2','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_20,c_171])).

tff(c_209,plain,(
    ! [C_305,A_306,B_307] :
      ( m1_connsp_2(C_305,A_306,B_307)
      | ~ r2_hidden(B_307,k1_tops_1(A_306,C_305))
      | ~ m1_subset_1(C_305,k1_zfmisc_1(u1_struct_0(A_306)))
      | ~ m1_subset_1(B_307,u1_struct_0(A_306))
      | ~ l1_pre_topc(A_306)
      | ~ v2_pre_topc(A_306)
      | v2_struct_0(A_306) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_211,plain,(
    ! [B_307] :
      ( m1_connsp_2('#skF_5','#skF_2',B_307)
      | ~ r2_hidden(B_307,'#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_307,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_209])).

tff(c_213,plain,(
    ! [B_307] :
      ( m1_connsp_2('#skF_5','#skF_2',B_307)
      | ~ r2_hidden(B_307,'#skF_5')
      | ~ m1_subset_1(B_307,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_26,c_211])).

tff(c_215,plain,(
    ! [B_308] :
      ( m1_connsp_2('#skF_5','#skF_2',B_308)
      | ~ r2_hidden(B_308,'#skF_5')
      | ~ m1_subset_1(B_308,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_213])).

tff(c_218,plain,
    ( m1_connsp_2('#skF_5','#skF_2','#skF_6')
    | ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_215])).

tff(c_221,plain,(
    m1_connsp_2('#skF_5','#skF_2','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_218])).

tff(c_222,plain,(
    ! [D_313,A_314,E_312,G_311,B_310,C_309] :
      ( r1_tmap_1(D_313,A_314,k2_tmap_1(B_310,A_314,C_309,D_313),G_311)
      | ~ r1_tmap_1(B_310,A_314,C_309,G_311)
      | ~ m1_connsp_2(E_312,B_310,G_311)
      | ~ r1_tarski(E_312,u1_struct_0(D_313))
      | ~ m1_subset_1(G_311,u1_struct_0(D_313))
      | ~ m1_subset_1(G_311,u1_struct_0(B_310))
      | ~ m1_subset_1(E_312,k1_zfmisc_1(u1_struct_0(B_310)))
      | ~ m1_pre_topc(D_313,B_310)
      | v2_struct_0(D_313)
      | ~ m1_subset_1(C_309,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_310),u1_struct_0(A_314))))
      | ~ v1_funct_2(C_309,u1_struct_0(B_310),u1_struct_0(A_314))
      | ~ v1_funct_1(C_309)
      | ~ l1_pre_topc(B_310)
      | ~ v2_pre_topc(B_310)
      | v2_struct_0(B_310)
      | ~ l1_pre_topc(A_314)
      | ~ v2_pre_topc(A_314)
      | v2_struct_0(A_314) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_224,plain,(
    ! [D_313,A_314,C_309] :
      ( r1_tmap_1(D_313,A_314,k2_tmap_1('#skF_2',A_314,C_309,D_313),'#skF_6')
      | ~ r1_tmap_1('#skF_2',A_314,C_309,'#skF_6')
      | ~ r1_tarski('#skF_5',u1_struct_0(D_313))
      | ~ m1_subset_1('#skF_6',u1_struct_0(D_313))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_pre_topc(D_313,'#skF_2')
      | v2_struct_0(D_313)
      | ~ m1_subset_1(C_309,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(A_314))))
      | ~ v1_funct_2(C_309,u1_struct_0('#skF_2'),u1_struct_0(A_314))
      | ~ v1_funct_1(C_309)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_314)
      | ~ v2_pre_topc(A_314)
      | v2_struct_0(A_314) ) ),
    inference(resolution,[status(thm)],[c_221,c_222])).

tff(c_227,plain,(
    ! [D_313,A_314,C_309] :
      ( r1_tmap_1(D_313,A_314,k2_tmap_1('#skF_2',A_314,C_309,D_313),'#skF_6')
      | ~ r1_tmap_1('#skF_2',A_314,C_309,'#skF_6')
      | ~ r1_tarski('#skF_5',u1_struct_0(D_313))
      | ~ m1_subset_1('#skF_6',u1_struct_0(D_313))
      | ~ m1_pre_topc(D_313,'#skF_2')
      | v2_struct_0(D_313)
      | ~ m1_subset_1(C_309,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(A_314))))
      | ~ v1_funct_2(C_309,u1_struct_0('#skF_2'),u1_struct_0(A_314))
      | ~ v1_funct_1(C_309)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_314)
      | ~ v2_pre_topc(A_314)
      | v2_struct_0(A_314) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_26,c_24,c_224])).

tff(c_229,plain,(
    ! [D_315,A_316,C_317] :
      ( r1_tmap_1(D_315,A_316,k2_tmap_1('#skF_2',A_316,C_317,D_315),'#skF_6')
      | ~ r1_tmap_1('#skF_2',A_316,C_317,'#skF_6')
      | ~ r1_tarski('#skF_5',u1_struct_0(D_315))
      | ~ m1_subset_1('#skF_6',u1_struct_0(D_315))
      | ~ m1_pre_topc(D_315,'#skF_2')
      | v2_struct_0(D_315)
      | ~ m1_subset_1(C_317,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(A_316))))
      | ~ v1_funct_2(C_317,u1_struct_0('#skF_2'),u1_struct_0(A_316))
      | ~ v1_funct_1(C_317)
      | ~ l1_pre_topc(A_316)
      | ~ v2_pre_topc(A_316)
      | v2_struct_0(A_316) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_227])).

tff(c_231,plain,(
    ! [D_315] :
      ( r1_tmap_1(D_315,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_315),'#skF_6')
      | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
      | ~ r1_tarski('#skF_5',u1_struct_0(D_315))
      | ~ m1_subset_1('#skF_6',u1_struct_0(D_315))
      | ~ m1_pre_topc(D_315,'#skF_2')
      | v2_struct_0(D_315)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_229])).

tff(c_234,plain,(
    ! [D_315] :
      ( r1_tmap_1(D_315,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_315),'#skF_6')
      | ~ r1_tarski('#skF_5',u1_struct_0(D_315))
      | ~ m1_subset_1('#skF_6',u1_struct_0(D_315))
      | ~ m1_pre_topc(D_315,'#skF_2')
      | v2_struct_0(D_315)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_36,c_34,c_154,c_231])).

tff(c_236,plain,(
    ! [D_318] :
      ( r1_tmap_1(D_318,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_318),'#skF_6')
      | ~ r1_tarski('#skF_5',u1_struct_0(D_318))
      | ~ m1_subset_1('#skF_6',u1_struct_0(D_318))
      | ~ m1_pre_topc(D_318,'#skF_2')
      | v2_struct_0(D_318) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_234])).

tff(c_155,plain,(
    ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_57])).

tff(c_239,plain,
    ( ~ r1_tarski('#skF_5',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_236,c_155])).

tff(c_242,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_59,c_16,c_239])).

tff(c_244,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_242])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:12:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.38  
% 2.60/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.39  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.60/1.39  
% 2.60/1.39  %Foreground sorts:
% 2.60/1.39  
% 2.60/1.39  
% 2.60/1.39  %Background operators:
% 2.60/1.39  
% 2.60/1.39  
% 2.60/1.39  %Foreground operators:
% 2.60/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.60/1.39  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 2.60/1.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.60/1.39  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.60/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.60/1.39  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 2.60/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.60/1.39  tff('#skF_7', type, '#skF_7': $i).
% 2.60/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.60/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.60/1.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.60/1.39  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.60/1.39  tff('#skF_6', type, '#skF_6': $i).
% 2.60/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.60/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.60/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.60/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.60/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.60/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.60/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.39  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.60/1.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.60/1.39  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 2.60/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.60/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.60/1.39  
% 2.60/1.41  tff(f_160, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((v3_pre_topc(E, B) & r2_hidden(F, E)) & r1_tarski(E, u1_struct_0(D))) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tmap_1)).
% 2.60/1.41  tff(f_46, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 2.60/1.41  tff(f_63, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 2.60/1.41  tff(f_110, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tmap_1)).
% 2.60/1.41  tff(c_30, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.60/1.41  tff(c_28, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.60/1.41  tff(c_14, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.60/1.41  tff(c_22, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.60/1.41  tff(c_59, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_22])).
% 2.60/1.41  tff(c_16, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.60/1.41  tff(c_48, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.60/1.41  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.60/1.41  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.60/1.41  tff(c_36, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.60/1.41  tff(c_34, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.60/1.41  tff(c_56, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.60/1.41  tff(c_57, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_56])).
% 2.60/1.41  tff(c_64, plain, (r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_57])).
% 2.60/1.41  tff(c_18, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.60/1.41  tff(c_24, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.60/1.41  tff(c_42, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.60/1.41  tff(c_40, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.60/1.41  tff(c_38, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.60/1.41  tff(c_26, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.60/1.41  tff(c_20, plain, (v3_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.60/1.41  tff(c_4, plain, (![B_9, D_15, C_13, A_1]: (k1_tops_1(B_9, D_15)=D_15 | ~v3_pre_topc(D_15, B_9) | ~m1_subset_1(D_15, k1_zfmisc_1(u1_struct_0(B_9))) | ~m1_subset_1(C_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(B_9) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.60/1.41  tff(c_67, plain, (![C_270, A_271]: (~m1_subset_1(C_270, k1_zfmisc_1(u1_struct_0(A_271))) | ~l1_pre_topc(A_271) | ~v2_pre_topc(A_271))), inference(splitLeft, [status(thm)], [c_4])).
% 2.60/1.41  tff(c_70, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_67])).
% 2.60/1.41  tff(c_74, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_70])).
% 2.60/1.41  tff(c_76, plain, (![B_272, D_273]: (k1_tops_1(B_272, D_273)=D_273 | ~v3_pre_topc(D_273, B_272) | ~m1_subset_1(D_273, k1_zfmisc_1(u1_struct_0(B_272))) | ~l1_pre_topc(B_272))), inference(splitRight, [status(thm)], [c_4])).
% 2.60/1.41  tff(c_79, plain, (k1_tops_1('#skF_2', '#skF_5')='#skF_5' | ~v3_pre_topc('#skF_5', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_76])).
% 2.60/1.41  tff(c_82, plain, (k1_tops_1('#skF_2', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_20, c_79])).
% 2.60/1.41  tff(c_101, plain, (![C_276, A_277, B_278]: (m1_connsp_2(C_276, A_277, B_278) | ~r2_hidden(B_278, k1_tops_1(A_277, C_276)) | ~m1_subset_1(C_276, k1_zfmisc_1(u1_struct_0(A_277))) | ~m1_subset_1(B_278, u1_struct_0(A_277)) | ~l1_pre_topc(A_277) | ~v2_pre_topc(A_277) | v2_struct_0(A_277))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.60/1.41  tff(c_103, plain, (![B_278]: (m1_connsp_2('#skF_5', '#skF_2', B_278) | ~r2_hidden(B_278, '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_278, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_101])).
% 2.60/1.41  tff(c_105, plain, (![B_278]: (m1_connsp_2('#skF_5', '#skF_2', B_278) | ~r2_hidden(B_278, '#skF_5') | ~m1_subset_1(B_278, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_26, c_103])).
% 2.60/1.41  tff(c_107, plain, (![B_279]: (m1_connsp_2('#skF_5', '#skF_2', B_279) | ~r2_hidden(B_279, '#skF_5') | ~m1_subset_1(B_279, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_42, c_105])).
% 2.60/1.41  tff(c_110, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_6') | ~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_24, c_107])).
% 2.60/1.41  tff(c_113, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_110])).
% 2.60/1.41  tff(c_50, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_7') | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.60/1.41  tff(c_58, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6') | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_50])).
% 2.60/1.41  tff(c_65, plain, (~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(splitLeft, [status(thm)], [c_58])).
% 2.60/1.41  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_160])).
% 2.60/1.41  tff(c_135, plain, (![G_288, A_291, E_289, D_290, B_287, C_286]: (r1_tmap_1(B_287, A_291, C_286, G_288) | ~r1_tmap_1(D_290, A_291, k2_tmap_1(B_287, A_291, C_286, D_290), G_288) | ~m1_connsp_2(E_289, B_287, G_288) | ~r1_tarski(E_289, u1_struct_0(D_290)) | ~m1_subset_1(G_288, u1_struct_0(D_290)) | ~m1_subset_1(G_288, u1_struct_0(B_287)) | ~m1_subset_1(E_289, k1_zfmisc_1(u1_struct_0(B_287))) | ~m1_pre_topc(D_290, B_287) | v2_struct_0(D_290) | ~m1_subset_1(C_286, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_287), u1_struct_0(A_291)))) | ~v1_funct_2(C_286, u1_struct_0(B_287), u1_struct_0(A_291)) | ~v1_funct_1(C_286) | ~l1_pre_topc(B_287) | ~v2_pre_topc(B_287) | v2_struct_0(B_287) | ~l1_pre_topc(A_291) | ~v2_pre_topc(A_291) | v2_struct_0(A_291))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.60/1.41  tff(c_137, plain, (![E_289]: (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | ~m1_connsp_2(E_289, '#skF_2', '#skF_6') | ~r1_tarski(E_289, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | ~m1_subset_1(E_289, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_64, c_135])).
% 2.60/1.41  tff(c_140, plain, (![E_289]: (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | ~m1_connsp_2(E_289, '#skF_2', '#skF_6') | ~r1_tarski(E_289, u1_struct_0('#skF_4')) | ~m1_subset_1(E_289, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_40, c_38, c_36, c_34, c_32, c_28, c_24, c_59, c_137])).
% 2.60/1.41  tff(c_142, plain, (![E_292]: (~m1_connsp_2(E_292, '#skF_2', '#skF_6') | ~r1_tarski(E_292, u1_struct_0('#skF_4')) | ~m1_subset_1(E_292, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_42, c_30, c_65, c_140])).
% 2.60/1.41  tff(c_145, plain, (~m1_connsp_2('#skF_5', '#skF_2', '#skF_6') | ~r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_142])).
% 2.60/1.41  tff(c_149, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_113, c_145])).
% 2.60/1.41  tff(c_150, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(splitRight, [status(thm)], [c_58])).
% 2.60/1.41  tff(c_153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_150])).
% 2.60/1.41  tff(c_154, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(splitRight, [status(thm)], [c_57])).
% 2.60/1.41  tff(c_159, plain, (![C_293, A_294]: (~m1_subset_1(C_293, k1_zfmisc_1(u1_struct_0(A_294))) | ~l1_pre_topc(A_294) | ~v2_pre_topc(A_294))), inference(splitLeft, [status(thm)], [c_4])).
% 2.60/1.41  tff(c_162, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_159])).
% 2.60/1.41  tff(c_166, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_162])).
% 2.60/1.41  tff(c_168, plain, (![B_295, D_296]: (k1_tops_1(B_295, D_296)=D_296 | ~v3_pre_topc(D_296, B_295) | ~m1_subset_1(D_296, k1_zfmisc_1(u1_struct_0(B_295))) | ~l1_pre_topc(B_295))), inference(splitRight, [status(thm)], [c_4])).
% 2.60/1.41  tff(c_171, plain, (k1_tops_1('#skF_2', '#skF_5')='#skF_5' | ~v3_pre_topc('#skF_5', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_168])).
% 2.60/1.41  tff(c_174, plain, (k1_tops_1('#skF_2', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_20, c_171])).
% 2.60/1.41  tff(c_209, plain, (![C_305, A_306, B_307]: (m1_connsp_2(C_305, A_306, B_307) | ~r2_hidden(B_307, k1_tops_1(A_306, C_305)) | ~m1_subset_1(C_305, k1_zfmisc_1(u1_struct_0(A_306))) | ~m1_subset_1(B_307, u1_struct_0(A_306)) | ~l1_pre_topc(A_306) | ~v2_pre_topc(A_306) | v2_struct_0(A_306))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.60/1.41  tff(c_211, plain, (![B_307]: (m1_connsp_2('#skF_5', '#skF_2', B_307) | ~r2_hidden(B_307, '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_307, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_174, c_209])).
% 2.60/1.41  tff(c_213, plain, (![B_307]: (m1_connsp_2('#skF_5', '#skF_2', B_307) | ~r2_hidden(B_307, '#skF_5') | ~m1_subset_1(B_307, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_26, c_211])).
% 2.60/1.41  tff(c_215, plain, (![B_308]: (m1_connsp_2('#skF_5', '#skF_2', B_308) | ~r2_hidden(B_308, '#skF_5') | ~m1_subset_1(B_308, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_42, c_213])).
% 2.60/1.41  tff(c_218, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_6') | ~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_24, c_215])).
% 2.60/1.41  tff(c_221, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_218])).
% 2.60/1.41  tff(c_222, plain, (![D_313, A_314, E_312, G_311, B_310, C_309]: (r1_tmap_1(D_313, A_314, k2_tmap_1(B_310, A_314, C_309, D_313), G_311) | ~r1_tmap_1(B_310, A_314, C_309, G_311) | ~m1_connsp_2(E_312, B_310, G_311) | ~r1_tarski(E_312, u1_struct_0(D_313)) | ~m1_subset_1(G_311, u1_struct_0(D_313)) | ~m1_subset_1(G_311, u1_struct_0(B_310)) | ~m1_subset_1(E_312, k1_zfmisc_1(u1_struct_0(B_310))) | ~m1_pre_topc(D_313, B_310) | v2_struct_0(D_313) | ~m1_subset_1(C_309, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_310), u1_struct_0(A_314)))) | ~v1_funct_2(C_309, u1_struct_0(B_310), u1_struct_0(A_314)) | ~v1_funct_1(C_309) | ~l1_pre_topc(B_310) | ~v2_pre_topc(B_310) | v2_struct_0(B_310) | ~l1_pre_topc(A_314) | ~v2_pre_topc(A_314) | v2_struct_0(A_314))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.60/1.41  tff(c_224, plain, (![D_313, A_314, C_309]: (r1_tmap_1(D_313, A_314, k2_tmap_1('#skF_2', A_314, C_309, D_313), '#skF_6') | ~r1_tmap_1('#skF_2', A_314, C_309, '#skF_6') | ~r1_tarski('#skF_5', u1_struct_0(D_313)) | ~m1_subset_1('#skF_6', u1_struct_0(D_313)) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc(D_313, '#skF_2') | v2_struct_0(D_313) | ~m1_subset_1(C_309, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(A_314)))) | ~v1_funct_2(C_309, u1_struct_0('#skF_2'), u1_struct_0(A_314)) | ~v1_funct_1(C_309) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_314) | ~v2_pre_topc(A_314) | v2_struct_0(A_314))), inference(resolution, [status(thm)], [c_221, c_222])).
% 2.60/1.41  tff(c_227, plain, (![D_313, A_314, C_309]: (r1_tmap_1(D_313, A_314, k2_tmap_1('#skF_2', A_314, C_309, D_313), '#skF_6') | ~r1_tmap_1('#skF_2', A_314, C_309, '#skF_6') | ~r1_tarski('#skF_5', u1_struct_0(D_313)) | ~m1_subset_1('#skF_6', u1_struct_0(D_313)) | ~m1_pre_topc(D_313, '#skF_2') | v2_struct_0(D_313) | ~m1_subset_1(C_309, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(A_314)))) | ~v1_funct_2(C_309, u1_struct_0('#skF_2'), u1_struct_0(A_314)) | ~v1_funct_1(C_309) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_314) | ~v2_pre_topc(A_314) | v2_struct_0(A_314))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_26, c_24, c_224])).
% 2.60/1.41  tff(c_229, plain, (![D_315, A_316, C_317]: (r1_tmap_1(D_315, A_316, k2_tmap_1('#skF_2', A_316, C_317, D_315), '#skF_6') | ~r1_tmap_1('#skF_2', A_316, C_317, '#skF_6') | ~r1_tarski('#skF_5', u1_struct_0(D_315)) | ~m1_subset_1('#skF_6', u1_struct_0(D_315)) | ~m1_pre_topc(D_315, '#skF_2') | v2_struct_0(D_315) | ~m1_subset_1(C_317, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(A_316)))) | ~v1_funct_2(C_317, u1_struct_0('#skF_2'), u1_struct_0(A_316)) | ~v1_funct_1(C_317) | ~l1_pre_topc(A_316) | ~v2_pre_topc(A_316) | v2_struct_0(A_316))), inference(negUnitSimplification, [status(thm)], [c_42, c_227])).
% 2.60/1.41  tff(c_231, plain, (![D_315]: (r1_tmap_1(D_315, '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', D_315), '#skF_6') | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | ~r1_tarski('#skF_5', u1_struct_0(D_315)) | ~m1_subset_1('#skF_6', u1_struct_0(D_315)) | ~m1_pre_topc(D_315, '#skF_2') | v2_struct_0(D_315) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_229])).
% 2.60/1.41  tff(c_234, plain, (![D_315]: (r1_tmap_1(D_315, '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', D_315), '#skF_6') | ~r1_tarski('#skF_5', u1_struct_0(D_315)) | ~m1_subset_1('#skF_6', u1_struct_0(D_315)) | ~m1_pre_topc(D_315, '#skF_2') | v2_struct_0(D_315) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_36, c_34, c_154, c_231])).
% 2.60/1.41  tff(c_236, plain, (![D_318]: (r1_tmap_1(D_318, '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', D_318), '#skF_6') | ~r1_tarski('#skF_5', u1_struct_0(D_318)) | ~m1_subset_1('#skF_6', u1_struct_0(D_318)) | ~m1_pre_topc(D_318, '#skF_2') | v2_struct_0(D_318))), inference(negUnitSimplification, [status(thm)], [c_48, c_234])).
% 2.60/1.41  tff(c_155, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(splitRight, [status(thm)], [c_57])).
% 2.60/1.41  tff(c_239, plain, (~r1_tarski('#skF_5', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_236, c_155])).
% 2.60/1.41  tff(c_242, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_59, c_16, c_239])).
% 2.60/1.41  tff(c_244, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_242])).
% 2.60/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.41  
% 2.60/1.41  Inference rules
% 2.60/1.41  ----------------------
% 2.60/1.41  #Ref     : 0
% 2.60/1.41  #Sup     : 29
% 2.60/1.41  #Fact    : 0
% 2.60/1.41  #Define  : 0
% 2.60/1.41  #Split   : 6
% 2.60/1.41  #Chain   : 0
% 2.60/1.41  #Close   : 0
% 2.60/1.41  
% 2.60/1.41  Ordering : KBO
% 2.60/1.41  
% 2.60/1.41  Simplification rules
% 2.60/1.41  ----------------------
% 2.60/1.41  #Subsume      : 3
% 2.60/1.41  #Demod        : 64
% 2.60/1.41  #Tautology    : 14
% 2.60/1.41  #SimpNegUnit  : 8
% 2.60/1.41  #BackRed      : 0
% 2.60/1.41  
% 2.60/1.41  #Partial instantiations: 0
% 2.60/1.41  #Strategies tried      : 1
% 2.60/1.41  
% 2.60/1.41  Timing (in seconds)
% 2.60/1.41  ----------------------
% 2.60/1.41  Preprocessing        : 0.38
% 2.60/1.41  Parsing              : 0.20
% 2.60/1.41  CNF conversion       : 0.05
% 2.60/1.41  Main loop            : 0.22
% 2.60/1.41  Inferencing          : 0.08
% 2.60/1.41  Reduction            : 0.07
% 2.60/1.41  Demodulation         : 0.05
% 2.60/1.41  BG Simplification    : 0.02
% 2.60/1.41  Subsumption          : 0.03
% 2.60/1.41  Abstraction          : 0.01
% 2.60/1.41  MUC search           : 0.00
% 2.60/1.41  Cooper               : 0.00
% 2.60/1.41  Total                : 0.64
% 2.60/1.41  Index Insertion      : 0.00
% 2.60/1.41  Index Deletion       : 0.00
% 2.60/1.41  Index Matching       : 0.00
% 2.60/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
