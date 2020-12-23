%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:03 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 189 expanded)
%              Number of leaves         :   29 (  88 expanded)
%              Depth                    :   15
%              Number of atoms          :  272 (1491 expanded)
%              Number of equality atoms :    3 (  68 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_141,negated_conjecture,(
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

tff(f_44,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( v3_pre_topc(B,A)
                  & r2_hidden(C,B) )
               => m1_connsp_2(B,A,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

tff(f_91,axiom,(
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

tff(c_24,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_22,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_8,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_16,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_53,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_16])).

tff(c_10,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_40,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_30,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_28,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_44,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_7')
    | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_52,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6')
    | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_44])).

tff(c_58,plain,(
    ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_14,plain,(
    v3_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_12,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_20,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_34,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_32,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_18,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_60,plain,(
    ! [B_255,A_256,C_257] :
      ( m1_connsp_2(B_255,A_256,C_257)
      | ~ r2_hidden(C_257,B_255)
      | ~ v3_pre_topc(B_255,A_256)
      | ~ m1_subset_1(C_257,u1_struct_0(A_256))
      | ~ m1_subset_1(B_255,k1_zfmisc_1(u1_struct_0(A_256)))
      | ~ l1_pre_topc(A_256)
      | ~ v2_pre_topc(A_256)
      | v2_struct_0(A_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_62,plain,(
    ! [B_255] :
      ( m1_connsp_2(B_255,'#skF_2','#skF_6')
      | ~ r2_hidden('#skF_6',B_255)
      | ~ v3_pre_topc(B_255,'#skF_2')
      | ~ m1_subset_1(B_255,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_60])).

tff(c_67,plain,(
    ! [B_255] :
      ( m1_connsp_2(B_255,'#skF_2','#skF_6')
      | ~ r2_hidden('#skF_6',B_255)
      | ~ v3_pre_topc(B_255,'#skF_2')
      | ~ m1_subset_1(B_255,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_62])).

tff(c_72,plain,(
    ! [B_258] :
      ( m1_connsp_2(B_258,'#skF_2','#skF_6')
      | ~ r2_hidden('#skF_6',B_258)
      | ~ v3_pre_topc(B_258,'#skF_2')
      | ~ m1_subset_1(B_258,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_67])).

tff(c_75,plain,
    ( m1_connsp_2('#skF_5','#skF_2','#skF_6')
    | ~ r2_hidden('#skF_6','#skF_5')
    | ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_72])).

tff(c_78,plain,(
    m1_connsp_2('#skF_5','#skF_2','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_75])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_50,plain,
    ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
    | r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_51,plain,
    ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
    | r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_50])).

tff(c_59,plain,(
    r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_51])).

tff(c_79,plain,(
    ! [E_262,A_261,D_259,C_260,B_263,G_264] :
      ( r1_tmap_1(B_263,A_261,C_260,G_264)
      | ~ r1_tmap_1(D_259,A_261,k2_tmap_1(B_263,A_261,C_260,D_259),G_264)
      | ~ m1_connsp_2(E_262,B_263,G_264)
      | ~ r1_tarski(E_262,u1_struct_0(D_259))
      | ~ m1_subset_1(G_264,u1_struct_0(D_259))
      | ~ m1_subset_1(G_264,u1_struct_0(B_263))
      | ~ m1_subset_1(E_262,k1_zfmisc_1(u1_struct_0(B_263)))
      | ~ m1_pre_topc(D_259,B_263)
      | v2_struct_0(D_259)
      | ~ m1_subset_1(C_260,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_263),u1_struct_0(A_261))))
      | ~ v1_funct_2(C_260,u1_struct_0(B_263),u1_struct_0(A_261))
      | ~ v1_funct_1(C_260)
      | ~ l1_pre_topc(B_263)
      | ~ v2_pre_topc(B_263)
      | v2_struct_0(B_263)
      | ~ l1_pre_topc(A_261)
      | ~ v2_pre_topc(A_261)
      | v2_struct_0(A_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_81,plain,(
    ! [E_262] :
      ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
      | ~ m1_connsp_2(E_262,'#skF_2','#skF_6')
      | ~ r1_tarski(E_262,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_262,k1_zfmisc_1(u1_struct_0('#skF_2')))
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
    inference(resolution,[status(thm)],[c_59,c_79])).

tff(c_84,plain,(
    ! [E_262] :
      ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
      | ~ m1_connsp_2(E_262,'#skF_2','#skF_6')
      | ~ r1_tarski(E_262,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_262,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_34,c_32,c_30,c_28,c_26,c_22,c_18,c_53,c_81])).

tff(c_86,plain,(
    ! [E_265] :
      ( ~ m1_connsp_2(E_265,'#skF_2','#skF_6')
      | ~ r1_tarski(E_265,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_265,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_36,c_24,c_58,c_84])).

tff(c_89,plain,
    ( ~ m1_connsp_2('#skF_5','#skF_2','#skF_6')
    | ~ r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_20,c_86])).

tff(c_93,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_78,c_89])).

tff(c_94,plain,(
    r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(splitRight,[status(thm)],[c_51])).

tff(c_96,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_94])).

tff(c_98,plain,(
    r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_104,plain,(
    ! [B_266,A_267,C_268] :
      ( m1_connsp_2(B_266,A_267,C_268)
      | ~ r2_hidden(C_268,B_266)
      | ~ v3_pre_topc(B_266,A_267)
      | ~ m1_subset_1(C_268,u1_struct_0(A_267))
      | ~ m1_subset_1(B_266,k1_zfmisc_1(u1_struct_0(A_267)))
      | ~ l1_pre_topc(A_267)
      | ~ v2_pre_topc(A_267)
      | v2_struct_0(A_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_106,plain,(
    ! [B_266] :
      ( m1_connsp_2(B_266,'#skF_2','#skF_6')
      | ~ r2_hidden('#skF_6',B_266)
      | ~ v3_pre_topc(B_266,'#skF_2')
      | ~ m1_subset_1(B_266,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_104])).

tff(c_111,plain,(
    ! [B_266] :
      ( m1_connsp_2(B_266,'#skF_2','#skF_6')
      | ~ r2_hidden('#skF_6',B_266)
      | ~ v3_pre_topc(B_266,'#skF_2')
      | ~ m1_subset_1(B_266,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_106])).

tff(c_116,plain,(
    ! [B_269] :
      ( m1_connsp_2(B_269,'#skF_2','#skF_6')
      | ~ r2_hidden('#skF_6',B_269)
      | ~ v3_pre_topc(B_269,'#skF_2')
      | ~ m1_subset_1(B_269,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_111])).

tff(c_119,plain,
    ( m1_connsp_2('#skF_5','#skF_2','#skF_6')
    | ~ r2_hidden('#skF_6','#skF_5')
    | ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_116])).

tff(c_122,plain,(
    m1_connsp_2('#skF_5','#skF_2','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_119])).

tff(c_125,plain,(
    ! [G_281,C_277,A_278,B_280,D_276,E_279] :
      ( r1_tmap_1(D_276,A_278,k2_tmap_1(B_280,A_278,C_277,D_276),G_281)
      | ~ r1_tmap_1(B_280,A_278,C_277,G_281)
      | ~ m1_connsp_2(E_279,B_280,G_281)
      | ~ r1_tarski(E_279,u1_struct_0(D_276))
      | ~ m1_subset_1(G_281,u1_struct_0(D_276))
      | ~ m1_subset_1(G_281,u1_struct_0(B_280))
      | ~ m1_subset_1(E_279,k1_zfmisc_1(u1_struct_0(B_280)))
      | ~ m1_pre_topc(D_276,B_280)
      | v2_struct_0(D_276)
      | ~ m1_subset_1(C_277,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_280),u1_struct_0(A_278))))
      | ~ v1_funct_2(C_277,u1_struct_0(B_280),u1_struct_0(A_278))
      | ~ v1_funct_1(C_277)
      | ~ l1_pre_topc(B_280)
      | ~ v2_pre_topc(B_280)
      | v2_struct_0(B_280)
      | ~ l1_pre_topc(A_278)
      | ~ v2_pre_topc(A_278)
      | v2_struct_0(A_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_127,plain,(
    ! [D_276,A_278,C_277] :
      ( r1_tmap_1(D_276,A_278,k2_tmap_1('#skF_2',A_278,C_277,D_276),'#skF_6')
      | ~ r1_tmap_1('#skF_2',A_278,C_277,'#skF_6')
      | ~ r1_tarski('#skF_5',u1_struct_0(D_276))
      | ~ m1_subset_1('#skF_6',u1_struct_0(D_276))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_pre_topc(D_276,'#skF_2')
      | v2_struct_0(D_276)
      | ~ m1_subset_1(C_277,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(A_278))))
      | ~ v1_funct_2(C_277,u1_struct_0('#skF_2'),u1_struct_0(A_278))
      | ~ v1_funct_1(C_277)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_278)
      | ~ v2_pre_topc(A_278)
      | v2_struct_0(A_278) ) ),
    inference(resolution,[status(thm)],[c_122,c_125])).

tff(c_130,plain,(
    ! [D_276,A_278,C_277] :
      ( r1_tmap_1(D_276,A_278,k2_tmap_1('#skF_2',A_278,C_277,D_276),'#skF_6')
      | ~ r1_tmap_1('#skF_2',A_278,C_277,'#skF_6')
      | ~ r1_tarski('#skF_5',u1_struct_0(D_276))
      | ~ m1_subset_1('#skF_6',u1_struct_0(D_276))
      | ~ m1_pre_topc(D_276,'#skF_2')
      | v2_struct_0(D_276)
      | ~ m1_subset_1(C_277,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(A_278))))
      | ~ v1_funct_2(C_277,u1_struct_0('#skF_2'),u1_struct_0(A_278))
      | ~ v1_funct_1(C_277)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_278)
      | ~ v2_pre_topc(A_278)
      | v2_struct_0(A_278) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_20,c_18,c_127])).

tff(c_132,plain,(
    ! [D_282,A_283,C_284] :
      ( r1_tmap_1(D_282,A_283,k2_tmap_1('#skF_2',A_283,C_284,D_282),'#skF_6')
      | ~ r1_tmap_1('#skF_2',A_283,C_284,'#skF_6')
      | ~ r1_tarski('#skF_5',u1_struct_0(D_282))
      | ~ m1_subset_1('#skF_6',u1_struct_0(D_282))
      | ~ m1_pre_topc(D_282,'#skF_2')
      | v2_struct_0(D_282)
      | ~ m1_subset_1(C_284,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(A_283))))
      | ~ v1_funct_2(C_284,u1_struct_0('#skF_2'),u1_struct_0(A_283))
      | ~ v1_funct_1(C_284)
      | ~ l1_pre_topc(A_283)
      | ~ v2_pre_topc(A_283)
      | v2_struct_0(A_283) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_130])).

tff(c_134,plain,(
    ! [D_282] :
      ( r1_tmap_1(D_282,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_282),'#skF_6')
      | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
      | ~ r1_tarski('#skF_5',u1_struct_0(D_282))
      | ~ m1_subset_1('#skF_6',u1_struct_0(D_282))
      | ~ m1_pre_topc(D_282,'#skF_2')
      | v2_struct_0(D_282)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_132])).

tff(c_137,plain,(
    ! [D_282] :
      ( r1_tmap_1(D_282,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_282),'#skF_6')
      | ~ r1_tarski('#skF_5',u1_struct_0(D_282))
      | ~ m1_subset_1('#skF_6',u1_struct_0(D_282))
      | ~ m1_pre_topc(D_282,'#skF_2')
      | v2_struct_0(D_282)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_30,c_28,c_98,c_134])).

tff(c_139,plain,(
    ! [D_285] :
      ( r1_tmap_1(D_285,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_285),'#skF_6')
      | ~ r1_tarski('#skF_5',u1_struct_0(D_285))
      | ~ m1_subset_1('#skF_6',u1_struct_0(D_285))
      | ~ m1_pre_topc(D_285,'#skF_2')
      | v2_struct_0(D_285) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_137])).

tff(c_97,plain,(
    ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_144,plain,
    ( ~ r1_tarski('#skF_5',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_139,c_97])).

tff(c_151,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_53,c_10,c_144])).

tff(c_153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_151])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:24:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.44/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.34  
% 2.44/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.34  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.44/1.34  
% 2.44/1.34  %Foreground sorts:
% 2.44/1.34  
% 2.44/1.34  
% 2.44/1.34  %Background operators:
% 2.44/1.34  
% 2.44/1.34  
% 2.44/1.34  %Foreground operators:
% 2.44/1.34  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.44/1.34  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 2.44/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.44/1.34  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.44/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.44/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.44/1.34  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 2.44/1.34  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.44/1.34  tff('#skF_7', type, '#skF_7': $i).
% 2.44/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.44/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.44/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.44/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.44/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.44/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.44/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.44/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.44/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.44/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.44/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.44/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.44/1.34  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.44/1.34  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.44/1.34  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 2.44/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.44/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.44/1.34  
% 2.44/1.36  tff(f_141, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((v3_pre_topc(E, B) & r2_hidden(F, E)) & r1_tarski(E, u1_struct_0(D))) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tmap_1)).
% 2.44/1.36  tff(f_44, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 2.44/1.36  tff(f_91, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tmap_1)).
% 2.44/1.36  tff(c_24, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.44/1.36  tff(c_22, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.44/1.36  tff(c_8, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.44/1.36  tff(c_16, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.44/1.36  tff(c_53, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_16])).
% 2.44/1.36  tff(c_10, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.44/1.36  tff(c_42, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.44/1.36  tff(c_40, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.44/1.36  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.44/1.36  tff(c_30, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.44/1.36  tff(c_28, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.44/1.36  tff(c_44, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_7') | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.44/1.36  tff(c_52, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6') | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_44])).
% 2.44/1.36  tff(c_58, plain, (~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(splitLeft, [status(thm)], [c_52])).
% 2.44/1.36  tff(c_14, plain, (v3_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.44/1.36  tff(c_12, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.44/1.36  tff(c_20, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.44/1.36  tff(c_36, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.44/1.36  tff(c_34, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.44/1.36  tff(c_32, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.44/1.36  tff(c_18, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.44/1.36  tff(c_60, plain, (![B_255, A_256, C_257]: (m1_connsp_2(B_255, A_256, C_257) | ~r2_hidden(C_257, B_255) | ~v3_pre_topc(B_255, A_256) | ~m1_subset_1(C_257, u1_struct_0(A_256)) | ~m1_subset_1(B_255, k1_zfmisc_1(u1_struct_0(A_256))) | ~l1_pre_topc(A_256) | ~v2_pre_topc(A_256) | v2_struct_0(A_256))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.44/1.36  tff(c_62, plain, (![B_255]: (m1_connsp_2(B_255, '#skF_2', '#skF_6') | ~r2_hidden('#skF_6', B_255) | ~v3_pre_topc(B_255, '#skF_2') | ~m1_subset_1(B_255, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_18, c_60])).
% 2.44/1.36  tff(c_67, plain, (![B_255]: (m1_connsp_2(B_255, '#skF_2', '#skF_6') | ~r2_hidden('#skF_6', B_255) | ~v3_pre_topc(B_255, '#skF_2') | ~m1_subset_1(B_255, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_62])).
% 2.44/1.36  tff(c_72, plain, (![B_258]: (m1_connsp_2(B_258, '#skF_2', '#skF_6') | ~r2_hidden('#skF_6', B_258) | ~v3_pre_topc(B_258, '#skF_2') | ~m1_subset_1(B_258, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_36, c_67])).
% 2.44/1.36  tff(c_75, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_6') | ~r2_hidden('#skF_6', '#skF_5') | ~v3_pre_topc('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_20, c_72])).
% 2.44/1.36  tff(c_78, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_75])).
% 2.44/1.36  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.44/1.36  tff(c_50, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.44/1.36  tff(c_51, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_50])).
% 2.44/1.36  tff(c_59, plain, (r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_51])).
% 2.44/1.36  tff(c_79, plain, (![E_262, A_261, D_259, C_260, B_263, G_264]: (r1_tmap_1(B_263, A_261, C_260, G_264) | ~r1_tmap_1(D_259, A_261, k2_tmap_1(B_263, A_261, C_260, D_259), G_264) | ~m1_connsp_2(E_262, B_263, G_264) | ~r1_tarski(E_262, u1_struct_0(D_259)) | ~m1_subset_1(G_264, u1_struct_0(D_259)) | ~m1_subset_1(G_264, u1_struct_0(B_263)) | ~m1_subset_1(E_262, k1_zfmisc_1(u1_struct_0(B_263))) | ~m1_pre_topc(D_259, B_263) | v2_struct_0(D_259) | ~m1_subset_1(C_260, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_263), u1_struct_0(A_261)))) | ~v1_funct_2(C_260, u1_struct_0(B_263), u1_struct_0(A_261)) | ~v1_funct_1(C_260) | ~l1_pre_topc(B_263) | ~v2_pre_topc(B_263) | v2_struct_0(B_263) | ~l1_pre_topc(A_261) | ~v2_pre_topc(A_261) | v2_struct_0(A_261))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.44/1.36  tff(c_81, plain, (![E_262]: (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | ~m1_connsp_2(E_262, '#skF_2', '#skF_6') | ~r1_tarski(E_262, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | ~m1_subset_1(E_262, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_59, c_79])).
% 2.44/1.36  tff(c_84, plain, (![E_262]: (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | ~m1_connsp_2(E_262, '#skF_2', '#skF_6') | ~r1_tarski(E_262, u1_struct_0('#skF_4')) | ~m1_subset_1(E_262, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_34, c_32, c_30, c_28, c_26, c_22, c_18, c_53, c_81])).
% 2.44/1.36  tff(c_86, plain, (![E_265]: (~m1_connsp_2(E_265, '#skF_2', '#skF_6') | ~r1_tarski(E_265, u1_struct_0('#skF_4')) | ~m1_subset_1(E_265, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_36, c_24, c_58, c_84])).
% 2.44/1.36  tff(c_89, plain, (~m1_connsp_2('#skF_5', '#skF_2', '#skF_6') | ~r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_20, c_86])).
% 2.44/1.36  tff(c_93, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_78, c_89])).
% 2.44/1.36  tff(c_94, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(splitRight, [status(thm)], [c_51])).
% 2.44/1.36  tff(c_96, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_94])).
% 2.44/1.36  tff(c_98, plain, (r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6')), inference(splitRight, [status(thm)], [c_52])).
% 2.44/1.36  tff(c_104, plain, (![B_266, A_267, C_268]: (m1_connsp_2(B_266, A_267, C_268) | ~r2_hidden(C_268, B_266) | ~v3_pre_topc(B_266, A_267) | ~m1_subset_1(C_268, u1_struct_0(A_267)) | ~m1_subset_1(B_266, k1_zfmisc_1(u1_struct_0(A_267))) | ~l1_pre_topc(A_267) | ~v2_pre_topc(A_267) | v2_struct_0(A_267))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.44/1.36  tff(c_106, plain, (![B_266]: (m1_connsp_2(B_266, '#skF_2', '#skF_6') | ~r2_hidden('#skF_6', B_266) | ~v3_pre_topc(B_266, '#skF_2') | ~m1_subset_1(B_266, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_18, c_104])).
% 2.44/1.36  tff(c_111, plain, (![B_266]: (m1_connsp_2(B_266, '#skF_2', '#skF_6') | ~r2_hidden('#skF_6', B_266) | ~v3_pre_topc(B_266, '#skF_2') | ~m1_subset_1(B_266, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_106])).
% 2.44/1.36  tff(c_116, plain, (![B_269]: (m1_connsp_2(B_269, '#skF_2', '#skF_6') | ~r2_hidden('#skF_6', B_269) | ~v3_pre_topc(B_269, '#skF_2') | ~m1_subset_1(B_269, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_36, c_111])).
% 2.44/1.36  tff(c_119, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_6') | ~r2_hidden('#skF_6', '#skF_5') | ~v3_pre_topc('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_20, c_116])).
% 2.44/1.36  tff(c_122, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_119])).
% 2.44/1.36  tff(c_125, plain, (![G_281, C_277, A_278, B_280, D_276, E_279]: (r1_tmap_1(D_276, A_278, k2_tmap_1(B_280, A_278, C_277, D_276), G_281) | ~r1_tmap_1(B_280, A_278, C_277, G_281) | ~m1_connsp_2(E_279, B_280, G_281) | ~r1_tarski(E_279, u1_struct_0(D_276)) | ~m1_subset_1(G_281, u1_struct_0(D_276)) | ~m1_subset_1(G_281, u1_struct_0(B_280)) | ~m1_subset_1(E_279, k1_zfmisc_1(u1_struct_0(B_280))) | ~m1_pre_topc(D_276, B_280) | v2_struct_0(D_276) | ~m1_subset_1(C_277, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_280), u1_struct_0(A_278)))) | ~v1_funct_2(C_277, u1_struct_0(B_280), u1_struct_0(A_278)) | ~v1_funct_1(C_277) | ~l1_pre_topc(B_280) | ~v2_pre_topc(B_280) | v2_struct_0(B_280) | ~l1_pre_topc(A_278) | ~v2_pre_topc(A_278) | v2_struct_0(A_278))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.44/1.36  tff(c_127, plain, (![D_276, A_278, C_277]: (r1_tmap_1(D_276, A_278, k2_tmap_1('#skF_2', A_278, C_277, D_276), '#skF_6') | ~r1_tmap_1('#skF_2', A_278, C_277, '#skF_6') | ~r1_tarski('#skF_5', u1_struct_0(D_276)) | ~m1_subset_1('#skF_6', u1_struct_0(D_276)) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc(D_276, '#skF_2') | v2_struct_0(D_276) | ~m1_subset_1(C_277, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(A_278)))) | ~v1_funct_2(C_277, u1_struct_0('#skF_2'), u1_struct_0(A_278)) | ~v1_funct_1(C_277) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_278) | ~v2_pre_topc(A_278) | v2_struct_0(A_278))), inference(resolution, [status(thm)], [c_122, c_125])).
% 2.44/1.36  tff(c_130, plain, (![D_276, A_278, C_277]: (r1_tmap_1(D_276, A_278, k2_tmap_1('#skF_2', A_278, C_277, D_276), '#skF_6') | ~r1_tmap_1('#skF_2', A_278, C_277, '#skF_6') | ~r1_tarski('#skF_5', u1_struct_0(D_276)) | ~m1_subset_1('#skF_6', u1_struct_0(D_276)) | ~m1_pre_topc(D_276, '#skF_2') | v2_struct_0(D_276) | ~m1_subset_1(C_277, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(A_278)))) | ~v1_funct_2(C_277, u1_struct_0('#skF_2'), u1_struct_0(A_278)) | ~v1_funct_1(C_277) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_278) | ~v2_pre_topc(A_278) | v2_struct_0(A_278))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_20, c_18, c_127])).
% 2.44/1.36  tff(c_132, plain, (![D_282, A_283, C_284]: (r1_tmap_1(D_282, A_283, k2_tmap_1('#skF_2', A_283, C_284, D_282), '#skF_6') | ~r1_tmap_1('#skF_2', A_283, C_284, '#skF_6') | ~r1_tarski('#skF_5', u1_struct_0(D_282)) | ~m1_subset_1('#skF_6', u1_struct_0(D_282)) | ~m1_pre_topc(D_282, '#skF_2') | v2_struct_0(D_282) | ~m1_subset_1(C_284, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(A_283)))) | ~v1_funct_2(C_284, u1_struct_0('#skF_2'), u1_struct_0(A_283)) | ~v1_funct_1(C_284) | ~l1_pre_topc(A_283) | ~v2_pre_topc(A_283) | v2_struct_0(A_283))), inference(negUnitSimplification, [status(thm)], [c_36, c_130])).
% 2.44/1.36  tff(c_134, plain, (![D_282]: (r1_tmap_1(D_282, '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', D_282), '#skF_6') | ~r1_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_6') | ~r1_tarski('#skF_5', u1_struct_0(D_282)) | ~m1_subset_1('#skF_6', u1_struct_0(D_282)) | ~m1_pre_topc(D_282, '#skF_2') | v2_struct_0(D_282) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_132])).
% 2.44/1.36  tff(c_137, plain, (![D_282]: (r1_tmap_1(D_282, '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', D_282), '#skF_6') | ~r1_tarski('#skF_5', u1_struct_0(D_282)) | ~m1_subset_1('#skF_6', u1_struct_0(D_282)) | ~m1_pre_topc(D_282, '#skF_2') | v2_struct_0(D_282) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_30, c_28, c_98, c_134])).
% 2.44/1.36  tff(c_139, plain, (![D_285]: (r1_tmap_1(D_285, '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', D_285), '#skF_6') | ~r1_tarski('#skF_5', u1_struct_0(D_285)) | ~m1_subset_1('#skF_6', u1_struct_0(D_285)) | ~m1_pre_topc(D_285, '#skF_2') | v2_struct_0(D_285))), inference(negUnitSimplification, [status(thm)], [c_42, c_137])).
% 2.44/1.36  tff(c_97, plain, (~r1_tmap_1('#skF_4', '#skF_1', k2_tmap_1('#skF_2', '#skF_1', '#skF_3', '#skF_4'), '#skF_6')), inference(splitRight, [status(thm)], [c_52])).
% 2.44/1.36  tff(c_144, plain, (~r1_tarski('#skF_5', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_139, c_97])).
% 2.44/1.36  tff(c_151, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_53, c_10, c_144])).
% 2.44/1.36  tff(c_153, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_151])).
% 2.44/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.36  
% 2.44/1.36  Inference rules
% 2.44/1.36  ----------------------
% 2.44/1.36  #Ref     : 0
% 2.44/1.36  #Sup     : 14
% 2.44/1.36  #Fact    : 0
% 2.44/1.36  #Define  : 0
% 2.44/1.36  #Split   : 4
% 2.44/1.36  #Chain   : 0
% 2.44/1.36  #Close   : 0
% 2.44/1.36  
% 2.44/1.36  Ordering : KBO
% 2.44/1.36  
% 2.44/1.36  Simplification rules
% 2.44/1.36  ----------------------
% 2.44/1.36  #Subsume      : 1
% 2.44/1.36  #Demod        : 45
% 2.44/1.36  #Tautology    : 6
% 2.44/1.36  #SimpNegUnit  : 11
% 2.44/1.36  #BackRed      : 0
% 2.44/1.36  
% 2.44/1.36  #Partial instantiations: 0
% 2.44/1.36  #Strategies tried      : 1
% 2.44/1.36  
% 2.44/1.36  Timing (in seconds)
% 2.44/1.36  ----------------------
% 2.69/1.37  Preprocessing        : 0.35
% 2.69/1.37  Parsing              : 0.18
% 2.69/1.37  CNF conversion       : 0.05
% 2.69/1.37  Main loop            : 0.21
% 2.69/1.37  Inferencing          : 0.07
% 2.69/1.37  Reduction            : 0.07
% 2.69/1.37  Demodulation         : 0.05
% 2.69/1.37  BG Simplification    : 0.01
% 2.69/1.37  Subsumption          : 0.03
% 2.69/1.37  Abstraction          : 0.01
% 2.69/1.37  MUC search           : 0.00
% 2.69/1.37  Cooper               : 0.00
% 2.69/1.37  Total                : 0.59
% 2.69/1.37  Index Insertion      : 0.00
% 2.69/1.37  Index Deletion       : 0.00
% 2.69/1.37  Index Matching       : 0.00
% 2.69/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
