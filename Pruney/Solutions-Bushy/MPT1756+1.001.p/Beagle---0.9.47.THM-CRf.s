%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1756+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:21 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 161 expanded)
%              Number of leaves         :   30 (  78 expanded)
%              Depth                    :    8
%              Number of atoms          :  222 (1225 expanded)
%              Number of equality atoms :    4 (  59 expanded)
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

tff(f_180,negated_conjecture,(
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

tff(f_43,axiom,(
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

tff(f_130,axiom,(
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

tff(f_83,axiom,(
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

tff(c_26,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_24,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_20,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_10,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_18,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_55,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_18])).

tff(c_46,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_7')
    | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_54,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6')
    | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_46])).

tff(c_60,plain,(
    ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_12,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_16,plain,(
    v3_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_14,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_22,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_36,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_34,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_62,plain,(
    ! [B_318,A_319,C_320] :
      ( m1_connsp_2(B_318,A_319,C_320)
      | ~ r2_hidden(C_320,B_318)
      | ~ v3_pre_topc(B_318,A_319)
      | ~ m1_subset_1(C_320,u1_struct_0(A_319))
      | ~ m1_subset_1(B_318,k1_zfmisc_1(u1_struct_0(A_319)))
      | ~ l1_pre_topc(A_319)
      | ~ v2_pre_topc(A_319)
      | v2_struct_0(A_319) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_64,plain,(
    ! [B_318] :
      ( m1_connsp_2(B_318,'#skF_2','#skF_6')
      | ~ r2_hidden('#skF_6',B_318)
      | ~ v3_pre_topc(B_318,'#skF_2')
      | ~ m1_subset_1(B_318,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_20,c_62])).

tff(c_69,plain,(
    ! [B_318] :
      ( m1_connsp_2(B_318,'#skF_2','#skF_6')
      | ~ r2_hidden('#skF_6',B_318)
      | ~ v3_pre_topc(B_318,'#skF_2')
      | ~ m1_subset_1(B_318,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_64])).

tff(c_74,plain,(
    ! [B_321] :
      ( m1_connsp_2(B_321,'#skF_2','#skF_6')
      | ~ r2_hidden('#skF_6',B_321)
      | ~ v3_pre_topc(B_321,'#skF_2')
      | ~ m1_subset_1(B_321,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_69])).

tff(c_77,plain,
    ( m1_connsp_2('#skF_5','#skF_2','#skF_6')
    | ~ r2_hidden('#skF_6','#skF_5')
    | ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_74])).

tff(c_80,plain,(
    m1_connsp_2('#skF_5','#skF_2','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_77])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_30,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_52,plain,
    ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
    | r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_53,plain,
    ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
    | r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_52])).

tff(c_61,plain,(
    r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_53])).

tff(c_90,plain,(
    ! [B_330,C_329,A_333,G_334,D_331,E_332] :
      ( r1_tmap_1(B_330,A_333,C_329,G_334)
      | ~ r1_tmap_1(D_331,A_333,k2_tmap_1(B_330,A_333,C_329,D_331),G_334)
      | ~ m1_connsp_2(E_332,B_330,G_334)
      | ~ r1_tarski(E_332,u1_struct_0(D_331))
      | ~ m1_subset_1(G_334,u1_struct_0(D_331))
      | ~ m1_subset_1(G_334,u1_struct_0(B_330))
      | ~ m1_subset_1(E_332,k1_zfmisc_1(u1_struct_0(B_330)))
      | ~ m1_pre_topc(D_331,B_330)
      | v2_struct_0(D_331)
      | ~ m1_subset_1(C_329,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_330),u1_struct_0(A_333))))
      | ~ v1_funct_2(C_329,u1_struct_0(B_330),u1_struct_0(A_333))
      | ~ v1_funct_1(C_329)
      | ~ l1_pre_topc(B_330)
      | ~ v2_pre_topc(B_330)
      | v2_struct_0(B_330)
      | ~ l1_pre_topc(A_333)
      | ~ v2_pre_topc(A_333)
      | v2_struct_0(A_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_94,plain,(
    ! [E_332] :
      ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
      | ~ m1_connsp_2(E_332,'#skF_2','#skF_6')
      | ~ r1_tarski(E_332,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_332,k1_zfmisc_1(u1_struct_0('#skF_2')))
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
    inference(resolution,[status(thm)],[c_61,c_90])).

tff(c_101,plain,(
    ! [E_332] :
      ( r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
      | ~ m1_connsp_2(E_332,'#skF_2','#skF_6')
      | ~ r1_tarski(E_332,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_332,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_34,c_32,c_30,c_28,c_24,c_20,c_55,c_94])).

tff(c_103,plain,(
    ! [E_335] :
      ( ~ m1_connsp_2(E_335,'#skF_2','#skF_6')
      | ~ r1_tarski(E_335,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_335,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_38,c_26,c_60,c_101])).

tff(c_106,plain,
    ( ~ m1_connsp_2('#skF_5','#skF_2','#skF_6')
    | ~ r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_22,c_103])).

tff(c_110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_80,c_106])).

tff(c_111,plain,(
    r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_113,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_111])).

tff(c_115,plain,(
    r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_138,plain,(
    ! [A_342,F_344,D_343,C_341,B_340] :
      ( r1_tmap_1(D_343,A_342,k2_tmap_1(B_340,A_342,C_341,D_343),F_344)
      | ~ r1_tmap_1(B_340,A_342,C_341,F_344)
      | ~ m1_subset_1(F_344,u1_struct_0(D_343))
      | ~ m1_subset_1(F_344,u1_struct_0(B_340))
      | ~ m1_pre_topc(D_343,B_340)
      | v2_struct_0(D_343)
      | ~ m1_subset_1(C_341,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_340),u1_struct_0(A_342))))
      | ~ v1_funct_2(C_341,u1_struct_0(B_340),u1_struct_0(A_342))
      | ~ v1_funct_1(C_341)
      | ~ l1_pre_topc(B_340)
      | ~ v2_pre_topc(B_340)
      | v2_struct_0(B_340)
      | ~ l1_pre_topc(A_342)
      | ~ v2_pre_topc(A_342)
      | v2_struct_0(A_342) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_140,plain,(
    ! [D_343,F_344] :
      ( r1_tmap_1(D_343,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_343),F_344)
      | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3',F_344)
      | ~ m1_subset_1(F_344,u1_struct_0(D_343))
      | ~ m1_subset_1(F_344,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_343,'#skF_2')
      | v2_struct_0(D_343)
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_138])).

tff(c_143,plain,(
    ! [D_343,F_344] :
      ( r1_tmap_1(D_343,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_343),F_344)
      | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3',F_344)
      | ~ m1_subset_1(F_344,u1_struct_0(D_343))
      | ~ m1_subset_1(F_344,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_343,'#skF_2')
      | v2_struct_0(D_343)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_34,c_32,c_30,c_140])).

tff(c_145,plain,(
    ! [D_345,F_346] :
      ( r1_tmap_1(D_345,'#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3',D_345),F_346)
      | ~ r1_tmap_1('#skF_2','#skF_1','#skF_3',F_346)
      | ~ m1_subset_1(F_346,u1_struct_0(D_345))
      | ~ m1_subset_1(F_346,u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_345,'#skF_2')
      | v2_struct_0(D_345) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_38,c_143])).

tff(c_114,plain,(
    ~ r1_tmap_1('#skF_4','#skF_1',k2_tmap_1('#skF_2','#skF_1','#skF_3','#skF_4'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_148,plain,
    ( ~ r1_tmap_1('#skF_2','#skF_1','#skF_3','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_145,c_114])).

tff(c_151,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_55,c_115,c_148])).

tff(c_153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_151])).

%------------------------------------------------------------------------------
