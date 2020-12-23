%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:03 EST 2020

% Result     : Theorem 4.89s
% Output     : CNFRefutation 5.24s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 291 expanded)
%              Number of leaves         :   33 ( 127 expanded)
%              Depth                    :   20
%              Number of atoms          :  505 (2161 expanded)
%              Number of equality atoms :    3 (  82 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_155,negated_conjecture,(
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

tff(f_58,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_105,axiom,(
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

tff(c_34,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_28,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_24,plain,(
    '#skF_10' = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_32,plain,(
    m1_subset_1('#skF_10',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_69,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_32])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_50,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_48,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_30,plain,(
    v3_pre_topc('#skF_8','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_36,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_238,plain,(
    ! [A_325,B_326,C_327] :
      ( m1_connsp_2('#skF_2'(A_325,B_326,C_327),A_325,C_327)
      | ~ r2_hidden(C_327,B_326)
      | ~ m1_subset_1(C_327,u1_struct_0(A_325))
      | ~ v3_pre_topc(B_326,A_325)
      | ~ m1_subset_1(B_326,k1_zfmisc_1(u1_struct_0(A_325)))
      | ~ l1_pre_topc(A_325)
      | ~ v2_pre_topc(A_325)
      | v2_struct_0(A_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_240,plain,(
    ! [C_327] :
      ( m1_connsp_2('#skF_2'('#skF_5','#skF_8',C_327),'#skF_5',C_327)
      | ~ r2_hidden(C_327,'#skF_8')
      | ~ m1_subset_1(C_327,u1_struct_0('#skF_5'))
      | ~ v3_pre_topc('#skF_8','#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_238])).

tff(c_243,plain,(
    ! [C_327] :
      ( m1_connsp_2('#skF_2'('#skF_5','#skF_8',C_327),'#skF_5',C_327)
      | ~ r2_hidden(C_327,'#skF_8')
      | ~ m1_subset_1(C_327,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_30,c_240])).

tff(c_244,plain,(
    ! [C_327] :
      ( m1_connsp_2('#skF_2'('#skF_5','#skF_8',C_327),'#skF_5',C_327)
      | ~ r2_hidden(C_327,'#skF_8')
      | ~ m1_subset_1(C_327,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_243])).

tff(c_26,plain,(
    r1_tarski('#skF_8',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_76,plain,(
    ! [A_280,B_281] :
      ( ~ r2_hidden('#skF_1'(A_280,B_281),B_281)
      | r1_tarski(A_280,B_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_81,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_76])).

tff(c_201,plain,(
    ! [A_316,B_317,C_318] :
      ( r1_tarski('#skF_2'(A_316,B_317,C_318),B_317)
      | ~ r2_hidden(C_318,B_317)
      | ~ m1_subset_1(C_318,u1_struct_0(A_316))
      | ~ v3_pre_topc(B_317,A_316)
      | ~ m1_subset_1(B_317,k1_zfmisc_1(u1_struct_0(A_316)))
      | ~ l1_pre_topc(A_316)
      | ~ v2_pre_topc(A_316)
      | v2_struct_0(A_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_203,plain,(
    ! [C_318] :
      ( r1_tarski('#skF_2'('#skF_5','#skF_8',C_318),'#skF_8')
      | ~ r2_hidden(C_318,'#skF_8')
      | ~ m1_subset_1(C_318,u1_struct_0('#skF_5'))
      | ~ v3_pre_topc('#skF_8','#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_201])).

tff(c_206,plain,(
    ! [C_318] :
      ( r1_tarski('#skF_2'('#skF_5','#skF_8',C_318),'#skF_8')
      | ~ r2_hidden(C_318,'#skF_8')
      | ~ m1_subset_1(C_318,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_30,c_203])).

tff(c_208,plain,(
    ! [C_319] :
      ( r1_tarski('#skF_2'('#skF_5','#skF_8',C_319),'#skF_8')
      | ~ r2_hidden(C_319,'#skF_8')
      | ~ m1_subset_1(C_319,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_206])).

tff(c_83,plain,(
    ! [C_283,B_284,A_285] :
      ( r2_hidden(C_283,B_284)
      | ~ r2_hidden(C_283,A_285)
      | ~ r1_tarski(A_285,B_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_122,plain,(
    ! [A_292,B_293,B_294] :
      ( r2_hidden('#skF_1'(A_292,B_293),B_294)
      | ~ r1_tarski(A_292,B_294)
      | r1_tarski(A_292,B_293) ) ),
    inference(resolution,[status(thm)],[c_6,c_83])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_129,plain,(
    ! [A_292,B_293,B_2,B_294] :
      ( r2_hidden('#skF_1'(A_292,B_293),B_2)
      | ~ r1_tarski(B_294,B_2)
      | ~ r1_tarski(A_292,B_294)
      | r1_tarski(A_292,B_293) ) ),
    inference(resolution,[status(thm)],[c_122,c_2])).

tff(c_224,plain,(
    ! [A_320,B_321,C_322] :
      ( r2_hidden('#skF_1'(A_320,B_321),'#skF_8')
      | ~ r1_tarski(A_320,'#skF_2'('#skF_5','#skF_8',C_322))
      | r1_tarski(A_320,B_321)
      | ~ r2_hidden(C_322,'#skF_8')
      | ~ m1_subset_1(C_322,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_208,c_129])).

tff(c_229,plain,(
    ! [C_323,B_324] :
      ( r2_hidden('#skF_1'('#skF_2'('#skF_5','#skF_8',C_323),B_324),'#skF_8')
      | r1_tarski('#skF_2'('#skF_5','#skF_8',C_323),B_324)
      | ~ r2_hidden(C_323,'#skF_8')
      | ~ m1_subset_1(C_323,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_81,c_224])).

tff(c_269,plain,(
    ! [C_332,B_333,B_334] :
      ( r2_hidden('#skF_1'('#skF_2'('#skF_5','#skF_8',C_332),B_333),B_334)
      | ~ r1_tarski('#skF_8',B_334)
      | r1_tarski('#skF_2'('#skF_5','#skF_8',C_332),B_333)
      | ~ r2_hidden(C_332,'#skF_8')
      | ~ m1_subset_1(C_332,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_229,c_2])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_277,plain,(
    ! [B_334,C_332] :
      ( ~ r1_tarski('#skF_8',B_334)
      | r1_tarski('#skF_2'('#skF_5','#skF_8',C_332),B_334)
      | ~ r2_hidden(C_332,'#skF_8')
      | ~ m1_subset_1(C_332,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_269,c_4])).

tff(c_18,plain,(
    ! [A_6,B_20,C_27] :
      ( m1_subset_1('#skF_2'(A_6,B_20,C_27),k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ r2_hidden(C_27,B_20)
      | ~ m1_subset_1(C_27,u1_struct_0(A_6))
      | ~ v3_pre_topc(B_20,A_6)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_pre_topc(A_6)
      | ~ v2_pre_topc(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_66,plain,
    ( r1_tmap_1('#skF_5','#skF_4','#skF_6','#skF_9')
    | r1_tmap_1('#skF_7','#skF_4',k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_7'),'#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_67,plain,
    ( r1_tmap_1('#skF_5','#skF_4','#skF_6','#skF_9')
    | r1_tmap_1('#skF_7','#skF_4',k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_7'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_66])).

tff(c_75,plain,(
    r1_tmap_1('#skF_7','#skF_4',k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_7'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_60,plain,
    ( ~ r1_tmap_1('#skF_7','#skF_4',k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_7'),'#skF_10')
    | ~ r1_tmap_1('#skF_5','#skF_4','#skF_6','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_68,plain,
    ( ~ r1_tmap_1('#skF_7','#skF_4',k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_7'),'#skF_9')
    | ~ r1_tmap_1('#skF_5','#skF_4','#skF_6','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_60])).

tff(c_95,plain,(
    ~ r1_tmap_1('#skF_5','#skF_4','#skF_6','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_68])).

tff(c_56,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_54,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_46,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_44,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_38,plain,(
    m1_pre_topc('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_448,plain,(
    ! [D_368,A_369,E_367,B_371,G_372,C_370] :
      ( r1_tmap_1(B_371,A_369,C_370,G_372)
      | ~ r1_tmap_1(D_368,A_369,k2_tmap_1(B_371,A_369,C_370,D_368),G_372)
      | ~ m1_connsp_2(E_367,B_371,G_372)
      | ~ r1_tarski(E_367,u1_struct_0(D_368))
      | ~ m1_subset_1(G_372,u1_struct_0(D_368))
      | ~ m1_subset_1(G_372,u1_struct_0(B_371))
      | ~ m1_subset_1(E_367,k1_zfmisc_1(u1_struct_0(B_371)))
      | ~ m1_pre_topc(D_368,B_371)
      | v2_struct_0(D_368)
      | ~ m1_subset_1(C_370,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_371),u1_struct_0(A_369))))
      | ~ v1_funct_2(C_370,u1_struct_0(B_371),u1_struct_0(A_369))
      | ~ v1_funct_1(C_370)
      | ~ l1_pre_topc(B_371)
      | ~ v2_pre_topc(B_371)
      | v2_struct_0(B_371)
      | ~ l1_pre_topc(A_369)
      | ~ v2_pre_topc(A_369)
      | v2_struct_0(A_369) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_450,plain,(
    ! [E_367] :
      ( r1_tmap_1('#skF_5','#skF_4','#skF_6','#skF_9')
      | ~ m1_connsp_2(E_367,'#skF_5','#skF_9')
      | ~ r1_tarski(E_367,u1_struct_0('#skF_7'))
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_7'))
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(E_367,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_7','#skF_5')
      | v2_struct_0('#skF_7')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_75,c_448])).

tff(c_453,plain,(
    ! [E_367] :
      ( r1_tmap_1('#skF_5','#skF_4','#skF_6','#skF_9')
      | ~ m1_connsp_2(E_367,'#skF_5','#skF_9')
      | ~ r1_tarski(E_367,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(E_367,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_7')
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_48,c_46,c_44,c_42,c_38,c_34,c_69,c_450])).

tff(c_456,plain,(
    ! [E_373] :
      ( ~ m1_connsp_2(E_373,'#skF_5','#skF_9')
      | ~ r1_tarski(E_373,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(E_373,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_52,c_40,c_95,c_453])).

tff(c_460,plain,(
    ! [B_20,C_27] :
      ( ~ m1_connsp_2('#skF_2'('#skF_5',B_20,C_27),'#skF_5','#skF_9')
      | ~ r1_tarski('#skF_2'('#skF_5',B_20,C_27),u1_struct_0('#skF_7'))
      | ~ r2_hidden(C_27,B_20)
      | ~ m1_subset_1(C_27,u1_struct_0('#skF_5'))
      | ~ v3_pre_topc(B_20,'#skF_5')
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_18,c_456])).

tff(c_466,plain,(
    ! [B_20,C_27] :
      ( ~ m1_connsp_2('#skF_2'('#skF_5',B_20,C_27),'#skF_5','#skF_9')
      | ~ r1_tarski('#skF_2'('#skF_5',B_20,C_27),u1_struct_0('#skF_7'))
      | ~ r2_hidden(C_27,B_20)
      | ~ m1_subset_1(C_27,u1_struct_0('#skF_5'))
      | ~ v3_pre_topc(B_20,'#skF_5')
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_460])).

tff(c_471,plain,(
    ! [B_374,C_375] :
      ( ~ m1_connsp_2('#skF_2'('#skF_5',B_374,C_375),'#skF_5','#skF_9')
      | ~ r1_tarski('#skF_2'('#skF_5',B_374,C_375),u1_struct_0('#skF_7'))
      | ~ r2_hidden(C_375,B_374)
      | ~ m1_subset_1(C_375,u1_struct_0('#skF_5'))
      | ~ v3_pre_topc(B_374,'#skF_5')
      | ~ m1_subset_1(B_374,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_466])).

tff(c_475,plain,(
    ! [C_332] :
      ( ~ m1_connsp_2('#skF_2'('#skF_5','#skF_8',C_332),'#skF_5','#skF_9')
      | ~ v3_pre_topc('#skF_8','#skF_5')
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_tarski('#skF_8',u1_struct_0('#skF_7'))
      | ~ r2_hidden(C_332,'#skF_8')
      | ~ m1_subset_1(C_332,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_277,c_471])).

tff(c_489,plain,(
    ! [C_376] :
      ( ~ m1_connsp_2('#skF_2'('#skF_5','#skF_8',C_376),'#skF_5','#skF_9')
      | ~ r2_hidden(C_376,'#skF_8')
      | ~ m1_subset_1(C_376,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_36,c_30,c_475])).

tff(c_493,plain,
    ( ~ r2_hidden('#skF_9','#skF_8')
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_244,c_489])).

tff(c_497,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_493])).

tff(c_498,plain,(
    r1_tmap_1('#skF_5','#skF_4','#skF_6','#skF_9') ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_500,plain,(
    ! [A_377,B_378] :
      ( ~ r2_hidden('#skF_1'(A_377,B_378),B_378)
      | r1_tarski(A_377,B_378) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_505,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_500])).

tff(c_625,plain,(
    ! [A_413,B_414,C_415] :
      ( r1_tarski('#skF_2'(A_413,B_414,C_415),B_414)
      | ~ r2_hidden(C_415,B_414)
      | ~ m1_subset_1(C_415,u1_struct_0(A_413))
      | ~ v3_pre_topc(B_414,A_413)
      | ~ m1_subset_1(B_414,k1_zfmisc_1(u1_struct_0(A_413)))
      | ~ l1_pre_topc(A_413)
      | ~ v2_pre_topc(A_413)
      | v2_struct_0(A_413) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_627,plain,(
    ! [C_415] :
      ( r1_tarski('#skF_2'('#skF_5','#skF_8',C_415),'#skF_8')
      | ~ r2_hidden(C_415,'#skF_8')
      | ~ m1_subset_1(C_415,u1_struct_0('#skF_5'))
      | ~ v3_pre_topc('#skF_8','#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_625])).

tff(c_630,plain,(
    ! [C_415] :
      ( r1_tarski('#skF_2'('#skF_5','#skF_8',C_415),'#skF_8')
      | ~ r2_hidden(C_415,'#skF_8')
      | ~ m1_subset_1(C_415,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_30,c_627])).

tff(c_633,plain,(
    ! [C_419] :
      ( r1_tarski('#skF_2'('#skF_5','#skF_8',C_419),'#skF_8')
      | ~ r2_hidden(C_419,'#skF_8')
      | ~ m1_subset_1(C_419,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_630])).

tff(c_507,plain,(
    ! [C_380,B_381,A_382] :
      ( r2_hidden(C_380,B_381)
      | ~ r2_hidden(C_380,A_382)
      | ~ r1_tarski(A_382,B_381) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_539,plain,(
    ! [A_387,B_388,B_389] :
      ( r2_hidden('#skF_1'(A_387,B_388),B_389)
      | ~ r1_tarski(A_387,B_389)
      | r1_tarski(A_387,B_388) ) ),
    inference(resolution,[status(thm)],[c_6,c_507])).

tff(c_548,plain,(
    ! [A_390,B_391,B_392,B_393] :
      ( r2_hidden('#skF_1'(A_390,B_391),B_392)
      | ~ r1_tarski(B_393,B_392)
      | ~ r1_tarski(A_390,B_393)
      | r1_tarski(A_390,B_391) ) ),
    inference(resolution,[status(thm)],[c_539,c_2])).

tff(c_555,plain,(
    ! [A_394,B_395] :
      ( r2_hidden('#skF_1'(A_394,B_395),u1_struct_0('#skF_7'))
      | ~ r1_tarski(A_394,'#skF_8')
      | r1_tarski(A_394,B_395) ) ),
    inference(resolution,[status(thm)],[c_26,c_548])).

tff(c_571,plain,(
    ! [A_398] :
      ( ~ r1_tarski(A_398,'#skF_8')
      | r1_tarski(A_398,u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_555,c_4])).

tff(c_546,plain,(
    ! [A_387,B_388,B_2,B_389] :
      ( r2_hidden('#skF_1'(A_387,B_388),B_2)
      | ~ r1_tarski(B_389,B_2)
      | ~ r1_tarski(A_387,B_389)
      | r1_tarski(A_387,B_388) ) ),
    inference(resolution,[status(thm)],[c_539,c_2])).

tff(c_580,plain,(
    ! [A_387,B_388,A_398] :
      ( r2_hidden('#skF_1'(A_387,B_388),u1_struct_0('#skF_7'))
      | ~ r1_tarski(A_387,A_398)
      | r1_tarski(A_387,B_388)
      | ~ r1_tarski(A_398,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_571,c_546])).

tff(c_637,plain,(
    ! [C_419,B_388] :
      ( r2_hidden('#skF_1'('#skF_2'('#skF_5','#skF_8',C_419),B_388),u1_struct_0('#skF_7'))
      | r1_tarski('#skF_2'('#skF_5','#skF_8',C_419),B_388)
      | ~ r1_tarski('#skF_8','#skF_8')
      | ~ r2_hidden(C_419,'#skF_8')
      | ~ m1_subset_1(C_419,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_633,c_580])).

tff(c_663,plain,(
    ! [C_425,B_426] :
      ( r2_hidden('#skF_1'('#skF_2'('#skF_5','#skF_8',C_425),B_426),u1_struct_0('#skF_7'))
      | r1_tarski('#skF_2'('#skF_5','#skF_8',C_425),B_426)
      | ~ r2_hidden(C_425,'#skF_8')
      | ~ m1_subset_1(C_425,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_637])).

tff(c_671,plain,(
    ! [C_425] :
      ( r1_tarski('#skF_2'('#skF_5','#skF_8',C_425),u1_struct_0('#skF_7'))
      | ~ r2_hidden(C_425,'#skF_8')
      | ~ m1_subset_1(C_425,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_663,c_4])).

tff(c_730,plain,(
    ! [A_440,B_441,C_442] :
      ( m1_connsp_2('#skF_2'(A_440,B_441,C_442),A_440,C_442)
      | ~ r2_hidden(C_442,B_441)
      | ~ m1_subset_1(C_442,u1_struct_0(A_440))
      | ~ v3_pre_topc(B_441,A_440)
      | ~ m1_subset_1(B_441,k1_zfmisc_1(u1_struct_0(A_440)))
      | ~ l1_pre_topc(A_440)
      | ~ v2_pre_topc(A_440)
      | v2_struct_0(A_440) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_732,plain,(
    ! [C_442] :
      ( m1_connsp_2('#skF_2'('#skF_5','#skF_8',C_442),'#skF_5',C_442)
      | ~ r2_hidden(C_442,'#skF_8')
      | ~ m1_subset_1(C_442,u1_struct_0('#skF_5'))
      | ~ v3_pre_topc('#skF_8','#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_730])).

tff(c_735,plain,(
    ! [C_442] :
      ( m1_connsp_2('#skF_2'('#skF_5','#skF_8',C_442),'#skF_5',C_442)
      | ~ r2_hidden(C_442,'#skF_8')
      | ~ m1_subset_1(C_442,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_30,c_732])).

tff(c_736,plain,(
    ! [C_442] :
      ( m1_connsp_2('#skF_2'('#skF_5','#skF_8',C_442),'#skF_5',C_442)
      | ~ r2_hidden(C_442,'#skF_8')
      | ~ m1_subset_1(C_442,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_735])).

tff(c_904,plain,(
    ! [D_482,A_483,C_484,B_485,G_486,E_481] :
      ( r1_tmap_1(D_482,A_483,k2_tmap_1(B_485,A_483,C_484,D_482),G_486)
      | ~ r1_tmap_1(B_485,A_483,C_484,G_486)
      | ~ m1_connsp_2(E_481,B_485,G_486)
      | ~ r1_tarski(E_481,u1_struct_0(D_482))
      | ~ m1_subset_1(G_486,u1_struct_0(D_482))
      | ~ m1_subset_1(G_486,u1_struct_0(B_485))
      | ~ m1_subset_1(E_481,k1_zfmisc_1(u1_struct_0(B_485)))
      | ~ m1_pre_topc(D_482,B_485)
      | v2_struct_0(D_482)
      | ~ m1_subset_1(C_484,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_485),u1_struct_0(A_483))))
      | ~ v1_funct_2(C_484,u1_struct_0(B_485),u1_struct_0(A_483))
      | ~ v1_funct_1(C_484)
      | ~ l1_pre_topc(B_485)
      | ~ v2_pre_topc(B_485)
      | v2_struct_0(B_485)
      | ~ l1_pre_topc(A_483)
      | ~ v2_pre_topc(A_483)
      | v2_struct_0(A_483) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_906,plain,(
    ! [D_482,A_483,C_484,C_442] :
      ( r1_tmap_1(D_482,A_483,k2_tmap_1('#skF_5',A_483,C_484,D_482),C_442)
      | ~ r1_tmap_1('#skF_5',A_483,C_484,C_442)
      | ~ r1_tarski('#skF_2'('#skF_5','#skF_8',C_442),u1_struct_0(D_482))
      | ~ m1_subset_1(C_442,u1_struct_0(D_482))
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_8',C_442),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc(D_482,'#skF_5')
      | v2_struct_0(D_482)
      | ~ m1_subset_1(C_484,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(A_483))))
      | ~ v1_funct_2(C_484,u1_struct_0('#skF_5'),u1_struct_0(A_483))
      | ~ v1_funct_1(C_484)
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_483)
      | ~ v2_pre_topc(A_483)
      | v2_struct_0(A_483)
      | ~ r2_hidden(C_442,'#skF_8')
      | ~ m1_subset_1(C_442,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_736,c_904])).

tff(c_909,plain,(
    ! [D_482,A_483,C_484,C_442] :
      ( r1_tmap_1(D_482,A_483,k2_tmap_1('#skF_5',A_483,C_484,D_482),C_442)
      | ~ r1_tmap_1('#skF_5',A_483,C_484,C_442)
      | ~ r1_tarski('#skF_2'('#skF_5','#skF_8',C_442),u1_struct_0(D_482))
      | ~ m1_subset_1(C_442,u1_struct_0(D_482))
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_8',C_442),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc(D_482,'#skF_5')
      | v2_struct_0(D_482)
      | ~ m1_subset_1(C_484,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(A_483))))
      | ~ v1_funct_2(C_484,u1_struct_0('#skF_5'),u1_struct_0(A_483))
      | ~ v1_funct_1(C_484)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_483)
      | ~ v2_pre_topc(A_483)
      | v2_struct_0(A_483)
      | ~ r2_hidden(C_442,'#skF_8')
      | ~ m1_subset_1(C_442,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_906])).

tff(c_1136,plain,(
    ! [D_532,A_533,C_534,C_535] :
      ( r1_tmap_1(D_532,A_533,k2_tmap_1('#skF_5',A_533,C_534,D_532),C_535)
      | ~ r1_tmap_1('#skF_5',A_533,C_534,C_535)
      | ~ r1_tarski('#skF_2'('#skF_5','#skF_8',C_535),u1_struct_0(D_532))
      | ~ m1_subset_1(C_535,u1_struct_0(D_532))
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_8',C_535),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc(D_532,'#skF_5')
      | v2_struct_0(D_532)
      | ~ m1_subset_1(C_534,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(A_533))))
      | ~ v1_funct_2(C_534,u1_struct_0('#skF_5'),u1_struct_0(A_533))
      | ~ v1_funct_1(C_534)
      | ~ l1_pre_topc(A_533)
      | ~ v2_pre_topc(A_533)
      | v2_struct_0(A_533)
      | ~ r2_hidden(C_535,'#skF_8')
      | ~ m1_subset_1(C_535,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_909])).

tff(c_1141,plain,(
    ! [A_533,C_534,C_425] :
      ( r1_tmap_1('#skF_7',A_533,k2_tmap_1('#skF_5',A_533,C_534,'#skF_7'),C_425)
      | ~ r1_tmap_1('#skF_5',A_533,C_534,C_425)
      | ~ m1_subset_1(C_425,u1_struct_0('#skF_7'))
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_8',C_425),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_7','#skF_5')
      | v2_struct_0('#skF_7')
      | ~ m1_subset_1(C_534,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(A_533))))
      | ~ v1_funct_2(C_534,u1_struct_0('#skF_5'),u1_struct_0(A_533))
      | ~ v1_funct_1(C_534)
      | ~ l1_pre_topc(A_533)
      | ~ v2_pre_topc(A_533)
      | v2_struct_0(A_533)
      | ~ r2_hidden(C_425,'#skF_8')
      | ~ m1_subset_1(C_425,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_671,c_1136])).

tff(c_1148,plain,(
    ! [A_533,C_534,C_425] :
      ( r1_tmap_1('#skF_7',A_533,k2_tmap_1('#skF_5',A_533,C_534,'#skF_7'),C_425)
      | ~ r1_tmap_1('#skF_5',A_533,C_534,C_425)
      | ~ m1_subset_1(C_425,u1_struct_0('#skF_7'))
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_8',C_425),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_7')
      | ~ m1_subset_1(C_534,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(A_533))))
      | ~ v1_funct_2(C_534,u1_struct_0('#skF_5'),u1_struct_0(A_533))
      | ~ v1_funct_1(C_534)
      | ~ l1_pre_topc(A_533)
      | ~ v2_pre_topc(A_533)
      | v2_struct_0(A_533)
      | ~ r2_hidden(C_425,'#skF_8')
      | ~ m1_subset_1(C_425,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1141])).

tff(c_1787,plain,(
    ! [A_635,C_636,C_637] :
      ( r1_tmap_1('#skF_7',A_635,k2_tmap_1('#skF_5',A_635,C_636,'#skF_7'),C_637)
      | ~ r1_tmap_1('#skF_5',A_635,C_636,C_637)
      | ~ m1_subset_1(C_637,u1_struct_0('#skF_7'))
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_8',C_637),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(C_636,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(A_635))))
      | ~ v1_funct_2(C_636,u1_struct_0('#skF_5'),u1_struct_0(A_635))
      | ~ v1_funct_1(C_636)
      | ~ l1_pre_topc(A_635)
      | ~ v2_pre_topc(A_635)
      | v2_struct_0(A_635)
      | ~ r2_hidden(C_637,'#skF_8')
      | ~ m1_subset_1(C_637,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1148])).

tff(c_1790,plain,(
    ! [A_635,C_636,C_27] :
      ( r1_tmap_1('#skF_7',A_635,k2_tmap_1('#skF_5',A_635,C_636,'#skF_7'),C_27)
      | ~ r1_tmap_1('#skF_5',A_635,C_636,C_27)
      | ~ m1_subset_1(C_27,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(C_636,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(A_635))))
      | ~ v1_funct_2(C_636,u1_struct_0('#skF_5'),u1_struct_0(A_635))
      | ~ v1_funct_1(C_636)
      | ~ l1_pre_topc(A_635)
      | ~ v2_pre_topc(A_635)
      | v2_struct_0(A_635)
      | ~ r2_hidden(C_27,'#skF_8')
      | ~ m1_subset_1(C_27,u1_struct_0('#skF_5'))
      | ~ v3_pre_topc('#skF_8','#skF_5')
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_18,c_1787])).

tff(c_1793,plain,(
    ! [A_635,C_636,C_27] :
      ( r1_tmap_1('#skF_7',A_635,k2_tmap_1('#skF_5',A_635,C_636,'#skF_7'),C_27)
      | ~ r1_tmap_1('#skF_5',A_635,C_636,C_27)
      | ~ m1_subset_1(C_27,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(C_636,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(A_635))))
      | ~ v1_funct_2(C_636,u1_struct_0('#skF_5'),u1_struct_0(A_635))
      | ~ v1_funct_1(C_636)
      | ~ l1_pre_topc(A_635)
      | ~ v2_pre_topc(A_635)
      | v2_struct_0(A_635)
      | ~ r2_hidden(C_27,'#skF_8')
      | ~ m1_subset_1(C_27,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_36,c_30,c_1790])).

tff(c_1795,plain,(
    ! [A_638,C_639,C_640] :
      ( r1_tmap_1('#skF_7',A_638,k2_tmap_1('#skF_5',A_638,C_639,'#skF_7'),C_640)
      | ~ r1_tmap_1('#skF_5',A_638,C_639,C_640)
      | ~ m1_subset_1(C_640,u1_struct_0('#skF_7'))
      | ~ m1_subset_1(C_639,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0(A_638))))
      | ~ v1_funct_2(C_639,u1_struct_0('#skF_5'),u1_struct_0(A_638))
      | ~ v1_funct_1(C_639)
      | ~ l1_pre_topc(A_638)
      | ~ v2_pre_topc(A_638)
      | v2_struct_0(A_638)
      | ~ r2_hidden(C_640,'#skF_8')
      | ~ m1_subset_1(C_640,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1793])).

tff(c_1797,plain,(
    ! [C_640] :
      ( r1_tmap_1('#skF_7','#skF_4',k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_7'),C_640)
      | ~ r1_tmap_1('#skF_5','#skF_4','#skF_6',C_640)
      | ~ m1_subset_1(C_640,u1_struct_0('#skF_7'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r2_hidden(C_640,'#skF_8')
      | ~ m1_subset_1(C_640,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_42,c_1795])).

tff(c_1800,plain,(
    ! [C_640] :
      ( r1_tmap_1('#skF_7','#skF_4',k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_7'),C_640)
      | ~ r1_tmap_1('#skF_5','#skF_4','#skF_6',C_640)
      | ~ m1_subset_1(C_640,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_4')
      | ~ r2_hidden(C_640,'#skF_8')
      | ~ m1_subset_1(C_640,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_46,c_44,c_1797])).

tff(c_1802,plain,(
    ! [C_641] :
      ( r1_tmap_1('#skF_7','#skF_4',k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_7'),C_641)
      | ~ r1_tmap_1('#skF_5','#skF_4','#skF_6',C_641)
      | ~ m1_subset_1(C_641,u1_struct_0('#skF_7'))
      | ~ r2_hidden(C_641,'#skF_8')
      | ~ m1_subset_1(C_641,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1800])).

tff(c_499,plain,(
    ~ r1_tmap_1('#skF_7','#skF_4',k2_tmap_1('#skF_5','#skF_4','#skF_6','#skF_7'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_1807,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_4','#skF_6','#skF_9')
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_7'))
    | ~ r2_hidden('#skF_9','#skF_8')
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1802,c_499])).

tff(c_1815,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_69,c_498,c_1807])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:12:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.89/1.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.89/1.93  
% 4.89/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.24/1.93  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4 > #skF_1
% 5.24/1.93  
% 5.24/1.93  %Foreground sorts:
% 5.24/1.93  
% 5.24/1.93  
% 5.24/1.93  %Background operators:
% 5.24/1.93  
% 5.24/1.93  
% 5.24/1.93  %Foreground operators:
% 5.24/1.93  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.24/1.93  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 5.24/1.93  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.24/1.93  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.24/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.24/1.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.24/1.93  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 5.24/1.93  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.24/1.93  tff('#skF_7', type, '#skF_7': $i).
% 5.24/1.93  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.24/1.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.24/1.93  tff('#skF_10', type, '#skF_10': $i).
% 5.24/1.93  tff('#skF_5', type, '#skF_5': $i).
% 5.24/1.93  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.24/1.93  tff('#skF_6', type, '#skF_6': $i).
% 5.24/1.93  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.24/1.93  tff('#skF_9', type, '#skF_9': $i).
% 5.24/1.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.24/1.93  tff('#skF_8', type, '#skF_8': $i).
% 5.24/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.24/1.93  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.24/1.93  tff('#skF_4', type, '#skF_4': $i).
% 5.24/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.24/1.93  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.24/1.93  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.24/1.93  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 5.24/1.93  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.24/1.93  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.24/1.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.24/1.93  
% 5.24/1.96  tff(f_155, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((v3_pre_topc(E, B) & r2_hidden(F, E)) & r1_tarski(E, u1_struct_0(D))) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_tmap_1)).
% 5.24/1.96  tff(f_58, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(D, A, C) & r1_tarski(D, B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_connsp_2)).
% 5.24/1.96  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.24/1.96  tff(f_105, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tmap_1)).
% 5.24/1.96  tff(c_34, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.24/1.96  tff(c_28, plain, (r2_hidden('#skF_9', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.24/1.96  tff(c_24, plain, ('#skF_10'='#skF_9'), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.24/1.96  tff(c_32, plain, (m1_subset_1('#skF_10', u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.24/1.96  tff(c_69, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_32])).
% 5.24/1.96  tff(c_52, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.24/1.96  tff(c_50, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.24/1.96  tff(c_48, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.24/1.96  tff(c_30, plain, (v3_pre_topc('#skF_8', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.24/1.96  tff(c_36, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.24/1.96  tff(c_238, plain, (![A_325, B_326, C_327]: (m1_connsp_2('#skF_2'(A_325, B_326, C_327), A_325, C_327) | ~r2_hidden(C_327, B_326) | ~m1_subset_1(C_327, u1_struct_0(A_325)) | ~v3_pre_topc(B_326, A_325) | ~m1_subset_1(B_326, k1_zfmisc_1(u1_struct_0(A_325))) | ~l1_pre_topc(A_325) | ~v2_pre_topc(A_325) | v2_struct_0(A_325))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.24/1.96  tff(c_240, plain, (![C_327]: (m1_connsp_2('#skF_2'('#skF_5', '#skF_8', C_327), '#skF_5', C_327) | ~r2_hidden(C_327, '#skF_8') | ~m1_subset_1(C_327, u1_struct_0('#skF_5')) | ~v3_pre_topc('#skF_8', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_36, c_238])).
% 5.24/1.96  tff(c_243, plain, (![C_327]: (m1_connsp_2('#skF_2'('#skF_5', '#skF_8', C_327), '#skF_5', C_327) | ~r2_hidden(C_327, '#skF_8') | ~m1_subset_1(C_327, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_30, c_240])).
% 5.24/1.96  tff(c_244, plain, (![C_327]: (m1_connsp_2('#skF_2'('#skF_5', '#skF_8', C_327), '#skF_5', C_327) | ~r2_hidden(C_327, '#skF_8') | ~m1_subset_1(C_327, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_52, c_243])).
% 5.24/1.96  tff(c_26, plain, (r1_tarski('#skF_8', u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.24/1.96  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.24/1.96  tff(c_76, plain, (![A_280, B_281]: (~r2_hidden('#skF_1'(A_280, B_281), B_281) | r1_tarski(A_280, B_281))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.24/1.96  tff(c_81, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_76])).
% 5.24/1.96  tff(c_201, plain, (![A_316, B_317, C_318]: (r1_tarski('#skF_2'(A_316, B_317, C_318), B_317) | ~r2_hidden(C_318, B_317) | ~m1_subset_1(C_318, u1_struct_0(A_316)) | ~v3_pre_topc(B_317, A_316) | ~m1_subset_1(B_317, k1_zfmisc_1(u1_struct_0(A_316))) | ~l1_pre_topc(A_316) | ~v2_pre_topc(A_316) | v2_struct_0(A_316))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.24/1.96  tff(c_203, plain, (![C_318]: (r1_tarski('#skF_2'('#skF_5', '#skF_8', C_318), '#skF_8') | ~r2_hidden(C_318, '#skF_8') | ~m1_subset_1(C_318, u1_struct_0('#skF_5')) | ~v3_pre_topc('#skF_8', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_36, c_201])).
% 5.24/1.96  tff(c_206, plain, (![C_318]: (r1_tarski('#skF_2'('#skF_5', '#skF_8', C_318), '#skF_8') | ~r2_hidden(C_318, '#skF_8') | ~m1_subset_1(C_318, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_30, c_203])).
% 5.24/1.96  tff(c_208, plain, (![C_319]: (r1_tarski('#skF_2'('#skF_5', '#skF_8', C_319), '#skF_8') | ~r2_hidden(C_319, '#skF_8') | ~m1_subset_1(C_319, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_52, c_206])).
% 5.24/1.96  tff(c_83, plain, (![C_283, B_284, A_285]: (r2_hidden(C_283, B_284) | ~r2_hidden(C_283, A_285) | ~r1_tarski(A_285, B_284))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.24/1.96  tff(c_122, plain, (![A_292, B_293, B_294]: (r2_hidden('#skF_1'(A_292, B_293), B_294) | ~r1_tarski(A_292, B_294) | r1_tarski(A_292, B_293))), inference(resolution, [status(thm)], [c_6, c_83])).
% 5.24/1.96  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.24/1.96  tff(c_129, plain, (![A_292, B_293, B_2, B_294]: (r2_hidden('#skF_1'(A_292, B_293), B_2) | ~r1_tarski(B_294, B_2) | ~r1_tarski(A_292, B_294) | r1_tarski(A_292, B_293))), inference(resolution, [status(thm)], [c_122, c_2])).
% 5.24/1.96  tff(c_224, plain, (![A_320, B_321, C_322]: (r2_hidden('#skF_1'(A_320, B_321), '#skF_8') | ~r1_tarski(A_320, '#skF_2'('#skF_5', '#skF_8', C_322)) | r1_tarski(A_320, B_321) | ~r2_hidden(C_322, '#skF_8') | ~m1_subset_1(C_322, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_208, c_129])).
% 5.24/1.96  tff(c_229, plain, (![C_323, B_324]: (r2_hidden('#skF_1'('#skF_2'('#skF_5', '#skF_8', C_323), B_324), '#skF_8') | r1_tarski('#skF_2'('#skF_5', '#skF_8', C_323), B_324) | ~r2_hidden(C_323, '#skF_8') | ~m1_subset_1(C_323, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_81, c_224])).
% 5.24/1.96  tff(c_269, plain, (![C_332, B_333, B_334]: (r2_hidden('#skF_1'('#skF_2'('#skF_5', '#skF_8', C_332), B_333), B_334) | ~r1_tarski('#skF_8', B_334) | r1_tarski('#skF_2'('#skF_5', '#skF_8', C_332), B_333) | ~r2_hidden(C_332, '#skF_8') | ~m1_subset_1(C_332, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_229, c_2])).
% 5.24/1.96  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.24/1.96  tff(c_277, plain, (![B_334, C_332]: (~r1_tarski('#skF_8', B_334) | r1_tarski('#skF_2'('#skF_5', '#skF_8', C_332), B_334) | ~r2_hidden(C_332, '#skF_8') | ~m1_subset_1(C_332, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_269, c_4])).
% 5.24/1.96  tff(c_18, plain, (![A_6, B_20, C_27]: (m1_subset_1('#skF_2'(A_6, B_20, C_27), k1_zfmisc_1(u1_struct_0(A_6))) | ~r2_hidden(C_27, B_20) | ~m1_subset_1(C_27, u1_struct_0(A_6)) | ~v3_pre_topc(B_20, A_6) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_6))) | ~l1_pre_topc(A_6) | ~v2_pre_topc(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.24/1.96  tff(c_58, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.24/1.96  tff(c_40, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.24/1.96  tff(c_66, plain, (r1_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_9') | r1_tmap_1('#skF_7', '#skF_4', k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_7'), '#skF_10')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.24/1.96  tff(c_67, plain, (r1_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_9') | r1_tmap_1('#skF_7', '#skF_4', k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_7'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_66])).
% 5.24/1.96  tff(c_75, plain, (r1_tmap_1('#skF_7', '#skF_4', k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_7'), '#skF_9')), inference(splitLeft, [status(thm)], [c_67])).
% 5.24/1.96  tff(c_60, plain, (~r1_tmap_1('#skF_7', '#skF_4', k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_7'), '#skF_10') | ~r1_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.24/1.96  tff(c_68, plain, (~r1_tmap_1('#skF_7', '#skF_4', k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_7'), '#skF_9') | ~r1_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_60])).
% 5.24/1.96  tff(c_95, plain, (~r1_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_68])).
% 5.24/1.96  tff(c_56, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.24/1.96  tff(c_54, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.24/1.96  tff(c_46, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.24/1.96  tff(c_44, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.24/1.96  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.24/1.96  tff(c_38, plain, (m1_pre_topc('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.24/1.96  tff(c_448, plain, (![D_368, A_369, E_367, B_371, G_372, C_370]: (r1_tmap_1(B_371, A_369, C_370, G_372) | ~r1_tmap_1(D_368, A_369, k2_tmap_1(B_371, A_369, C_370, D_368), G_372) | ~m1_connsp_2(E_367, B_371, G_372) | ~r1_tarski(E_367, u1_struct_0(D_368)) | ~m1_subset_1(G_372, u1_struct_0(D_368)) | ~m1_subset_1(G_372, u1_struct_0(B_371)) | ~m1_subset_1(E_367, k1_zfmisc_1(u1_struct_0(B_371))) | ~m1_pre_topc(D_368, B_371) | v2_struct_0(D_368) | ~m1_subset_1(C_370, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_371), u1_struct_0(A_369)))) | ~v1_funct_2(C_370, u1_struct_0(B_371), u1_struct_0(A_369)) | ~v1_funct_1(C_370) | ~l1_pre_topc(B_371) | ~v2_pre_topc(B_371) | v2_struct_0(B_371) | ~l1_pre_topc(A_369) | ~v2_pre_topc(A_369) | v2_struct_0(A_369))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.24/1.96  tff(c_450, plain, (![E_367]: (r1_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_9') | ~m1_connsp_2(E_367, '#skF_5', '#skF_9') | ~r1_tarski(E_367, u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_5')) | ~m1_subset_1(E_367, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_7', '#skF_5') | v2_struct_0('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_75, c_448])).
% 5.24/1.96  tff(c_453, plain, (![E_367]: (r1_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_9') | ~m1_connsp_2(E_367, '#skF_5', '#skF_9') | ~r1_tarski(E_367, u1_struct_0('#skF_7')) | ~m1_subset_1(E_367, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_7') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_50, c_48, c_46, c_44, c_42, c_38, c_34, c_69, c_450])).
% 5.24/1.96  tff(c_456, plain, (![E_373]: (~m1_connsp_2(E_373, '#skF_5', '#skF_9') | ~r1_tarski(E_373, u1_struct_0('#skF_7')) | ~m1_subset_1(E_373, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_52, c_40, c_95, c_453])).
% 5.24/1.96  tff(c_460, plain, (![B_20, C_27]: (~m1_connsp_2('#skF_2'('#skF_5', B_20, C_27), '#skF_5', '#skF_9') | ~r1_tarski('#skF_2'('#skF_5', B_20, C_27), u1_struct_0('#skF_7')) | ~r2_hidden(C_27, B_20) | ~m1_subset_1(C_27, u1_struct_0('#skF_5')) | ~v3_pre_topc(B_20, '#skF_5') | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_18, c_456])).
% 5.24/1.96  tff(c_466, plain, (![B_20, C_27]: (~m1_connsp_2('#skF_2'('#skF_5', B_20, C_27), '#skF_5', '#skF_9') | ~r1_tarski('#skF_2'('#skF_5', B_20, C_27), u1_struct_0('#skF_7')) | ~r2_hidden(C_27, B_20) | ~m1_subset_1(C_27, u1_struct_0('#skF_5')) | ~v3_pre_topc(B_20, '#skF_5') | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_460])).
% 5.24/1.96  tff(c_471, plain, (![B_374, C_375]: (~m1_connsp_2('#skF_2'('#skF_5', B_374, C_375), '#skF_5', '#skF_9') | ~r1_tarski('#skF_2'('#skF_5', B_374, C_375), u1_struct_0('#skF_7')) | ~r2_hidden(C_375, B_374) | ~m1_subset_1(C_375, u1_struct_0('#skF_5')) | ~v3_pre_topc(B_374, '#skF_5') | ~m1_subset_1(B_374, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_466])).
% 5.24/1.96  tff(c_475, plain, (![C_332]: (~m1_connsp_2('#skF_2'('#skF_5', '#skF_8', C_332), '#skF_5', '#skF_9') | ~v3_pre_topc('#skF_8', '#skF_5') | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_tarski('#skF_8', u1_struct_0('#skF_7')) | ~r2_hidden(C_332, '#skF_8') | ~m1_subset_1(C_332, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_277, c_471])).
% 5.24/1.96  tff(c_489, plain, (![C_376]: (~m1_connsp_2('#skF_2'('#skF_5', '#skF_8', C_376), '#skF_5', '#skF_9') | ~r2_hidden(C_376, '#skF_8') | ~m1_subset_1(C_376, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_36, c_30, c_475])).
% 5.24/1.96  tff(c_493, plain, (~r2_hidden('#skF_9', '#skF_8') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_244, c_489])).
% 5.24/1.96  tff(c_497, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_493])).
% 5.24/1.96  tff(c_498, plain, (r1_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_9')), inference(splitRight, [status(thm)], [c_67])).
% 5.24/1.96  tff(c_500, plain, (![A_377, B_378]: (~r2_hidden('#skF_1'(A_377, B_378), B_378) | r1_tarski(A_377, B_378))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.24/1.96  tff(c_505, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_500])).
% 5.24/1.96  tff(c_625, plain, (![A_413, B_414, C_415]: (r1_tarski('#skF_2'(A_413, B_414, C_415), B_414) | ~r2_hidden(C_415, B_414) | ~m1_subset_1(C_415, u1_struct_0(A_413)) | ~v3_pre_topc(B_414, A_413) | ~m1_subset_1(B_414, k1_zfmisc_1(u1_struct_0(A_413))) | ~l1_pre_topc(A_413) | ~v2_pre_topc(A_413) | v2_struct_0(A_413))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.24/1.96  tff(c_627, plain, (![C_415]: (r1_tarski('#skF_2'('#skF_5', '#skF_8', C_415), '#skF_8') | ~r2_hidden(C_415, '#skF_8') | ~m1_subset_1(C_415, u1_struct_0('#skF_5')) | ~v3_pre_topc('#skF_8', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_36, c_625])).
% 5.24/1.96  tff(c_630, plain, (![C_415]: (r1_tarski('#skF_2'('#skF_5', '#skF_8', C_415), '#skF_8') | ~r2_hidden(C_415, '#skF_8') | ~m1_subset_1(C_415, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_30, c_627])).
% 5.24/1.96  tff(c_633, plain, (![C_419]: (r1_tarski('#skF_2'('#skF_5', '#skF_8', C_419), '#skF_8') | ~r2_hidden(C_419, '#skF_8') | ~m1_subset_1(C_419, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_52, c_630])).
% 5.24/1.96  tff(c_507, plain, (![C_380, B_381, A_382]: (r2_hidden(C_380, B_381) | ~r2_hidden(C_380, A_382) | ~r1_tarski(A_382, B_381))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.24/1.96  tff(c_539, plain, (![A_387, B_388, B_389]: (r2_hidden('#skF_1'(A_387, B_388), B_389) | ~r1_tarski(A_387, B_389) | r1_tarski(A_387, B_388))), inference(resolution, [status(thm)], [c_6, c_507])).
% 5.24/1.96  tff(c_548, plain, (![A_390, B_391, B_392, B_393]: (r2_hidden('#skF_1'(A_390, B_391), B_392) | ~r1_tarski(B_393, B_392) | ~r1_tarski(A_390, B_393) | r1_tarski(A_390, B_391))), inference(resolution, [status(thm)], [c_539, c_2])).
% 5.24/1.96  tff(c_555, plain, (![A_394, B_395]: (r2_hidden('#skF_1'(A_394, B_395), u1_struct_0('#skF_7')) | ~r1_tarski(A_394, '#skF_8') | r1_tarski(A_394, B_395))), inference(resolution, [status(thm)], [c_26, c_548])).
% 5.24/1.96  tff(c_571, plain, (![A_398]: (~r1_tarski(A_398, '#skF_8') | r1_tarski(A_398, u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_555, c_4])).
% 5.24/1.96  tff(c_546, plain, (![A_387, B_388, B_2, B_389]: (r2_hidden('#skF_1'(A_387, B_388), B_2) | ~r1_tarski(B_389, B_2) | ~r1_tarski(A_387, B_389) | r1_tarski(A_387, B_388))), inference(resolution, [status(thm)], [c_539, c_2])).
% 5.24/1.96  tff(c_580, plain, (![A_387, B_388, A_398]: (r2_hidden('#skF_1'(A_387, B_388), u1_struct_0('#skF_7')) | ~r1_tarski(A_387, A_398) | r1_tarski(A_387, B_388) | ~r1_tarski(A_398, '#skF_8'))), inference(resolution, [status(thm)], [c_571, c_546])).
% 5.24/1.96  tff(c_637, plain, (![C_419, B_388]: (r2_hidden('#skF_1'('#skF_2'('#skF_5', '#skF_8', C_419), B_388), u1_struct_0('#skF_7')) | r1_tarski('#skF_2'('#skF_5', '#skF_8', C_419), B_388) | ~r1_tarski('#skF_8', '#skF_8') | ~r2_hidden(C_419, '#skF_8') | ~m1_subset_1(C_419, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_633, c_580])).
% 5.24/1.96  tff(c_663, plain, (![C_425, B_426]: (r2_hidden('#skF_1'('#skF_2'('#skF_5', '#skF_8', C_425), B_426), u1_struct_0('#skF_7')) | r1_tarski('#skF_2'('#skF_5', '#skF_8', C_425), B_426) | ~r2_hidden(C_425, '#skF_8') | ~m1_subset_1(C_425, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_505, c_637])).
% 5.24/1.96  tff(c_671, plain, (![C_425]: (r1_tarski('#skF_2'('#skF_5', '#skF_8', C_425), u1_struct_0('#skF_7')) | ~r2_hidden(C_425, '#skF_8') | ~m1_subset_1(C_425, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_663, c_4])).
% 5.24/1.96  tff(c_730, plain, (![A_440, B_441, C_442]: (m1_connsp_2('#skF_2'(A_440, B_441, C_442), A_440, C_442) | ~r2_hidden(C_442, B_441) | ~m1_subset_1(C_442, u1_struct_0(A_440)) | ~v3_pre_topc(B_441, A_440) | ~m1_subset_1(B_441, k1_zfmisc_1(u1_struct_0(A_440))) | ~l1_pre_topc(A_440) | ~v2_pre_topc(A_440) | v2_struct_0(A_440))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.24/1.96  tff(c_732, plain, (![C_442]: (m1_connsp_2('#skF_2'('#skF_5', '#skF_8', C_442), '#skF_5', C_442) | ~r2_hidden(C_442, '#skF_8') | ~m1_subset_1(C_442, u1_struct_0('#skF_5')) | ~v3_pre_topc('#skF_8', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_36, c_730])).
% 5.24/1.96  tff(c_735, plain, (![C_442]: (m1_connsp_2('#skF_2'('#skF_5', '#skF_8', C_442), '#skF_5', C_442) | ~r2_hidden(C_442, '#skF_8') | ~m1_subset_1(C_442, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_30, c_732])).
% 5.24/1.96  tff(c_736, plain, (![C_442]: (m1_connsp_2('#skF_2'('#skF_5', '#skF_8', C_442), '#skF_5', C_442) | ~r2_hidden(C_442, '#skF_8') | ~m1_subset_1(C_442, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_52, c_735])).
% 5.24/1.96  tff(c_904, plain, (![D_482, A_483, C_484, B_485, G_486, E_481]: (r1_tmap_1(D_482, A_483, k2_tmap_1(B_485, A_483, C_484, D_482), G_486) | ~r1_tmap_1(B_485, A_483, C_484, G_486) | ~m1_connsp_2(E_481, B_485, G_486) | ~r1_tarski(E_481, u1_struct_0(D_482)) | ~m1_subset_1(G_486, u1_struct_0(D_482)) | ~m1_subset_1(G_486, u1_struct_0(B_485)) | ~m1_subset_1(E_481, k1_zfmisc_1(u1_struct_0(B_485))) | ~m1_pre_topc(D_482, B_485) | v2_struct_0(D_482) | ~m1_subset_1(C_484, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_485), u1_struct_0(A_483)))) | ~v1_funct_2(C_484, u1_struct_0(B_485), u1_struct_0(A_483)) | ~v1_funct_1(C_484) | ~l1_pre_topc(B_485) | ~v2_pre_topc(B_485) | v2_struct_0(B_485) | ~l1_pre_topc(A_483) | ~v2_pre_topc(A_483) | v2_struct_0(A_483))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.24/1.96  tff(c_906, plain, (![D_482, A_483, C_484, C_442]: (r1_tmap_1(D_482, A_483, k2_tmap_1('#skF_5', A_483, C_484, D_482), C_442) | ~r1_tmap_1('#skF_5', A_483, C_484, C_442) | ~r1_tarski('#skF_2'('#skF_5', '#skF_8', C_442), u1_struct_0(D_482)) | ~m1_subset_1(C_442, u1_struct_0(D_482)) | ~m1_subset_1('#skF_2'('#skF_5', '#skF_8', C_442), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc(D_482, '#skF_5') | v2_struct_0(D_482) | ~m1_subset_1(C_484, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(A_483)))) | ~v1_funct_2(C_484, u1_struct_0('#skF_5'), u1_struct_0(A_483)) | ~v1_funct_1(C_484) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc(A_483) | ~v2_pre_topc(A_483) | v2_struct_0(A_483) | ~r2_hidden(C_442, '#skF_8') | ~m1_subset_1(C_442, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_736, c_904])).
% 5.24/1.96  tff(c_909, plain, (![D_482, A_483, C_484, C_442]: (r1_tmap_1(D_482, A_483, k2_tmap_1('#skF_5', A_483, C_484, D_482), C_442) | ~r1_tmap_1('#skF_5', A_483, C_484, C_442) | ~r1_tarski('#skF_2'('#skF_5', '#skF_8', C_442), u1_struct_0(D_482)) | ~m1_subset_1(C_442, u1_struct_0(D_482)) | ~m1_subset_1('#skF_2'('#skF_5', '#skF_8', C_442), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc(D_482, '#skF_5') | v2_struct_0(D_482) | ~m1_subset_1(C_484, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(A_483)))) | ~v1_funct_2(C_484, u1_struct_0('#skF_5'), u1_struct_0(A_483)) | ~v1_funct_1(C_484) | v2_struct_0('#skF_5') | ~l1_pre_topc(A_483) | ~v2_pre_topc(A_483) | v2_struct_0(A_483) | ~r2_hidden(C_442, '#skF_8') | ~m1_subset_1(C_442, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_906])).
% 5.24/1.96  tff(c_1136, plain, (![D_532, A_533, C_534, C_535]: (r1_tmap_1(D_532, A_533, k2_tmap_1('#skF_5', A_533, C_534, D_532), C_535) | ~r1_tmap_1('#skF_5', A_533, C_534, C_535) | ~r1_tarski('#skF_2'('#skF_5', '#skF_8', C_535), u1_struct_0(D_532)) | ~m1_subset_1(C_535, u1_struct_0(D_532)) | ~m1_subset_1('#skF_2'('#skF_5', '#skF_8', C_535), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc(D_532, '#skF_5') | v2_struct_0(D_532) | ~m1_subset_1(C_534, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(A_533)))) | ~v1_funct_2(C_534, u1_struct_0('#skF_5'), u1_struct_0(A_533)) | ~v1_funct_1(C_534) | ~l1_pre_topc(A_533) | ~v2_pre_topc(A_533) | v2_struct_0(A_533) | ~r2_hidden(C_535, '#skF_8') | ~m1_subset_1(C_535, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_52, c_909])).
% 5.24/1.96  tff(c_1141, plain, (![A_533, C_534, C_425]: (r1_tmap_1('#skF_7', A_533, k2_tmap_1('#skF_5', A_533, C_534, '#skF_7'), C_425) | ~r1_tmap_1('#skF_5', A_533, C_534, C_425) | ~m1_subset_1(C_425, u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_2'('#skF_5', '#skF_8', C_425), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_7', '#skF_5') | v2_struct_0('#skF_7') | ~m1_subset_1(C_534, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(A_533)))) | ~v1_funct_2(C_534, u1_struct_0('#skF_5'), u1_struct_0(A_533)) | ~v1_funct_1(C_534) | ~l1_pre_topc(A_533) | ~v2_pre_topc(A_533) | v2_struct_0(A_533) | ~r2_hidden(C_425, '#skF_8') | ~m1_subset_1(C_425, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_671, c_1136])).
% 5.24/1.96  tff(c_1148, plain, (![A_533, C_534, C_425]: (r1_tmap_1('#skF_7', A_533, k2_tmap_1('#skF_5', A_533, C_534, '#skF_7'), C_425) | ~r1_tmap_1('#skF_5', A_533, C_534, C_425) | ~m1_subset_1(C_425, u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_2'('#skF_5', '#skF_8', C_425), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_7') | ~m1_subset_1(C_534, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(A_533)))) | ~v1_funct_2(C_534, u1_struct_0('#skF_5'), u1_struct_0(A_533)) | ~v1_funct_1(C_534) | ~l1_pre_topc(A_533) | ~v2_pre_topc(A_533) | v2_struct_0(A_533) | ~r2_hidden(C_425, '#skF_8') | ~m1_subset_1(C_425, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1141])).
% 5.24/1.96  tff(c_1787, plain, (![A_635, C_636, C_637]: (r1_tmap_1('#skF_7', A_635, k2_tmap_1('#skF_5', A_635, C_636, '#skF_7'), C_637) | ~r1_tmap_1('#skF_5', A_635, C_636, C_637) | ~m1_subset_1(C_637, u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_2'('#skF_5', '#skF_8', C_637), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(C_636, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(A_635)))) | ~v1_funct_2(C_636, u1_struct_0('#skF_5'), u1_struct_0(A_635)) | ~v1_funct_1(C_636) | ~l1_pre_topc(A_635) | ~v2_pre_topc(A_635) | v2_struct_0(A_635) | ~r2_hidden(C_637, '#skF_8') | ~m1_subset_1(C_637, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_40, c_1148])).
% 5.24/1.96  tff(c_1790, plain, (![A_635, C_636, C_27]: (r1_tmap_1('#skF_7', A_635, k2_tmap_1('#skF_5', A_635, C_636, '#skF_7'), C_27) | ~r1_tmap_1('#skF_5', A_635, C_636, C_27) | ~m1_subset_1(C_27, u1_struct_0('#skF_7')) | ~m1_subset_1(C_636, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(A_635)))) | ~v1_funct_2(C_636, u1_struct_0('#skF_5'), u1_struct_0(A_635)) | ~v1_funct_1(C_636) | ~l1_pre_topc(A_635) | ~v2_pre_topc(A_635) | v2_struct_0(A_635) | ~r2_hidden(C_27, '#skF_8') | ~m1_subset_1(C_27, u1_struct_0('#skF_5')) | ~v3_pre_topc('#skF_8', '#skF_5') | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_18, c_1787])).
% 5.24/1.96  tff(c_1793, plain, (![A_635, C_636, C_27]: (r1_tmap_1('#skF_7', A_635, k2_tmap_1('#skF_5', A_635, C_636, '#skF_7'), C_27) | ~r1_tmap_1('#skF_5', A_635, C_636, C_27) | ~m1_subset_1(C_27, u1_struct_0('#skF_7')) | ~m1_subset_1(C_636, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(A_635)))) | ~v1_funct_2(C_636, u1_struct_0('#skF_5'), u1_struct_0(A_635)) | ~v1_funct_1(C_636) | ~l1_pre_topc(A_635) | ~v2_pre_topc(A_635) | v2_struct_0(A_635) | ~r2_hidden(C_27, '#skF_8') | ~m1_subset_1(C_27, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_36, c_30, c_1790])).
% 5.24/1.96  tff(c_1795, plain, (![A_638, C_639, C_640]: (r1_tmap_1('#skF_7', A_638, k2_tmap_1('#skF_5', A_638, C_639, '#skF_7'), C_640) | ~r1_tmap_1('#skF_5', A_638, C_639, C_640) | ~m1_subset_1(C_640, u1_struct_0('#skF_7')) | ~m1_subset_1(C_639, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0(A_638)))) | ~v1_funct_2(C_639, u1_struct_0('#skF_5'), u1_struct_0(A_638)) | ~v1_funct_1(C_639) | ~l1_pre_topc(A_638) | ~v2_pre_topc(A_638) | v2_struct_0(A_638) | ~r2_hidden(C_640, '#skF_8') | ~m1_subset_1(C_640, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_52, c_1793])).
% 5.24/1.96  tff(c_1797, plain, (![C_640]: (r1_tmap_1('#skF_7', '#skF_4', k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_7'), C_640) | ~r1_tmap_1('#skF_5', '#skF_4', '#skF_6', C_640) | ~m1_subset_1(C_640, u1_struct_0('#skF_7')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r2_hidden(C_640, '#skF_8') | ~m1_subset_1(C_640, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_42, c_1795])).
% 5.24/1.96  tff(c_1800, plain, (![C_640]: (r1_tmap_1('#skF_7', '#skF_4', k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_7'), C_640) | ~r1_tmap_1('#skF_5', '#skF_4', '#skF_6', C_640) | ~m1_subset_1(C_640, u1_struct_0('#skF_7')) | v2_struct_0('#skF_4') | ~r2_hidden(C_640, '#skF_8') | ~m1_subset_1(C_640, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_46, c_44, c_1797])).
% 5.24/1.96  tff(c_1802, plain, (![C_641]: (r1_tmap_1('#skF_7', '#skF_4', k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_7'), C_641) | ~r1_tmap_1('#skF_5', '#skF_4', '#skF_6', C_641) | ~m1_subset_1(C_641, u1_struct_0('#skF_7')) | ~r2_hidden(C_641, '#skF_8') | ~m1_subset_1(C_641, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_1800])).
% 5.24/1.96  tff(c_499, plain, (~r1_tmap_1('#skF_7', '#skF_4', k2_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_7'), '#skF_9')), inference(splitRight, [status(thm)], [c_67])).
% 5.24/1.96  tff(c_1807, plain, (~r1_tmap_1('#skF_5', '#skF_4', '#skF_6', '#skF_9') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_7')) | ~r2_hidden('#skF_9', '#skF_8') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_1802, c_499])).
% 5.24/1.96  tff(c_1815, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_69, c_498, c_1807])).
% 5.24/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.24/1.96  
% 5.24/1.96  Inference rules
% 5.24/1.96  ----------------------
% 5.24/1.96  #Ref     : 0
% 5.24/1.96  #Sup     : 384
% 5.24/1.96  #Fact    : 0
% 5.24/1.96  #Define  : 0
% 5.24/1.96  #Split   : 8
% 5.24/1.96  #Chain   : 0
% 5.24/1.96  #Close   : 0
% 5.24/1.96  
% 5.24/1.96  Ordering : KBO
% 5.24/1.96  
% 5.24/1.96  Simplification rules
% 5.24/1.96  ----------------------
% 5.24/1.96  #Subsume      : 191
% 5.24/1.96  #Demod        : 262
% 5.24/1.96  #Tautology    : 28
% 5.24/1.96  #SimpNegUnit  : 68
% 5.24/1.96  #BackRed      : 0
% 5.24/1.96  
% 5.24/1.96  #Partial instantiations: 0
% 5.24/1.96  #Strategies tried      : 1
% 5.24/1.96  
% 5.24/1.96  Timing (in seconds)
% 5.24/1.96  ----------------------
% 5.24/1.97  Preprocessing        : 0.35
% 5.24/1.97  Parsing              : 0.17
% 5.24/1.97  CNF conversion       : 0.05
% 5.24/1.97  Main loop            : 0.83
% 5.24/1.97  Inferencing          : 0.29
% 5.24/1.97  Reduction            : 0.24
% 5.24/1.97  Demodulation         : 0.17
% 5.24/1.97  BG Simplification    : 0.03
% 5.24/1.97  Subsumption          : 0.23
% 5.24/1.97  Abstraction          : 0.03
% 5.24/1.97  MUC search           : 0.00
% 5.24/1.97  Cooper               : 0.00
% 5.24/1.97  Total                : 1.24
% 5.24/1.97  Index Insertion      : 0.00
% 5.24/1.97  Index Deletion       : 0.00
% 5.24/1.97  Index Matching       : 0.00
% 5.24/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
