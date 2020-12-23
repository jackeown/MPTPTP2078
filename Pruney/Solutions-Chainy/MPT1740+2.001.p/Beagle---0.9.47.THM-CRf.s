%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:48 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 216 expanded)
%              Number of leaves         :   30 ( 103 expanded)
%              Depth                    :   13
%              Number of atoms          :  344 (1353 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v5_pre_topc > v1_funct_2 > m1_connsp_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k7_relset_1 > k3_funct_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_4 > #skF_7 > #skF_2 > #skF_6 > #skF_5 > #skF_9 > #skF_3 > #skF_1 > #skF_8

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_125,negated_conjecture,(
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
               => ( v5_pre_topc(C,B,A)
                <=> ! [D] :
                      ( m1_subset_1(D,u1_struct_0(B))
                     => r1_tmap_1(B,A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tmap_1)).

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
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v5_pre_topc(C,A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ! [E] :
                        ( m1_connsp_2(E,B,k3_funct_2(u1_struct_0(A),u1_struct_0(B),C,D))
                       => ? [F] :
                            ( m1_connsp_2(F,A,D)
                            & r1_tarski(k7_relset_1(u1_struct_0(A),u1_struct_0(B),C,F),E) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_borsuk_1)).

tff(f_60,axiom,(
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
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r1_tmap_1(A,B,C,D)
                  <=> ! [E] :
                        ( m1_connsp_2(E,B,k3_funct_2(u1_struct_0(A),u1_struct_0(B),C,D))
                       => ? [F] :
                            ( m1_connsp_2(F,A,D)
                            & r1_tarski(k7_relset_1(u1_struct_0(A),u1_struct_0(B),C,F),E) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tmap_1)).

tff(c_30,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_40,plain,
    ( m1_subset_1('#skF_9',u1_struct_0('#skF_7'))
    | ~ v5_pre_topc('#skF_8','#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_49,plain,(
    ~ v5_pre_topc('#skF_8','#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_28,plain,(
    v2_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_26,plain,(
    l1_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_34,plain,(
    v2_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_32,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_24,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_22,plain,(
    v1_funct_2('#skF_8',u1_struct_0('#skF_7'),u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_20,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_57,plain,(
    ! [A_246,B_247,C_248] :
      ( m1_subset_1('#skF_4'(A_246,B_247,C_248),u1_struct_0(A_246))
      | v5_pre_topc(C_248,A_246,B_247)
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_246),u1_struct_0(B_247))))
      | ~ v1_funct_2(C_248,u1_struct_0(A_246),u1_struct_0(B_247))
      | ~ v1_funct_1(C_248)
      | ~ l1_pre_topc(B_247)
      | ~ v2_pre_topc(B_247)
      | v2_struct_0(B_247)
      | ~ l1_pre_topc(A_246)
      | ~ v2_pre_topc(A_246)
      | v2_struct_0(A_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_59,plain,
    ( m1_subset_1('#skF_4'('#skF_7','#skF_6','#skF_8'),u1_struct_0('#skF_7'))
    | v5_pre_topc('#skF_8','#skF_7','#skF_6')
    | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_7'),u1_struct_0('#skF_6'))
    | ~ v1_funct_1('#skF_8')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_20,c_57])).

tff(c_62,plain,
    ( m1_subset_1('#skF_4'('#skF_7','#skF_6','#skF_8'),u1_struct_0('#skF_7'))
    | v5_pre_topc('#skF_8','#skF_7','#skF_6')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_34,c_32,c_24,c_22,c_59])).

tff(c_63,plain,(
    m1_subset_1('#skF_4'('#skF_7','#skF_6','#skF_8'),u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_36,c_49,c_62])).

tff(c_48,plain,(
    ! [D_244] :
      ( v5_pre_topc('#skF_8','#skF_7','#skF_6')
      | r1_tmap_1('#skF_7','#skF_6','#skF_8',D_244)
      | ~ m1_subset_1(D_244,u1_struct_0('#skF_7')) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_51,plain,(
    ! [D_244] :
      ( r1_tmap_1('#skF_7','#skF_6','#skF_8',D_244)
      | ~ m1_subset_1(D_244,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_48])).

tff(c_67,plain,(
    r1_tmap_1('#skF_7','#skF_6','#skF_8','#skF_4'('#skF_7','#skF_6','#skF_8')) ),
    inference(resolution,[status(thm)],[c_63,c_51])).

tff(c_12,plain,(
    ! [A_110,B_170,C_200] :
      ( m1_connsp_2('#skF_5'(A_110,B_170,C_200),B_170,k3_funct_2(u1_struct_0(A_110),u1_struct_0(B_170),C_200,'#skF_4'(A_110,B_170,C_200)))
      | v5_pre_topc(C_200,A_110,B_170)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_110),u1_struct_0(B_170))))
      | ~ v1_funct_2(C_200,u1_struct_0(A_110),u1_struct_0(B_170))
      | ~ v1_funct_1(C_200)
      | ~ l1_pre_topc(B_170)
      | ~ v2_pre_topc(B_170)
      | v2_struct_0(B_170)
      | ~ l1_pre_topc(A_110)
      | ~ v2_pre_topc(A_110)
      | v2_struct_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_79,plain,(
    ! [D_274,C_270,A_273,E_272,B_271] :
      ( m1_connsp_2('#skF_1'(C_270,B_271,E_272,A_273,D_274),A_273,D_274)
      | ~ m1_connsp_2(E_272,B_271,k3_funct_2(u1_struct_0(A_273),u1_struct_0(B_271),C_270,D_274))
      | ~ r1_tmap_1(A_273,B_271,C_270,D_274)
      | ~ m1_subset_1(D_274,u1_struct_0(A_273))
      | ~ m1_subset_1(C_270,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_273),u1_struct_0(B_271))))
      | ~ v1_funct_2(C_270,u1_struct_0(A_273),u1_struct_0(B_271))
      | ~ v1_funct_1(C_270)
      | ~ l1_pre_topc(B_271)
      | ~ v2_pre_topc(B_271)
      | v2_struct_0(B_271)
      | ~ l1_pre_topc(A_273)
      | ~ v2_pre_topc(A_273)
      | v2_struct_0(A_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_85,plain,(
    ! [C_200,B_170,A_110] :
      ( m1_connsp_2('#skF_1'(C_200,B_170,'#skF_5'(A_110,B_170,C_200),A_110,'#skF_4'(A_110,B_170,C_200)),A_110,'#skF_4'(A_110,B_170,C_200))
      | ~ r1_tmap_1(A_110,B_170,C_200,'#skF_4'(A_110,B_170,C_200))
      | ~ m1_subset_1('#skF_4'(A_110,B_170,C_200),u1_struct_0(A_110))
      | v5_pre_topc(C_200,A_110,B_170)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_110),u1_struct_0(B_170))))
      | ~ v1_funct_2(C_200,u1_struct_0(A_110),u1_struct_0(B_170))
      | ~ v1_funct_1(C_200)
      | ~ l1_pre_topc(B_170)
      | ~ v2_pre_topc(B_170)
      | v2_struct_0(B_170)
      | ~ l1_pre_topc(A_110)
      | ~ v2_pre_topc(A_110)
      | v2_struct_0(A_110) ) ),
    inference(resolution,[status(thm)],[c_12,c_79])).

tff(c_104,plain,(
    ! [C_284,B_285,E_286,D_288,A_287] :
      ( r1_tarski(k7_relset_1(u1_struct_0(A_287),u1_struct_0(B_285),C_284,'#skF_1'(C_284,B_285,E_286,A_287,D_288)),E_286)
      | ~ m1_connsp_2(E_286,B_285,k3_funct_2(u1_struct_0(A_287),u1_struct_0(B_285),C_284,D_288))
      | ~ r1_tmap_1(A_287,B_285,C_284,D_288)
      | ~ m1_subset_1(D_288,u1_struct_0(A_287))
      | ~ m1_subset_1(C_284,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_287),u1_struct_0(B_285))))
      | ~ v1_funct_2(C_284,u1_struct_0(A_287),u1_struct_0(B_285))
      | ~ v1_funct_1(C_284)
      | ~ l1_pre_topc(B_285)
      | ~ v2_pre_topc(B_285)
      | v2_struct_0(B_285)
      | ~ l1_pre_topc(A_287)
      | ~ v2_pre_topc(A_287)
      | v2_struct_0(A_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10,plain,(
    ! [A_110,B_170,C_200,F_225] :
      ( ~ r1_tarski(k7_relset_1(u1_struct_0(A_110),u1_struct_0(B_170),C_200,F_225),'#skF_5'(A_110,B_170,C_200))
      | ~ m1_connsp_2(F_225,A_110,'#skF_4'(A_110,B_170,C_200))
      | v5_pre_topc(C_200,A_110,B_170)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_110),u1_struct_0(B_170))))
      | ~ v1_funct_2(C_200,u1_struct_0(A_110),u1_struct_0(B_170))
      | ~ v1_funct_1(C_200)
      | ~ l1_pre_topc(B_170)
      | ~ v2_pre_topc(B_170)
      | v2_struct_0(B_170)
      | ~ l1_pre_topc(A_110)
      | ~ v2_pre_topc(A_110)
      | v2_struct_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_116,plain,(
    ! [C_292,B_293,A_294,D_295] :
      ( ~ m1_connsp_2('#skF_1'(C_292,B_293,'#skF_5'(A_294,B_293,C_292),A_294,D_295),A_294,'#skF_4'(A_294,B_293,C_292))
      | v5_pre_topc(C_292,A_294,B_293)
      | ~ m1_connsp_2('#skF_5'(A_294,B_293,C_292),B_293,k3_funct_2(u1_struct_0(A_294),u1_struct_0(B_293),C_292,D_295))
      | ~ r1_tmap_1(A_294,B_293,C_292,D_295)
      | ~ m1_subset_1(D_295,u1_struct_0(A_294))
      | ~ m1_subset_1(C_292,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_294),u1_struct_0(B_293))))
      | ~ v1_funct_2(C_292,u1_struct_0(A_294),u1_struct_0(B_293))
      | ~ v1_funct_1(C_292)
      | ~ l1_pre_topc(B_293)
      | ~ v2_pre_topc(B_293)
      | v2_struct_0(B_293)
      | ~ l1_pre_topc(A_294)
      | ~ v2_pre_topc(A_294)
      | v2_struct_0(A_294) ) ),
    inference(resolution,[status(thm)],[c_104,c_10])).

tff(c_120,plain,(
    ! [A_296,B_297,C_298] :
      ( ~ m1_connsp_2('#skF_5'(A_296,B_297,C_298),B_297,k3_funct_2(u1_struct_0(A_296),u1_struct_0(B_297),C_298,'#skF_4'(A_296,B_297,C_298)))
      | ~ r1_tmap_1(A_296,B_297,C_298,'#skF_4'(A_296,B_297,C_298))
      | ~ m1_subset_1('#skF_4'(A_296,B_297,C_298),u1_struct_0(A_296))
      | v5_pre_topc(C_298,A_296,B_297)
      | ~ m1_subset_1(C_298,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_296),u1_struct_0(B_297))))
      | ~ v1_funct_2(C_298,u1_struct_0(A_296),u1_struct_0(B_297))
      | ~ v1_funct_1(C_298)
      | ~ l1_pre_topc(B_297)
      | ~ v2_pre_topc(B_297)
      | v2_struct_0(B_297)
      | ~ l1_pre_topc(A_296)
      | ~ v2_pre_topc(A_296)
      | v2_struct_0(A_296) ) ),
    inference(resolution,[status(thm)],[c_85,c_116])).

tff(c_125,plain,(
    ! [A_299,B_300,C_301] :
      ( ~ r1_tmap_1(A_299,B_300,C_301,'#skF_4'(A_299,B_300,C_301))
      | ~ m1_subset_1('#skF_4'(A_299,B_300,C_301),u1_struct_0(A_299))
      | v5_pre_topc(C_301,A_299,B_300)
      | ~ m1_subset_1(C_301,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_299),u1_struct_0(B_300))))
      | ~ v1_funct_2(C_301,u1_struct_0(A_299),u1_struct_0(B_300))
      | ~ v1_funct_1(C_301)
      | ~ l1_pre_topc(B_300)
      | ~ v2_pre_topc(B_300)
      | v2_struct_0(B_300)
      | ~ l1_pre_topc(A_299)
      | ~ v2_pre_topc(A_299)
      | v2_struct_0(A_299) ) ),
    inference(resolution,[status(thm)],[c_12,c_120])).

tff(c_127,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_7','#skF_6','#skF_8'),u1_struct_0('#skF_7'))
    | v5_pre_topc('#skF_8','#skF_7','#skF_6')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_6'))))
    | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_7'),u1_struct_0('#skF_6'))
    | ~ v1_funct_1('#skF_8')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_67,c_125])).

tff(c_130,plain,
    ( v5_pre_topc('#skF_8','#skF_7','#skF_6')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_34,c_32,c_24,c_22,c_20,c_63,c_127])).

tff(c_132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_36,c_49,c_130])).

tff(c_134,plain,(
    v5_pre_topc('#skF_8','#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_38,plain,
    ( ~ r1_tmap_1('#skF_7','#skF_6','#skF_8','#skF_9')
    | ~ v5_pre_topc('#skF_8','#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_136,plain,(
    ~ r1_tmap_1('#skF_7','#skF_6','#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_38])).

tff(c_133,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_4,plain,(
    ! [A_1,B_57,C_85,D_99] :
      ( m1_connsp_2('#skF_2'(A_1,B_57,C_85,D_99),B_57,k3_funct_2(u1_struct_0(A_1),u1_struct_0(B_57),C_85,D_99))
      | r1_tmap_1(A_1,B_57,C_85,D_99)
      | ~ m1_subset_1(D_99,u1_struct_0(A_1))
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1),u1_struct_0(B_57))))
      | ~ v1_funct_2(C_85,u1_struct_0(A_1),u1_struct_0(B_57))
      | ~ v1_funct_1(C_85)
      | ~ l1_pre_topc(B_57)
      | ~ v2_pre_topc(B_57)
      | v2_struct_0(B_57)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_150,plain,(
    ! [B_323,E_324,D_322,A_321,C_325] :
      ( m1_connsp_2('#skF_3'(A_321,D_322,B_323,E_324,C_325),A_321,D_322)
      | ~ m1_connsp_2(E_324,B_323,k3_funct_2(u1_struct_0(A_321),u1_struct_0(B_323),C_325,D_322))
      | ~ m1_subset_1(D_322,u1_struct_0(A_321))
      | ~ v5_pre_topc(C_325,A_321,B_323)
      | ~ m1_subset_1(C_325,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_321),u1_struct_0(B_323))))
      | ~ v1_funct_2(C_325,u1_struct_0(A_321),u1_struct_0(B_323))
      | ~ v1_funct_1(C_325)
      | ~ l1_pre_topc(B_323)
      | ~ v2_pre_topc(B_323)
      | v2_struct_0(B_323)
      | ~ l1_pre_topc(A_321)
      | ~ v2_pre_topc(A_321)
      | v2_struct_0(A_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_164,plain,(
    ! [A_331,D_332,B_333,C_334] :
      ( m1_connsp_2('#skF_3'(A_331,D_332,B_333,'#skF_2'(A_331,B_333,C_334,D_332),C_334),A_331,D_332)
      | ~ v5_pre_topc(C_334,A_331,B_333)
      | r1_tmap_1(A_331,B_333,C_334,D_332)
      | ~ m1_subset_1(D_332,u1_struct_0(A_331))
      | ~ m1_subset_1(C_334,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_331),u1_struct_0(B_333))))
      | ~ v1_funct_2(C_334,u1_struct_0(A_331),u1_struct_0(B_333))
      | ~ v1_funct_1(C_334)
      | ~ l1_pre_topc(B_333)
      | ~ v2_pre_topc(B_333)
      | v2_struct_0(B_333)
      | ~ l1_pre_topc(A_331)
      | ~ v2_pre_topc(A_331)
      | v2_struct_0(A_331) ) ),
    inference(resolution,[status(thm)],[c_4,c_150])).

tff(c_166,plain,(
    ! [D_332] :
      ( m1_connsp_2('#skF_3'('#skF_7',D_332,'#skF_6','#skF_2'('#skF_7','#skF_6','#skF_8',D_332),'#skF_8'),'#skF_7',D_332)
      | ~ v5_pre_topc('#skF_8','#skF_7','#skF_6')
      | r1_tmap_1('#skF_7','#skF_6','#skF_8',D_332)
      | ~ m1_subset_1(D_332,u1_struct_0('#skF_7'))
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_7'),u1_struct_0('#skF_6'))
      | ~ v1_funct_1('#skF_8')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_20,c_164])).

tff(c_169,plain,(
    ! [D_332] :
      ( m1_connsp_2('#skF_3'('#skF_7',D_332,'#skF_6','#skF_2'('#skF_7','#skF_6','#skF_8',D_332),'#skF_8'),'#skF_7',D_332)
      | r1_tmap_1('#skF_7','#skF_6','#skF_8',D_332)
      | ~ m1_subset_1(D_332,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_34,c_32,c_24,c_22,c_134,c_166])).

tff(c_170,plain,(
    ! [D_332] :
      ( m1_connsp_2('#skF_3'('#skF_7',D_332,'#skF_6','#skF_2'('#skF_7','#skF_6','#skF_8',D_332),'#skF_8'),'#skF_7',D_332)
      | r1_tmap_1('#skF_7','#skF_6','#skF_8',D_332)
      | ~ m1_subset_1(D_332,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_36,c_169])).

tff(c_186,plain,(
    ! [E_339,A_336,B_338,D_337,C_340] :
      ( r1_tarski(k7_relset_1(u1_struct_0(A_336),u1_struct_0(B_338),C_340,'#skF_3'(A_336,D_337,B_338,E_339,C_340)),E_339)
      | ~ m1_connsp_2(E_339,B_338,k3_funct_2(u1_struct_0(A_336),u1_struct_0(B_338),C_340,D_337))
      | ~ m1_subset_1(D_337,u1_struct_0(A_336))
      | ~ v5_pre_topc(C_340,A_336,B_338)
      | ~ m1_subset_1(C_340,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_336),u1_struct_0(B_338))))
      | ~ v1_funct_2(C_340,u1_struct_0(A_336),u1_struct_0(B_338))
      | ~ v1_funct_1(C_340)
      | ~ l1_pre_topc(B_338)
      | ~ v2_pre_topc(B_338)
      | v2_struct_0(B_338)
      | ~ l1_pre_topc(A_336)
      | ~ v2_pre_topc(A_336)
      | v2_struct_0(A_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2,plain,(
    ! [C_85,D_99,A_1,F_109,B_57] :
      ( ~ r1_tarski(k7_relset_1(u1_struct_0(A_1),u1_struct_0(B_57),C_85,F_109),'#skF_2'(A_1,B_57,C_85,D_99))
      | ~ m1_connsp_2(F_109,A_1,D_99)
      | r1_tmap_1(A_1,B_57,C_85,D_99)
      | ~ m1_subset_1(D_99,u1_struct_0(A_1))
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1),u1_struct_0(B_57))))
      | ~ v1_funct_2(C_85,u1_struct_0(A_1),u1_struct_0(B_57))
      | ~ v1_funct_1(C_85)
      | ~ l1_pre_topc(B_57)
      | ~ v2_pre_topc(B_57)
      | v2_struct_0(B_57)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_228,plain,(
    ! [C_365,D_366,A_363,D_364,B_362] :
      ( ~ m1_connsp_2('#skF_3'(A_363,D_364,B_362,'#skF_2'(A_363,B_362,C_365,D_366),C_365),A_363,D_366)
      | r1_tmap_1(A_363,B_362,C_365,D_366)
      | ~ m1_subset_1(D_366,u1_struct_0(A_363))
      | ~ m1_connsp_2('#skF_2'(A_363,B_362,C_365,D_366),B_362,k3_funct_2(u1_struct_0(A_363),u1_struct_0(B_362),C_365,D_364))
      | ~ m1_subset_1(D_364,u1_struct_0(A_363))
      | ~ v5_pre_topc(C_365,A_363,B_362)
      | ~ m1_subset_1(C_365,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_363),u1_struct_0(B_362))))
      | ~ v1_funct_2(C_365,u1_struct_0(A_363),u1_struct_0(B_362))
      | ~ v1_funct_1(C_365)
      | ~ l1_pre_topc(B_362)
      | ~ v2_pre_topc(B_362)
      | v2_struct_0(B_362)
      | ~ l1_pre_topc(A_363)
      | ~ v2_pre_topc(A_363)
      | v2_struct_0(A_363) ) ),
    inference(resolution,[status(thm)],[c_186,c_2])).

tff(c_230,plain,(
    ! [D_332] :
      ( ~ m1_connsp_2('#skF_2'('#skF_7','#skF_6','#skF_8',D_332),'#skF_6',k3_funct_2(u1_struct_0('#skF_7'),u1_struct_0('#skF_6'),'#skF_8',D_332))
      | ~ v5_pre_topc('#skF_8','#skF_7','#skF_6')
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_6'))))
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_7'),u1_struct_0('#skF_6'))
      | ~ v1_funct_1('#skF_8')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7')
      | r1_tmap_1('#skF_7','#skF_6','#skF_8',D_332)
      | ~ m1_subset_1(D_332,u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_170,c_228])).

tff(c_233,plain,(
    ! [D_332] :
      ( ~ m1_connsp_2('#skF_2'('#skF_7','#skF_6','#skF_8',D_332),'#skF_6',k3_funct_2(u1_struct_0('#skF_7'),u1_struct_0('#skF_6'),'#skF_8',D_332))
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_7')
      | r1_tmap_1('#skF_7','#skF_6','#skF_8',D_332)
      | ~ m1_subset_1(D_332,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_34,c_32,c_24,c_22,c_20,c_134,c_230])).

tff(c_235,plain,(
    ! [D_367] :
      ( ~ m1_connsp_2('#skF_2'('#skF_7','#skF_6','#skF_8',D_367),'#skF_6',k3_funct_2(u1_struct_0('#skF_7'),u1_struct_0('#skF_6'),'#skF_8',D_367))
      | r1_tmap_1('#skF_7','#skF_6','#skF_8',D_367)
      | ~ m1_subset_1(D_367,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_36,c_233])).

tff(c_239,plain,(
    ! [D_99] :
      ( r1_tmap_1('#skF_7','#skF_6','#skF_8',D_99)
      | ~ m1_subset_1(D_99,u1_struct_0('#skF_7'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_6'))))
      | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_7'),u1_struct_0('#skF_6'))
      | ~ v1_funct_1('#skF_8')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_4,c_235])).

tff(c_242,plain,(
    ! [D_99] :
      ( r1_tmap_1('#skF_7','#skF_6','#skF_8',D_99)
      | ~ m1_subset_1(D_99,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_34,c_32,c_24,c_22,c_20,c_239])).

tff(c_244,plain,(
    ! [D_368] :
      ( r1_tmap_1('#skF_7','#skF_6','#skF_8',D_368)
      | ~ m1_subset_1(D_368,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_36,c_242])).

tff(c_247,plain,(
    r1_tmap_1('#skF_7','#skF_6','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_133,c_244])).

tff(c_251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_247])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:14:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.46  
% 2.45/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.46  %$ r1_tmap_1 > v5_pre_topc > v1_funct_2 > m1_connsp_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k7_relset_1 > k3_funct_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_4 > #skF_7 > #skF_2 > #skF_6 > #skF_5 > #skF_9 > #skF_3 > #skF_1 > #skF_8
% 2.83/1.46  
% 2.83/1.46  %Foreground sorts:
% 2.83/1.46  
% 2.83/1.46  
% 2.83/1.46  %Background operators:
% 2.83/1.46  
% 2.83/1.46  
% 2.83/1.46  %Foreground operators:
% 2.83/1.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.83/1.46  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 2.83/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.83/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.46  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 2.83/1.46  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.83/1.46  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.83/1.46  tff('#skF_7', type, '#skF_7': $i).
% 2.83/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.83/1.46  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.83/1.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.83/1.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.83/1.46  tff('#skF_6', type, '#skF_6': $i).
% 2.83/1.46  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.83/1.46  tff('#skF_9', type, '#skF_9': $i).
% 2.83/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.83/1.46  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 2.83/1.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 2.83/1.46  tff('#skF_8', type, '#skF_8': $i).
% 2.83/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.83/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.46  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 2.83/1.46  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.83/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.83/1.46  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.83/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.83/1.46  
% 2.90/1.48  tff(f_125, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (v5_pre_topc(C, B, A) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => r1_tmap_1(B, A, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tmap_1)).
% 2.90/1.48  tff(f_95, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v5_pre_topc(C, A, B) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (![E]: (m1_connsp_2(E, B, k3_funct_2(u1_struct_0(A), u1_struct_0(B), C, D)) => (?[F]: (m1_connsp_2(F, A, D) & r1_tarski(k7_relset_1(u1_struct_0(A), u1_struct_0(B), C, F), E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_borsuk_1)).
% 2.90/1.48  tff(f_60, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_tmap_1(A, B, C, D) <=> (![E]: (m1_connsp_2(E, B, k3_funct_2(u1_struct_0(A), u1_struct_0(B), C, D)) => (?[F]: (m1_connsp_2(F, A, D) & r1_tarski(k7_relset_1(u1_struct_0(A), u1_struct_0(B), C, F), E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tmap_1)).
% 2.90/1.48  tff(c_30, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.90/1.48  tff(c_36, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.90/1.48  tff(c_40, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_7')) | ~v5_pre_topc('#skF_8', '#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.90/1.48  tff(c_49, plain, (~v5_pre_topc('#skF_8', '#skF_7', '#skF_6')), inference(splitLeft, [status(thm)], [c_40])).
% 2.90/1.48  tff(c_28, plain, (v2_pre_topc('#skF_7')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.90/1.48  tff(c_26, plain, (l1_pre_topc('#skF_7')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.90/1.48  tff(c_34, plain, (v2_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.90/1.48  tff(c_32, plain, (l1_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.90/1.48  tff(c_24, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.90/1.48  tff(c_22, plain, (v1_funct_2('#skF_8', u1_struct_0('#skF_7'), u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.90/1.48  tff(c_20, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'), u1_struct_0('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.90/1.48  tff(c_57, plain, (![A_246, B_247, C_248]: (m1_subset_1('#skF_4'(A_246, B_247, C_248), u1_struct_0(A_246)) | v5_pre_topc(C_248, A_246, B_247) | ~m1_subset_1(C_248, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_246), u1_struct_0(B_247)))) | ~v1_funct_2(C_248, u1_struct_0(A_246), u1_struct_0(B_247)) | ~v1_funct_1(C_248) | ~l1_pre_topc(B_247) | ~v2_pre_topc(B_247) | v2_struct_0(B_247) | ~l1_pre_topc(A_246) | ~v2_pre_topc(A_246) | v2_struct_0(A_246))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.90/1.48  tff(c_59, plain, (m1_subset_1('#skF_4'('#skF_7', '#skF_6', '#skF_8'), u1_struct_0('#skF_7')) | v5_pre_topc('#skF_8', '#skF_7', '#skF_6') | ~v1_funct_2('#skF_8', u1_struct_0('#skF_7'), u1_struct_0('#skF_6')) | ~v1_funct_1('#skF_8') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_20, c_57])).
% 2.90/1.48  tff(c_62, plain, (m1_subset_1('#skF_4'('#skF_7', '#skF_6', '#skF_8'), u1_struct_0('#skF_7')) | v5_pre_topc('#skF_8', '#skF_7', '#skF_6') | v2_struct_0('#skF_6') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_34, c_32, c_24, c_22, c_59])).
% 2.90/1.48  tff(c_63, plain, (m1_subset_1('#skF_4'('#skF_7', '#skF_6', '#skF_8'), u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_30, c_36, c_49, c_62])).
% 2.90/1.48  tff(c_48, plain, (![D_244]: (v5_pre_topc('#skF_8', '#skF_7', '#skF_6') | r1_tmap_1('#skF_7', '#skF_6', '#skF_8', D_244) | ~m1_subset_1(D_244, u1_struct_0('#skF_7')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.90/1.48  tff(c_51, plain, (![D_244]: (r1_tmap_1('#skF_7', '#skF_6', '#skF_8', D_244) | ~m1_subset_1(D_244, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_49, c_48])).
% 2.90/1.48  tff(c_67, plain, (r1_tmap_1('#skF_7', '#skF_6', '#skF_8', '#skF_4'('#skF_7', '#skF_6', '#skF_8'))), inference(resolution, [status(thm)], [c_63, c_51])).
% 2.90/1.48  tff(c_12, plain, (![A_110, B_170, C_200]: (m1_connsp_2('#skF_5'(A_110, B_170, C_200), B_170, k3_funct_2(u1_struct_0(A_110), u1_struct_0(B_170), C_200, '#skF_4'(A_110, B_170, C_200))) | v5_pre_topc(C_200, A_110, B_170) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_110), u1_struct_0(B_170)))) | ~v1_funct_2(C_200, u1_struct_0(A_110), u1_struct_0(B_170)) | ~v1_funct_1(C_200) | ~l1_pre_topc(B_170) | ~v2_pre_topc(B_170) | v2_struct_0(B_170) | ~l1_pre_topc(A_110) | ~v2_pre_topc(A_110) | v2_struct_0(A_110))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.90/1.48  tff(c_79, plain, (![D_274, C_270, A_273, E_272, B_271]: (m1_connsp_2('#skF_1'(C_270, B_271, E_272, A_273, D_274), A_273, D_274) | ~m1_connsp_2(E_272, B_271, k3_funct_2(u1_struct_0(A_273), u1_struct_0(B_271), C_270, D_274)) | ~r1_tmap_1(A_273, B_271, C_270, D_274) | ~m1_subset_1(D_274, u1_struct_0(A_273)) | ~m1_subset_1(C_270, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_273), u1_struct_0(B_271)))) | ~v1_funct_2(C_270, u1_struct_0(A_273), u1_struct_0(B_271)) | ~v1_funct_1(C_270) | ~l1_pre_topc(B_271) | ~v2_pre_topc(B_271) | v2_struct_0(B_271) | ~l1_pre_topc(A_273) | ~v2_pre_topc(A_273) | v2_struct_0(A_273))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.90/1.48  tff(c_85, plain, (![C_200, B_170, A_110]: (m1_connsp_2('#skF_1'(C_200, B_170, '#skF_5'(A_110, B_170, C_200), A_110, '#skF_4'(A_110, B_170, C_200)), A_110, '#skF_4'(A_110, B_170, C_200)) | ~r1_tmap_1(A_110, B_170, C_200, '#skF_4'(A_110, B_170, C_200)) | ~m1_subset_1('#skF_4'(A_110, B_170, C_200), u1_struct_0(A_110)) | v5_pre_topc(C_200, A_110, B_170) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_110), u1_struct_0(B_170)))) | ~v1_funct_2(C_200, u1_struct_0(A_110), u1_struct_0(B_170)) | ~v1_funct_1(C_200) | ~l1_pre_topc(B_170) | ~v2_pre_topc(B_170) | v2_struct_0(B_170) | ~l1_pre_topc(A_110) | ~v2_pre_topc(A_110) | v2_struct_0(A_110))), inference(resolution, [status(thm)], [c_12, c_79])).
% 2.90/1.48  tff(c_104, plain, (![C_284, B_285, E_286, D_288, A_287]: (r1_tarski(k7_relset_1(u1_struct_0(A_287), u1_struct_0(B_285), C_284, '#skF_1'(C_284, B_285, E_286, A_287, D_288)), E_286) | ~m1_connsp_2(E_286, B_285, k3_funct_2(u1_struct_0(A_287), u1_struct_0(B_285), C_284, D_288)) | ~r1_tmap_1(A_287, B_285, C_284, D_288) | ~m1_subset_1(D_288, u1_struct_0(A_287)) | ~m1_subset_1(C_284, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_287), u1_struct_0(B_285)))) | ~v1_funct_2(C_284, u1_struct_0(A_287), u1_struct_0(B_285)) | ~v1_funct_1(C_284) | ~l1_pre_topc(B_285) | ~v2_pre_topc(B_285) | v2_struct_0(B_285) | ~l1_pre_topc(A_287) | ~v2_pre_topc(A_287) | v2_struct_0(A_287))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.90/1.48  tff(c_10, plain, (![A_110, B_170, C_200, F_225]: (~r1_tarski(k7_relset_1(u1_struct_0(A_110), u1_struct_0(B_170), C_200, F_225), '#skF_5'(A_110, B_170, C_200)) | ~m1_connsp_2(F_225, A_110, '#skF_4'(A_110, B_170, C_200)) | v5_pre_topc(C_200, A_110, B_170) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_110), u1_struct_0(B_170)))) | ~v1_funct_2(C_200, u1_struct_0(A_110), u1_struct_0(B_170)) | ~v1_funct_1(C_200) | ~l1_pre_topc(B_170) | ~v2_pre_topc(B_170) | v2_struct_0(B_170) | ~l1_pre_topc(A_110) | ~v2_pre_topc(A_110) | v2_struct_0(A_110))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.90/1.48  tff(c_116, plain, (![C_292, B_293, A_294, D_295]: (~m1_connsp_2('#skF_1'(C_292, B_293, '#skF_5'(A_294, B_293, C_292), A_294, D_295), A_294, '#skF_4'(A_294, B_293, C_292)) | v5_pre_topc(C_292, A_294, B_293) | ~m1_connsp_2('#skF_5'(A_294, B_293, C_292), B_293, k3_funct_2(u1_struct_0(A_294), u1_struct_0(B_293), C_292, D_295)) | ~r1_tmap_1(A_294, B_293, C_292, D_295) | ~m1_subset_1(D_295, u1_struct_0(A_294)) | ~m1_subset_1(C_292, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_294), u1_struct_0(B_293)))) | ~v1_funct_2(C_292, u1_struct_0(A_294), u1_struct_0(B_293)) | ~v1_funct_1(C_292) | ~l1_pre_topc(B_293) | ~v2_pre_topc(B_293) | v2_struct_0(B_293) | ~l1_pre_topc(A_294) | ~v2_pre_topc(A_294) | v2_struct_0(A_294))), inference(resolution, [status(thm)], [c_104, c_10])).
% 2.90/1.48  tff(c_120, plain, (![A_296, B_297, C_298]: (~m1_connsp_2('#skF_5'(A_296, B_297, C_298), B_297, k3_funct_2(u1_struct_0(A_296), u1_struct_0(B_297), C_298, '#skF_4'(A_296, B_297, C_298))) | ~r1_tmap_1(A_296, B_297, C_298, '#skF_4'(A_296, B_297, C_298)) | ~m1_subset_1('#skF_4'(A_296, B_297, C_298), u1_struct_0(A_296)) | v5_pre_topc(C_298, A_296, B_297) | ~m1_subset_1(C_298, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_296), u1_struct_0(B_297)))) | ~v1_funct_2(C_298, u1_struct_0(A_296), u1_struct_0(B_297)) | ~v1_funct_1(C_298) | ~l1_pre_topc(B_297) | ~v2_pre_topc(B_297) | v2_struct_0(B_297) | ~l1_pre_topc(A_296) | ~v2_pre_topc(A_296) | v2_struct_0(A_296))), inference(resolution, [status(thm)], [c_85, c_116])).
% 2.90/1.48  tff(c_125, plain, (![A_299, B_300, C_301]: (~r1_tmap_1(A_299, B_300, C_301, '#skF_4'(A_299, B_300, C_301)) | ~m1_subset_1('#skF_4'(A_299, B_300, C_301), u1_struct_0(A_299)) | v5_pre_topc(C_301, A_299, B_300) | ~m1_subset_1(C_301, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_299), u1_struct_0(B_300)))) | ~v1_funct_2(C_301, u1_struct_0(A_299), u1_struct_0(B_300)) | ~v1_funct_1(C_301) | ~l1_pre_topc(B_300) | ~v2_pre_topc(B_300) | v2_struct_0(B_300) | ~l1_pre_topc(A_299) | ~v2_pre_topc(A_299) | v2_struct_0(A_299))), inference(resolution, [status(thm)], [c_12, c_120])).
% 2.90/1.48  tff(c_127, plain, (~m1_subset_1('#skF_4'('#skF_7', '#skF_6', '#skF_8'), u1_struct_0('#skF_7')) | v5_pre_topc('#skF_8', '#skF_7', '#skF_6') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'), u1_struct_0('#skF_6')))) | ~v1_funct_2('#skF_8', u1_struct_0('#skF_7'), u1_struct_0('#skF_6')) | ~v1_funct_1('#skF_8') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_67, c_125])).
% 2.90/1.48  tff(c_130, plain, (v5_pre_topc('#skF_8', '#skF_7', '#skF_6') | v2_struct_0('#skF_6') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_34, c_32, c_24, c_22, c_20, c_63, c_127])).
% 2.90/1.48  tff(c_132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_36, c_49, c_130])).
% 2.90/1.48  tff(c_134, plain, (v5_pre_topc('#skF_8', '#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_40])).
% 2.90/1.48  tff(c_38, plain, (~r1_tmap_1('#skF_7', '#skF_6', '#skF_8', '#skF_9') | ~v5_pre_topc('#skF_8', '#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.90/1.48  tff(c_136, plain, (~r1_tmap_1('#skF_7', '#skF_6', '#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_38])).
% 2.90/1.48  tff(c_133, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_40])).
% 2.90/1.48  tff(c_4, plain, (![A_1, B_57, C_85, D_99]: (m1_connsp_2('#skF_2'(A_1, B_57, C_85, D_99), B_57, k3_funct_2(u1_struct_0(A_1), u1_struct_0(B_57), C_85, D_99)) | r1_tmap_1(A_1, B_57, C_85, D_99) | ~m1_subset_1(D_99, u1_struct_0(A_1)) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1), u1_struct_0(B_57)))) | ~v1_funct_2(C_85, u1_struct_0(A_1), u1_struct_0(B_57)) | ~v1_funct_1(C_85) | ~l1_pre_topc(B_57) | ~v2_pre_topc(B_57) | v2_struct_0(B_57) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.90/1.48  tff(c_150, plain, (![B_323, E_324, D_322, A_321, C_325]: (m1_connsp_2('#skF_3'(A_321, D_322, B_323, E_324, C_325), A_321, D_322) | ~m1_connsp_2(E_324, B_323, k3_funct_2(u1_struct_0(A_321), u1_struct_0(B_323), C_325, D_322)) | ~m1_subset_1(D_322, u1_struct_0(A_321)) | ~v5_pre_topc(C_325, A_321, B_323) | ~m1_subset_1(C_325, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_321), u1_struct_0(B_323)))) | ~v1_funct_2(C_325, u1_struct_0(A_321), u1_struct_0(B_323)) | ~v1_funct_1(C_325) | ~l1_pre_topc(B_323) | ~v2_pre_topc(B_323) | v2_struct_0(B_323) | ~l1_pre_topc(A_321) | ~v2_pre_topc(A_321) | v2_struct_0(A_321))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.90/1.48  tff(c_164, plain, (![A_331, D_332, B_333, C_334]: (m1_connsp_2('#skF_3'(A_331, D_332, B_333, '#skF_2'(A_331, B_333, C_334, D_332), C_334), A_331, D_332) | ~v5_pre_topc(C_334, A_331, B_333) | r1_tmap_1(A_331, B_333, C_334, D_332) | ~m1_subset_1(D_332, u1_struct_0(A_331)) | ~m1_subset_1(C_334, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_331), u1_struct_0(B_333)))) | ~v1_funct_2(C_334, u1_struct_0(A_331), u1_struct_0(B_333)) | ~v1_funct_1(C_334) | ~l1_pre_topc(B_333) | ~v2_pre_topc(B_333) | v2_struct_0(B_333) | ~l1_pre_topc(A_331) | ~v2_pre_topc(A_331) | v2_struct_0(A_331))), inference(resolution, [status(thm)], [c_4, c_150])).
% 2.90/1.48  tff(c_166, plain, (![D_332]: (m1_connsp_2('#skF_3'('#skF_7', D_332, '#skF_6', '#skF_2'('#skF_7', '#skF_6', '#skF_8', D_332), '#skF_8'), '#skF_7', D_332) | ~v5_pre_topc('#skF_8', '#skF_7', '#skF_6') | r1_tmap_1('#skF_7', '#skF_6', '#skF_8', D_332) | ~m1_subset_1(D_332, u1_struct_0('#skF_7')) | ~v1_funct_2('#skF_8', u1_struct_0('#skF_7'), u1_struct_0('#skF_6')) | ~v1_funct_1('#skF_8') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_20, c_164])).
% 2.90/1.48  tff(c_169, plain, (![D_332]: (m1_connsp_2('#skF_3'('#skF_7', D_332, '#skF_6', '#skF_2'('#skF_7', '#skF_6', '#skF_8', D_332), '#skF_8'), '#skF_7', D_332) | r1_tmap_1('#skF_7', '#skF_6', '#skF_8', D_332) | ~m1_subset_1(D_332, u1_struct_0('#skF_7')) | v2_struct_0('#skF_6') | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_34, c_32, c_24, c_22, c_134, c_166])).
% 2.90/1.48  tff(c_170, plain, (![D_332]: (m1_connsp_2('#skF_3'('#skF_7', D_332, '#skF_6', '#skF_2'('#skF_7', '#skF_6', '#skF_8', D_332), '#skF_8'), '#skF_7', D_332) | r1_tmap_1('#skF_7', '#skF_6', '#skF_8', D_332) | ~m1_subset_1(D_332, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_30, c_36, c_169])).
% 2.90/1.48  tff(c_186, plain, (![E_339, A_336, B_338, D_337, C_340]: (r1_tarski(k7_relset_1(u1_struct_0(A_336), u1_struct_0(B_338), C_340, '#skF_3'(A_336, D_337, B_338, E_339, C_340)), E_339) | ~m1_connsp_2(E_339, B_338, k3_funct_2(u1_struct_0(A_336), u1_struct_0(B_338), C_340, D_337)) | ~m1_subset_1(D_337, u1_struct_0(A_336)) | ~v5_pre_topc(C_340, A_336, B_338) | ~m1_subset_1(C_340, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_336), u1_struct_0(B_338)))) | ~v1_funct_2(C_340, u1_struct_0(A_336), u1_struct_0(B_338)) | ~v1_funct_1(C_340) | ~l1_pre_topc(B_338) | ~v2_pre_topc(B_338) | v2_struct_0(B_338) | ~l1_pre_topc(A_336) | ~v2_pre_topc(A_336) | v2_struct_0(A_336))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.90/1.48  tff(c_2, plain, (![C_85, D_99, A_1, F_109, B_57]: (~r1_tarski(k7_relset_1(u1_struct_0(A_1), u1_struct_0(B_57), C_85, F_109), '#skF_2'(A_1, B_57, C_85, D_99)) | ~m1_connsp_2(F_109, A_1, D_99) | r1_tmap_1(A_1, B_57, C_85, D_99) | ~m1_subset_1(D_99, u1_struct_0(A_1)) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1), u1_struct_0(B_57)))) | ~v1_funct_2(C_85, u1_struct_0(A_1), u1_struct_0(B_57)) | ~v1_funct_1(C_85) | ~l1_pre_topc(B_57) | ~v2_pre_topc(B_57) | v2_struct_0(B_57) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.90/1.48  tff(c_228, plain, (![C_365, D_366, A_363, D_364, B_362]: (~m1_connsp_2('#skF_3'(A_363, D_364, B_362, '#skF_2'(A_363, B_362, C_365, D_366), C_365), A_363, D_366) | r1_tmap_1(A_363, B_362, C_365, D_366) | ~m1_subset_1(D_366, u1_struct_0(A_363)) | ~m1_connsp_2('#skF_2'(A_363, B_362, C_365, D_366), B_362, k3_funct_2(u1_struct_0(A_363), u1_struct_0(B_362), C_365, D_364)) | ~m1_subset_1(D_364, u1_struct_0(A_363)) | ~v5_pre_topc(C_365, A_363, B_362) | ~m1_subset_1(C_365, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_363), u1_struct_0(B_362)))) | ~v1_funct_2(C_365, u1_struct_0(A_363), u1_struct_0(B_362)) | ~v1_funct_1(C_365) | ~l1_pre_topc(B_362) | ~v2_pre_topc(B_362) | v2_struct_0(B_362) | ~l1_pre_topc(A_363) | ~v2_pre_topc(A_363) | v2_struct_0(A_363))), inference(resolution, [status(thm)], [c_186, c_2])).
% 2.90/1.48  tff(c_230, plain, (![D_332]: (~m1_connsp_2('#skF_2'('#skF_7', '#skF_6', '#skF_8', D_332), '#skF_6', k3_funct_2(u1_struct_0('#skF_7'), u1_struct_0('#skF_6'), '#skF_8', D_332)) | ~v5_pre_topc('#skF_8', '#skF_7', '#skF_6') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'), u1_struct_0('#skF_6')))) | ~v1_funct_2('#skF_8', u1_struct_0('#skF_7'), u1_struct_0('#skF_6')) | ~v1_funct_1('#skF_8') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7') | r1_tmap_1('#skF_7', '#skF_6', '#skF_8', D_332) | ~m1_subset_1(D_332, u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_170, c_228])).
% 2.90/1.48  tff(c_233, plain, (![D_332]: (~m1_connsp_2('#skF_2'('#skF_7', '#skF_6', '#skF_8', D_332), '#skF_6', k3_funct_2(u1_struct_0('#skF_7'), u1_struct_0('#skF_6'), '#skF_8', D_332)) | v2_struct_0('#skF_6') | v2_struct_0('#skF_7') | r1_tmap_1('#skF_7', '#skF_6', '#skF_8', D_332) | ~m1_subset_1(D_332, u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_34, c_32, c_24, c_22, c_20, c_134, c_230])).
% 2.90/1.48  tff(c_235, plain, (![D_367]: (~m1_connsp_2('#skF_2'('#skF_7', '#skF_6', '#skF_8', D_367), '#skF_6', k3_funct_2(u1_struct_0('#skF_7'), u1_struct_0('#skF_6'), '#skF_8', D_367)) | r1_tmap_1('#skF_7', '#skF_6', '#skF_8', D_367) | ~m1_subset_1(D_367, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_30, c_36, c_233])).
% 2.90/1.48  tff(c_239, plain, (![D_99]: (r1_tmap_1('#skF_7', '#skF_6', '#skF_8', D_99) | ~m1_subset_1(D_99, u1_struct_0('#skF_7')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'), u1_struct_0('#skF_6')))) | ~v1_funct_2('#skF_8', u1_struct_0('#skF_7'), u1_struct_0('#skF_6')) | ~v1_funct_1('#skF_8') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_4, c_235])).
% 2.90/1.48  tff(c_242, plain, (![D_99]: (r1_tmap_1('#skF_7', '#skF_6', '#skF_8', D_99) | ~m1_subset_1(D_99, u1_struct_0('#skF_7')) | v2_struct_0('#skF_6') | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_34, c_32, c_24, c_22, c_20, c_239])).
% 2.90/1.48  tff(c_244, plain, (![D_368]: (r1_tmap_1('#skF_7', '#skF_6', '#skF_8', D_368) | ~m1_subset_1(D_368, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_30, c_36, c_242])).
% 2.90/1.48  tff(c_247, plain, (r1_tmap_1('#skF_7', '#skF_6', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_133, c_244])).
% 2.90/1.48  tff(c_251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_136, c_247])).
% 2.90/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.48  
% 2.90/1.48  Inference rules
% 2.90/1.48  ----------------------
% 2.90/1.48  #Ref     : 0
% 2.90/1.48  #Sup     : 34
% 2.90/1.48  #Fact    : 0
% 2.90/1.48  #Define  : 0
% 2.90/1.48  #Split   : 2
% 2.90/1.48  #Chain   : 0
% 2.90/1.48  #Close   : 0
% 2.90/1.48  
% 2.90/1.48  Ordering : KBO
% 2.90/1.48  
% 2.90/1.48  Simplification rules
% 2.90/1.48  ----------------------
% 2.90/1.48  #Subsume      : 11
% 2.90/1.48  #Demod        : 56
% 2.90/1.48  #Tautology    : 10
% 2.90/1.48  #SimpNegUnit  : 11
% 2.90/1.48  #BackRed      : 0
% 2.90/1.48  
% 2.90/1.48  #Partial instantiations: 0
% 2.90/1.48  #Strategies tried      : 1
% 2.90/1.48  
% 2.90/1.48  Timing (in seconds)
% 2.90/1.48  ----------------------
% 2.90/1.48  Preprocessing        : 0.34
% 2.90/1.48  Parsing              : 0.18
% 2.90/1.48  CNF conversion       : 0.05
% 2.90/1.48  Main loop            : 0.29
% 2.90/1.48  Inferencing          : 0.13
% 2.90/1.48  Reduction            : 0.07
% 2.90/1.49  Demodulation         : 0.05
% 2.90/1.49  BG Simplification    : 0.02
% 2.90/1.49  Subsumption          : 0.04
% 2.90/1.49  Abstraction          : 0.01
% 2.90/1.49  MUC search           : 0.00
% 2.90/1.49  Cooper               : 0.00
% 2.90/1.49  Total                : 0.67
% 2.90/1.49  Index Insertion      : 0.00
% 2.90/1.49  Index Deletion       : 0.00
% 2.90/1.49  Index Matching       : 0.00
% 2.90/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
