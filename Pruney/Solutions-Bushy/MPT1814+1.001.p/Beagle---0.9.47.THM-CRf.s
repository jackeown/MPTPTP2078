%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1814+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:27 EST 2020

% Result     : Theorem 4.94s
% Output     : CNFRefutation 5.34s
% Verified   : 
% Statistics : Number of formulae       :  229 (1152 expanded)
%              Number of leaves         :   26 ( 463 expanded)
%              Depth                    :   12
%              Number of atoms          : 1010 (13378 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   29 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > r4_tsep_1 > v1_borsuk_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r4_tsep_1,type,(
    r4_tsep_1: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

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

tff(v1_borsuk_1,type,(
    v1_borsuk_1: ( $i * $i ) > $o )).

tff(f_166,negated_conjecture,(
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
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & v1_borsuk_1(D,A)
                      & m1_pre_topc(D,A) )
                   => ! [E] :
                        ( ( ~ v2_struct_0(E)
                          & v1_borsuk_1(E,A)
                          & m1_pre_topc(E,A) )
                       => ( ( v1_funct_1(k2_tmap_1(A,B,C,k1_tsep_1(A,D,E)))
                            & v1_funct_2(k2_tmap_1(A,B,C,k1_tsep_1(A,D,E)),u1_struct_0(k1_tsep_1(A,D,E)),u1_struct_0(B))
                            & v5_pre_topc(k2_tmap_1(A,B,C,k1_tsep_1(A,D,E)),k1_tsep_1(A,D,E),B)
                            & m1_subset_1(k2_tmap_1(A,B,C,k1_tsep_1(A,D,E)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,D,E)),u1_struct_0(B)))) )
                        <=> ( v1_funct_1(k2_tmap_1(A,B,C,D))
                            & v1_funct_2(k2_tmap_1(A,B,C,D),u1_struct_0(D),u1_struct_0(B))
                            & v5_pre_topc(k2_tmap_1(A,B,C,D),D,B)
                            & m1_subset_1(k2_tmap_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B))))
                            & v1_funct_1(k2_tmap_1(A,B,C,E))
                            & v1_funct_2(k2_tmap_1(A,B,C,E),u1_struct_0(E),u1_struct_0(B))
                            & v5_pre_topc(k2_tmap_1(A,B,C,E),E,B)
                            & m1_subset_1(k2_tmap_1(A,B,C,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(E),u1_struct_0(B)))) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_tmap_1)).

tff(f_103,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_borsuk_1(B,A)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( v1_borsuk_1(C,A)
                & m1_pre_topc(C,A) )
             => r4_tsep_1(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_tsep_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ( r4_tsep_1(A,C,D)
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                       => ( ( v1_funct_1(k2_tmap_1(A,B,E,k1_tsep_1(A,C,D)))
                            & v1_funct_2(k2_tmap_1(A,B,E,k1_tsep_1(A,C,D)),u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
                            & v5_pre_topc(k2_tmap_1(A,B,E,k1_tsep_1(A,C,D)),k1_tsep_1(A,C,D),B)
                            & m1_subset_1(k2_tmap_1(A,B,E,k1_tsep_1(A,C,D)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) )
                        <=> ( v1_funct_1(k2_tmap_1(A,B,E,C))
                            & v1_funct_2(k2_tmap_1(A,B,E,C),u1_struct_0(C),u1_struct_0(B))
                            & v5_pre_topc(k2_tmap_1(A,B,E,C),C,B)
                            & m1_subset_1(k2_tmap_1(A,B,E,C),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B))))
                            & v1_funct_1(k2_tmap_1(A,B,E,D))
                            & v1_funct_2(k2_tmap_1(A,B,E,D),u1_struct_0(D),u1_struct_0(B))
                            & v5_pre_topc(k2_tmap_1(A,B,E,D),D,B)
                            & m1_subset_1(k2_tmap_1(A,B,E,D),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_tmap_1)).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_36,plain,(
    v1_borsuk_1('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_34,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_30,plain,(
    v1_borsuk_1('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_28,plain,(
    m1_pre_topc('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_26,plain,(
    ! [A_32,B_36,C_38] :
      ( r4_tsep_1(A_32,B_36,C_38)
      | ~ m1_pre_topc(C_38,A_32)
      | ~ v1_borsuk_1(C_38,A_32)
      | ~ m1_pre_topc(B_36,A_32)
      | ~ v1_borsuk_1(B_36,A_32)
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_44,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_42,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_146,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')))
    | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_148,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_136,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')))
    | v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_152,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_126,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')))
    | v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_150,plain,(
    v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_116,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')))
    | m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_155,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_106,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')))
    | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_147,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_96,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')))
    | v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_151,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_86,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')))
    | v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_149,plain,(
    v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_76,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')))
    | m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_156,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_621,plain,(
    ! [D_205,C_206,E_209,A_208,B_207] :
      ( v1_funct_2(k2_tmap_1(A_208,B_207,E_209,k1_tsep_1(A_208,C_206,D_205)),u1_struct_0(k1_tsep_1(A_208,C_206,D_205)),u1_struct_0(B_207))
      | ~ m1_subset_1(k2_tmap_1(A_208,B_207,E_209,D_205),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_205),u1_struct_0(B_207))))
      | ~ v5_pre_topc(k2_tmap_1(A_208,B_207,E_209,D_205),D_205,B_207)
      | ~ v1_funct_2(k2_tmap_1(A_208,B_207,E_209,D_205),u1_struct_0(D_205),u1_struct_0(B_207))
      | ~ v1_funct_1(k2_tmap_1(A_208,B_207,E_209,D_205))
      | ~ m1_subset_1(k2_tmap_1(A_208,B_207,E_209,C_206),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_206),u1_struct_0(B_207))))
      | ~ v5_pre_topc(k2_tmap_1(A_208,B_207,E_209,C_206),C_206,B_207)
      | ~ v1_funct_2(k2_tmap_1(A_208,B_207,E_209,C_206),u1_struct_0(C_206),u1_struct_0(B_207))
      | ~ v1_funct_1(k2_tmap_1(A_208,B_207,E_209,C_206))
      | ~ m1_subset_1(E_209,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_208),u1_struct_0(B_207))))
      | ~ v1_funct_2(E_209,u1_struct_0(A_208),u1_struct_0(B_207))
      | ~ v1_funct_1(E_209)
      | ~ r4_tsep_1(A_208,C_206,D_205)
      | ~ m1_pre_topc(D_205,A_208)
      | v2_struct_0(D_205)
      | ~ m1_pre_topc(C_206,A_208)
      | v2_struct_0(C_206)
      | ~ l1_pre_topc(B_207)
      | ~ v2_pre_topc(B_207)
      | v2_struct_0(B_207)
      | ~ l1_pre_topc(A_208)
      | ~ v2_pre_topc(A_208)
      | v2_struct_0(A_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_324,plain,(
    ! [E_155,C_152,A_154,D_151,B_153] :
      ( v5_pre_topc(k2_tmap_1(A_154,B_153,E_155,k1_tsep_1(A_154,C_152,D_151)),k1_tsep_1(A_154,C_152,D_151),B_153)
      | ~ m1_subset_1(k2_tmap_1(A_154,B_153,E_155,D_151),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_151),u1_struct_0(B_153))))
      | ~ v5_pre_topc(k2_tmap_1(A_154,B_153,E_155,D_151),D_151,B_153)
      | ~ v1_funct_2(k2_tmap_1(A_154,B_153,E_155,D_151),u1_struct_0(D_151),u1_struct_0(B_153))
      | ~ v1_funct_1(k2_tmap_1(A_154,B_153,E_155,D_151))
      | ~ m1_subset_1(k2_tmap_1(A_154,B_153,E_155,C_152),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_152),u1_struct_0(B_153))))
      | ~ v5_pre_topc(k2_tmap_1(A_154,B_153,E_155,C_152),C_152,B_153)
      | ~ v1_funct_2(k2_tmap_1(A_154,B_153,E_155,C_152),u1_struct_0(C_152),u1_struct_0(B_153))
      | ~ v1_funct_1(k2_tmap_1(A_154,B_153,E_155,C_152))
      | ~ m1_subset_1(E_155,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_154),u1_struct_0(B_153))))
      | ~ v1_funct_2(E_155,u1_struct_0(A_154),u1_struct_0(B_153))
      | ~ v1_funct_1(E_155)
      | ~ r4_tsep_1(A_154,C_152,D_151)
      | ~ m1_pre_topc(D_151,A_154)
      | v2_struct_0(D_151)
      | ~ m1_pre_topc(C_152,A_154)
      | v2_struct_0(C_152)
      | ~ l1_pre_topc(B_153)
      | ~ v2_pre_topc(B_153)
      | v2_struct_0(B_153)
      | ~ l1_pre_topc(A_154)
      | ~ v2_pre_topc(A_154)
      | v2_struct_0(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_326,plain,(
    ! [C_152] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',C_152,'#skF_5')),k1_tsep_1('#skF_1',C_152,'#skF_5'),'#skF_2')
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'))
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_152),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_152),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_152),C_152,'#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_152),u1_struct_0(C_152),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_152))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ r4_tsep_1('#skF_1',C_152,'#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(C_152,'#skF_1')
      | v2_struct_0(C_152)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_156,c_324])).

tff(c_331,plain,(
    ! [C_152] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',C_152,'#skF_5')),k1_tsep_1('#skF_1',C_152,'#skF_5'),'#skF_2')
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_152),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_152),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_152),C_152,'#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_152),u1_struct_0(C_152),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_152))
      | ~ r4_tsep_1('#skF_1',C_152,'#skF_5')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(C_152,'#skF_1')
      | v2_struct_0(C_152)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_46,c_28,c_44,c_42,c_40,c_147,c_151,c_149,c_326])).

tff(c_337,plain,(
    ! [C_156] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',C_156,'#skF_5')),k1_tsep_1('#skF_1',C_156,'#skF_5'),'#skF_2')
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_156),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_156),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_156),C_156,'#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_156),u1_struct_0(C_156),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_156))
      | ~ r4_tsep_1('#skF_1',C_156,'#skF_5')
      | ~ m1_pre_topc(C_156,'#skF_1')
      | v2_struct_0(C_156) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_50,c_32,c_331])).

tff(c_343,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2')
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_155,c_337])).

tff(c_350,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2')
    | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_148,c_152,c_150,c_343])).

tff(c_351,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2')
    | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_350])).

tff(c_353,plain,(
    ~ r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_351])).

tff(c_356,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ v1_borsuk_1('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_borsuk_1('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_353])).

tff(c_359,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_36,c_34,c_30,c_28,c_356])).

tff(c_361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_359])).

tff(c_363,plain,(
    r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_351])).

tff(c_379,plain,(
    ! [A_166,E_167,B_165,C_164,D_163] :
      ( m1_subset_1(k2_tmap_1(A_166,B_165,E_167,k1_tsep_1(A_166,C_164,D_163)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_166,C_164,D_163)),u1_struct_0(B_165))))
      | ~ m1_subset_1(k2_tmap_1(A_166,B_165,E_167,D_163),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_163),u1_struct_0(B_165))))
      | ~ v5_pre_topc(k2_tmap_1(A_166,B_165,E_167,D_163),D_163,B_165)
      | ~ v1_funct_2(k2_tmap_1(A_166,B_165,E_167,D_163),u1_struct_0(D_163),u1_struct_0(B_165))
      | ~ v1_funct_1(k2_tmap_1(A_166,B_165,E_167,D_163))
      | ~ m1_subset_1(k2_tmap_1(A_166,B_165,E_167,C_164),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_164),u1_struct_0(B_165))))
      | ~ v5_pre_topc(k2_tmap_1(A_166,B_165,E_167,C_164),C_164,B_165)
      | ~ v1_funct_2(k2_tmap_1(A_166,B_165,E_167,C_164),u1_struct_0(C_164),u1_struct_0(B_165))
      | ~ v1_funct_1(k2_tmap_1(A_166,B_165,E_167,C_164))
      | ~ m1_subset_1(E_167,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_166),u1_struct_0(B_165))))
      | ~ v1_funct_2(E_167,u1_struct_0(A_166),u1_struct_0(B_165))
      | ~ v1_funct_1(E_167)
      | ~ r4_tsep_1(A_166,C_164,D_163)
      | ~ m1_pre_topc(D_163,A_166)
      | v2_struct_0(D_163)
      | ~ m1_pre_topc(C_164,A_166)
      | v2_struct_0(C_164)
      | ~ l1_pre_topc(B_165)
      | ~ v2_pre_topc(B_165)
      | v2_struct_0(B_165)
      | ~ l1_pre_topc(A_166)
      | ~ v2_pre_topc(A_166)
      | v2_struct_0(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_58,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_184,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_152,c_150,c_155,c_147,c_151,c_149,c_156,c_58])).

tff(c_185,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_191,plain,(
    ! [D_108,B_110,A_111,C_109,E_112] :
      ( v1_funct_1(k2_tmap_1(A_111,B_110,E_112,k1_tsep_1(A_111,C_109,D_108)))
      | ~ m1_subset_1(k2_tmap_1(A_111,B_110,E_112,D_108),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_108),u1_struct_0(B_110))))
      | ~ v5_pre_topc(k2_tmap_1(A_111,B_110,E_112,D_108),D_108,B_110)
      | ~ v1_funct_2(k2_tmap_1(A_111,B_110,E_112,D_108),u1_struct_0(D_108),u1_struct_0(B_110))
      | ~ v1_funct_1(k2_tmap_1(A_111,B_110,E_112,D_108))
      | ~ m1_subset_1(k2_tmap_1(A_111,B_110,E_112,C_109),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_109),u1_struct_0(B_110))))
      | ~ v5_pre_topc(k2_tmap_1(A_111,B_110,E_112,C_109),C_109,B_110)
      | ~ v1_funct_2(k2_tmap_1(A_111,B_110,E_112,C_109),u1_struct_0(C_109),u1_struct_0(B_110))
      | ~ v1_funct_1(k2_tmap_1(A_111,B_110,E_112,C_109))
      | ~ m1_subset_1(E_112,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_111),u1_struct_0(B_110))))
      | ~ v1_funct_2(E_112,u1_struct_0(A_111),u1_struct_0(B_110))
      | ~ v1_funct_1(E_112)
      | ~ r4_tsep_1(A_111,C_109,D_108)
      | ~ m1_pre_topc(D_108,A_111)
      | v2_struct_0(D_108)
      | ~ m1_pre_topc(C_109,A_111)
      | v2_struct_0(C_109)
      | ~ l1_pre_topc(B_110)
      | ~ v2_pre_topc(B_110)
      | v2_struct_0(B_110)
      | ~ l1_pre_topc(A_111)
      | ~ v2_pre_topc(A_111)
      | v2_struct_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_193,plain,(
    ! [C_109] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',C_109,'#skF_5')))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'))
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_109),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_109),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_109),C_109,'#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_109),u1_struct_0(C_109),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_109))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ r4_tsep_1('#skF_1',C_109,'#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(C_109,'#skF_1')
      | v2_struct_0(C_109)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_156,c_191])).

tff(c_198,plain,(
    ! [C_109] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',C_109,'#skF_5')))
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_109),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_109),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_109),C_109,'#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_109),u1_struct_0(C_109),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_109))
      | ~ r4_tsep_1('#skF_1',C_109,'#skF_5')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(C_109,'#skF_1')
      | v2_struct_0(C_109)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_46,c_28,c_44,c_42,c_40,c_147,c_151,c_149,c_193])).

tff(c_204,plain,(
    ! [C_113] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',C_113,'#skF_5')))
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_113),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_113),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_113),C_113,'#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_113),u1_struct_0(C_113),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_113))
      | ~ r4_tsep_1('#skF_1',C_113,'#skF_5')
      | ~ m1_pre_topc(C_113,'#skF_1')
      | v2_struct_0(C_113) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_50,c_32,c_198])).

tff(c_210,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_155,c_204])).

tff(c_217,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')))
    | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_148,c_152,c_150,c_210])).

tff(c_218,plain,(
    ~ r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_185,c_217])).

tff(c_221,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ v1_borsuk_1('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_borsuk_1('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_218])).

tff(c_224,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_36,c_34,c_30,c_28,c_221])).

tff(c_226,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_224])).

tff(c_227,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2')
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_229,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_227])).

tff(c_417,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_379,c_229])).

tff(c_452,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_46,c_34,c_28,c_363,c_44,c_42,c_40,c_148,c_152,c_150,c_155,c_147,c_151,c_149,c_156,c_417])).

tff(c_454,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_50,c_38,c_32,c_452])).

tff(c_455,plain,
    ( ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_227])).

tff(c_478,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_455])).

tff(c_624,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_621,c_478])).

tff(c_627,plain,
    ( ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_46,c_34,c_28,c_44,c_42,c_40,c_148,c_152,c_150,c_155,c_147,c_151,c_149,c_156,c_624])).

tff(c_628,plain,(
    ~ r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_50,c_38,c_32,c_627])).

tff(c_631,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ v1_borsuk_1('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_borsuk_1('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_628])).

tff(c_634,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_36,c_34,c_30,c_28,c_631])).

tff(c_636,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_634])).

tff(c_637,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_455])).

tff(c_698,plain,(
    ! [E_244,C_241,A_243,D_240,B_242] :
      ( v5_pre_topc(k2_tmap_1(A_243,B_242,E_244,k1_tsep_1(A_243,C_241,D_240)),k1_tsep_1(A_243,C_241,D_240),B_242)
      | ~ m1_subset_1(k2_tmap_1(A_243,B_242,E_244,D_240),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_240),u1_struct_0(B_242))))
      | ~ v5_pre_topc(k2_tmap_1(A_243,B_242,E_244,D_240),D_240,B_242)
      | ~ v1_funct_2(k2_tmap_1(A_243,B_242,E_244,D_240),u1_struct_0(D_240),u1_struct_0(B_242))
      | ~ v1_funct_1(k2_tmap_1(A_243,B_242,E_244,D_240))
      | ~ m1_subset_1(k2_tmap_1(A_243,B_242,E_244,C_241),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_241),u1_struct_0(B_242))))
      | ~ v5_pre_topc(k2_tmap_1(A_243,B_242,E_244,C_241),C_241,B_242)
      | ~ v1_funct_2(k2_tmap_1(A_243,B_242,E_244,C_241),u1_struct_0(C_241),u1_struct_0(B_242))
      | ~ v1_funct_1(k2_tmap_1(A_243,B_242,E_244,C_241))
      | ~ m1_subset_1(E_244,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_243),u1_struct_0(B_242))))
      | ~ v1_funct_2(E_244,u1_struct_0(A_243),u1_struct_0(B_242))
      | ~ v1_funct_1(E_244)
      | ~ r4_tsep_1(A_243,C_241,D_240)
      | ~ m1_pre_topc(D_240,A_243)
      | v2_struct_0(D_240)
      | ~ m1_pre_topc(C_241,A_243)
      | v2_struct_0(C_241)
      | ~ l1_pre_topc(B_242)
      | ~ v2_pre_topc(B_242)
      | v2_struct_0(B_242)
      | ~ l1_pre_topc(A_243)
      | ~ v2_pre_topc(A_243)
      | v2_struct_0(A_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_702,plain,(
    ! [C_241] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',C_241,'#skF_5')),k1_tsep_1('#skF_1',C_241,'#skF_5'),'#skF_2')
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'))
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_241),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_241),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_241),C_241,'#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_241),u1_struct_0(C_241),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_241))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ r4_tsep_1('#skF_1',C_241,'#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(C_241,'#skF_1')
      | v2_struct_0(C_241)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_156,c_698])).

tff(c_711,plain,(
    ! [C_241] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',C_241,'#skF_5')),k1_tsep_1('#skF_1',C_241,'#skF_5'),'#skF_2')
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_241),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_241),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_241),C_241,'#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_241),u1_struct_0(C_241),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_241))
      | ~ r4_tsep_1('#skF_1',C_241,'#skF_5')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(C_241,'#skF_1')
      | v2_struct_0(C_241)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_46,c_28,c_44,c_42,c_40,c_147,c_151,c_149,c_702])).

tff(c_793,plain,(
    ! [C_252] :
      ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1',C_252,'#skF_5')),k1_tsep_1('#skF_1',C_252,'#skF_5'),'#skF_2')
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_252),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_252),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_252),C_252,'#skF_2')
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_252),u1_struct_0(C_252),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',C_252))
      | ~ r4_tsep_1('#skF_1',C_252,'#skF_5')
      | ~ m1_pre_topc(C_252,'#skF_1')
      | v2_struct_0(C_252) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_50,c_32,c_711])).

tff(c_802,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2')
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_155,c_793])).

tff(c_812,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2')
    | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_148,c_152,c_150,c_802])).

tff(c_813,plain,(
    ~ r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_637,c_812])).

tff(c_816,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ v1_borsuk_1('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_borsuk_1('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_813])).

tff(c_819,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_36,c_34,c_30,c_28,c_816])).

tff(c_821,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_819])).

tff(c_823,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_822,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_74,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2'))
    | m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_844,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_823,c_74])).

tff(c_72,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2')
    | m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_835,plain,(
    v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_823,c_72])).

tff(c_70,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2'))))
    | m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_846,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_823,c_70])).

tff(c_897,plain,(
    ! [E_290,A_289,B_288,D_286,C_287] :
      ( m1_subset_1(k2_tmap_1(A_289,B_288,E_290,D_286),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_286),u1_struct_0(B_288))))
      | ~ m1_subset_1(k2_tmap_1(A_289,B_288,E_290,k1_tsep_1(A_289,C_287,D_286)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_289,C_287,D_286)),u1_struct_0(B_288))))
      | ~ v5_pre_topc(k2_tmap_1(A_289,B_288,E_290,k1_tsep_1(A_289,C_287,D_286)),k1_tsep_1(A_289,C_287,D_286),B_288)
      | ~ v1_funct_2(k2_tmap_1(A_289,B_288,E_290,k1_tsep_1(A_289,C_287,D_286)),u1_struct_0(k1_tsep_1(A_289,C_287,D_286)),u1_struct_0(B_288))
      | ~ v1_funct_1(k2_tmap_1(A_289,B_288,E_290,k1_tsep_1(A_289,C_287,D_286)))
      | ~ m1_subset_1(E_290,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_289),u1_struct_0(B_288))))
      | ~ v1_funct_2(E_290,u1_struct_0(A_289),u1_struct_0(B_288))
      | ~ v1_funct_1(E_290)
      | ~ r4_tsep_1(A_289,C_287,D_286)
      | ~ m1_pre_topc(D_286,A_289)
      | v2_struct_0(D_286)
      | ~ m1_pre_topc(C_287,A_289)
      | v2_struct_0(C_287)
      | ~ l1_pre_topc(B_288)
      | ~ v2_pre_topc(B_288)
      | v2_struct_0(B_288)
      | ~ l1_pre_topc(A_289)
      | ~ v2_pre_topc(A_289)
      | v2_struct_0(A_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_900,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_846,c_897])).

tff(c_903,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_46,c_34,c_28,c_44,c_42,c_40,c_822,c_844,c_835,c_900])).

tff(c_904,plain,(
    ~ r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_50,c_38,c_32,c_823,c_903])).

tff(c_915,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ v1_borsuk_1('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_borsuk_1('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_904])).

tff(c_918,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_36,c_34,c_30,c_28,c_915])).

tff(c_920,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_918])).

tff(c_922,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_921,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_114,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2'))
    | m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_941,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_922,c_114])).

tff(c_112,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2')
    | m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_936,plain,(
    v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_922,c_112])).

tff(c_110,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2'))))
    | m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_946,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_922,c_110])).

tff(c_997,plain,(
    ! [C_330,A_332,E_333,B_331,D_329] :
      ( m1_subset_1(k2_tmap_1(A_332,B_331,E_333,C_330),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_330),u1_struct_0(B_331))))
      | ~ m1_subset_1(k2_tmap_1(A_332,B_331,E_333,k1_tsep_1(A_332,C_330,D_329)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_332,C_330,D_329)),u1_struct_0(B_331))))
      | ~ v5_pre_topc(k2_tmap_1(A_332,B_331,E_333,k1_tsep_1(A_332,C_330,D_329)),k1_tsep_1(A_332,C_330,D_329),B_331)
      | ~ v1_funct_2(k2_tmap_1(A_332,B_331,E_333,k1_tsep_1(A_332,C_330,D_329)),u1_struct_0(k1_tsep_1(A_332,C_330,D_329)),u1_struct_0(B_331))
      | ~ v1_funct_1(k2_tmap_1(A_332,B_331,E_333,k1_tsep_1(A_332,C_330,D_329)))
      | ~ m1_subset_1(E_333,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_332),u1_struct_0(B_331))))
      | ~ v1_funct_2(E_333,u1_struct_0(A_332),u1_struct_0(B_331))
      | ~ v1_funct_1(E_333)
      | ~ r4_tsep_1(A_332,C_330,D_329)
      | ~ m1_pre_topc(D_329,A_332)
      | v2_struct_0(D_329)
      | ~ m1_pre_topc(C_330,A_332)
      | v2_struct_0(C_330)
      | ~ l1_pre_topc(B_331)
      | ~ v2_pre_topc(B_331)
      | v2_struct_0(B_331)
      | ~ l1_pre_topc(A_332)
      | ~ v2_pre_topc(A_332)
      | v2_struct_0(A_332) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1000,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_946,c_997])).

tff(c_1003,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_46,c_34,c_28,c_44,c_42,c_40,c_921,c_941,c_936,c_1000])).

tff(c_1004,plain,(
    ~ r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_50,c_38,c_32,c_922,c_1003])).

tff(c_1007,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ v1_borsuk_1('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_borsuk_1('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_1004])).

tff(c_1010,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_36,c_34,c_30,c_28,c_1007])).

tff(c_1012,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1010])).

tff(c_1014,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_1013,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_134,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2'))
    | v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_1031,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_1014,c_134])).

tff(c_132,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2')
    | v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_1024,plain,(
    v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_1014,c_132])).

tff(c_130,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2'))))
    | v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_1038,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_1014,c_130])).

tff(c_1082,plain,(
    ! [D_362,E_366,A_365,C_363,B_364] :
      ( v1_funct_2(k2_tmap_1(A_365,B_364,E_366,C_363),u1_struct_0(C_363),u1_struct_0(B_364))
      | ~ m1_subset_1(k2_tmap_1(A_365,B_364,E_366,k1_tsep_1(A_365,C_363,D_362)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_365,C_363,D_362)),u1_struct_0(B_364))))
      | ~ v5_pre_topc(k2_tmap_1(A_365,B_364,E_366,k1_tsep_1(A_365,C_363,D_362)),k1_tsep_1(A_365,C_363,D_362),B_364)
      | ~ v1_funct_2(k2_tmap_1(A_365,B_364,E_366,k1_tsep_1(A_365,C_363,D_362)),u1_struct_0(k1_tsep_1(A_365,C_363,D_362)),u1_struct_0(B_364))
      | ~ v1_funct_1(k2_tmap_1(A_365,B_364,E_366,k1_tsep_1(A_365,C_363,D_362)))
      | ~ m1_subset_1(E_366,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_365),u1_struct_0(B_364))))
      | ~ v1_funct_2(E_366,u1_struct_0(A_365),u1_struct_0(B_364))
      | ~ v1_funct_1(E_366)
      | ~ r4_tsep_1(A_365,C_363,D_362)
      | ~ m1_pre_topc(D_362,A_365)
      | v2_struct_0(D_362)
      | ~ m1_pre_topc(C_363,A_365)
      | v2_struct_0(C_363)
      | ~ l1_pre_topc(B_364)
      | ~ v2_pre_topc(B_364)
      | v2_struct_0(B_364)
      | ~ l1_pre_topc(A_365)
      | ~ v2_pre_topc(A_365)
      | v2_struct_0(A_365) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1085,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1038,c_1082])).

tff(c_1088,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_46,c_34,c_28,c_44,c_42,c_40,c_1013,c_1031,c_1024,c_1085])).

tff(c_1089,plain,(
    ~ r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_50,c_38,c_32,c_1014,c_1088])).

tff(c_1092,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ v1_borsuk_1('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_borsuk_1('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_1089])).

tff(c_1095,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_36,c_34,c_30,c_28,c_1092])).

tff(c_1097,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1095])).

tff(c_1099,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_1098,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_94,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2'))
    | v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_1118,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_1099,c_94])).

tff(c_92,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2')
    | v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_1113,plain,(
    v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_1099,c_92])).

tff(c_90,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2'))))
    | v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_1122,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_1099,c_90])).

tff(c_1168,plain,(
    ! [B_397,C_396,E_399,A_398,D_395] :
      ( v1_funct_2(k2_tmap_1(A_398,B_397,E_399,D_395),u1_struct_0(D_395),u1_struct_0(B_397))
      | ~ m1_subset_1(k2_tmap_1(A_398,B_397,E_399,k1_tsep_1(A_398,C_396,D_395)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_398,C_396,D_395)),u1_struct_0(B_397))))
      | ~ v5_pre_topc(k2_tmap_1(A_398,B_397,E_399,k1_tsep_1(A_398,C_396,D_395)),k1_tsep_1(A_398,C_396,D_395),B_397)
      | ~ v1_funct_2(k2_tmap_1(A_398,B_397,E_399,k1_tsep_1(A_398,C_396,D_395)),u1_struct_0(k1_tsep_1(A_398,C_396,D_395)),u1_struct_0(B_397))
      | ~ v1_funct_1(k2_tmap_1(A_398,B_397,E_399,k1_tsep_1(A_398,C_396,D_395)))
      | ~ m1_subset_1(E_399,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_398),u1_struct_0(B_397))))
      | ~ v1_funct_2(E_399,u1_struct_0(A_398),u1_struct_0(B_397))
      | ~ v1_funct_1(E_399)
      | ~ r4_tsep_1(A_398,C_396,D_395)
      | ~ m1_pre_topc(D_395,A_398)
      | v2_struct_0(D_395)
      | ~ m1_pre_topc(C_396,A_398)
      | v2_struct_0(C_396)
      | ~ l1_pre_topc(B_397)
      | ~ v2_pre_topc(B_397)
      | v2_struct_0(B_397)
      | ~ l1_pre_topc(A_398)
      | ~ v2_pre_topc(A_398)
      | v2_struct_0(A_398) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1171,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1122,c_1168])).

tff(c_1174,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_46,c_34,c_28,c_44,c_42,c_40,c_1098,c_1118,c_1113,c_1171])).

tff(c_1175,plain,(
    ~ r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_50,c_38,c_32,c_1099,c_1174])).

tff(c_1178,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ v1_borsuk_1('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_borsuk_1('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_1175])).

tff(c_1181,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_36,c_34,c_30,c_28,c_1178])).

tff(c_1183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1181])).

tff(c_1185,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_1184,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_124,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2'))
    | v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_1201,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_1185,c_124])).

tff(c_122,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2')
    | v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_1193,plain,(
    v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_1185,c_122])).

tff(c_120,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2'))))
    | v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_1206,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_1185,c_120])).

tff(c_1241,plain,(
    ! [B_420,C_419,A_421,D_418,E_422] :
      ( v5_pre_topc(k2_tmap_1(A_421,B_420,E_422,C_419),C_419,B_420)
      | ~ m1_subset_1(k2_tmap_1(A_421,B_420,E_422,k1_tsep_1(A_421,C_419,D_418)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_421,C_419,D_418)),u1_struct_0(B_420))))
      | ~ v5_pre_topc(k2_tmap_1(A_421,B_420,E_422,k1_tsep_1(A_421,C_419,D_418)),k1_tsep_1(A_421,C_419,D_418),B_420)
      | ~ v1_funct_2(k2_tmap_1(A_421,B_420,E_422,k1_tsep_1(A_421,C_419,D_418)),u1_struct_0(k1_tsep_1(A_421,C_419,D_418)),u1_struct_0(B_420))
      | ~ v1_funct_1(k2_tmap_1(A_421,B_420,E_422,k1_tsep_1(A_421,C_419,D_418)))
      | ~ m1_subset_1(E_422,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_421),u1_struct_0(B_420))))
      | ~ v1_funct_2(E_422,u1_struct_0(A_421),u1_struct_0(B_420))
      | ~ v1_funct_1(E_422)
      | ~ r4_tsep_1(A_421,C_419,D_418)
      | ~ m1_pre_topc(D_418,A_421)
      | v2_struct_0(D_418)
      | ~ m1_pre_topc(C_419,A_421)
      | v2_struct_0(C_419)
      | ~ l1_pre_topc(B_420)
      | ~ v2_pre_topc(B_420)
      | v2_struct_0(B_420)
      | ~ l1_pre_topc(A_421)
      | ~ v2_pre_topc(A_421)
      | v2_struct_0(A_421) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1244,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1206,c_1241])).

tff(c_1247,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4','#skF_2')
    | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_46,c_34,c_28,c_44,c_42,c_40,c_1184,c_1201,c_1193,c_1244])).

tff(c_1248,plain,(
    ~ r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_50,c_38,c_32,c_1185,c_1247])).

tff(c_1251,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ v1_borsuk_1('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_borsuk_1('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_1248])).

tff(c_1254,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_36,c_34,c_30,c_28,c_1251])).

tff(c_1256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1254])).

tff(c_1258,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_1257,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_84,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2'))
    | v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_1276,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_1258,c_84])).

tff(c_82,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2')
    | v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_1267,plain,(
    v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_1258,c_82])).

tff(c_80,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2'))))
    | v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_1282,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_1258,c_80])).

tff(c_1315,plain,(
    ! [D_441,C_442,A_444,B_443,E_445] :
      ( v5_pre_topc(k2_tmap_1(A_444,B_443,E_445,D_441),D_441,B_443)
      | ~ m1_subset_1(k2_tmap_1(A_444,B_443,E_445,k1_tsep_1(A_444,C_442,D_441)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_444,C_442,D_441)),u1_struct_0(B_443))))
      | ~ v5_pre_topc(k2_tmap_1(A_444,B_443,E_445,k1_tsep_1(A_444,C_442,D_441)),k1_tsep_1(A_444,C_442,D_441),B_443)
      | ~ v1_funct_2(k2_tmap_1(A_444,B_443,E_445,k1_tsep_1(A_444,C_442,D_441)),u1_struct_0(k1_tsep_1(A_444,C_442,D_441)),u1_struct_0(B_443))
      | ~ v1_funct_1(k2_tmap_1(A_444,B_443,E_445,k1_tsep_1(A_444,C_442,D_441)))
      | ~ m1_subset_1(E_445,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_444),u1_struct_0(B_443))))
      | ~ v1_funct_2(E_445,u1_struct_0(A_444),u1_struct_0(B_443))
      | ~ v1_funct_1(E_445)
      | ~ r4_tsep_1(A_444,C_442,D_441)
      | ~ m1_pre_topc(D_441,A_444)
      | v2_struct_0(D_441)
      | ~ m1_pre_topc(C_442,A_444)
      | v2_struct_0(C_442)
      | ~ l1_pre_topc(B_443)
      | ~ v2_pre_topc(B_443)
      | v2_struct_0(B_443)
      | ~ l1_pre_topc(A_444)
      | ~ v2_pre_topc(A_444)
      | v2_struct_0(A_444) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1318,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1282,c_1315])).

tff(c_1321,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_5','#skF_2')
    | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_46,c_34,c_28,c_44,c_42,c_40,c_1257,c_1276,c_1267,c_1318])).

tff(c_1322,plain,(
    ~ r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_50,c_38,c_32,c_1258,c_1321])).

tff(c_1325,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ v1_borsuk_1('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_borsuk_1('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_1322])).

tff(c_1328,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_36,c_34,c_30,c_28,c_1325])).

tff(c_1330,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1328])).

tff(c_1332,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_1331,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_144,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2'))
    | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_1342,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_1332,c_144])).

tff(c_142,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2')
    | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_1338,plain,(
    v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_1332,c_142])).

tff(c_140,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2'))))
    | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_1346,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_1332,c_140])).

tff(c_1364,plain,(
    ! [B_451,C_450,E_453,A_452,D_449] :
      ( v1_funct_1(k2_tmap_1(A_452,B_451,E_453,C_450))
      | ~ m1_subset_1(k2_tmap_1(A_452,B_451,E_453,k1_tsep_1(A_452,C_450,D_449)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_452,C_450,D_449)),u1_struct_0(B_451))))
      | ~ v5_pre_topc(k2_tmap_1(A_452,B_451,E_453,k1_tsep_1(A_452,C_450,D_449)),k1_tsep_1(A_452,C_450,D_449),B_451)
      | ~ v1_funct_2(k2_tmap_1(A_452,B_451,E_453,k1_tsep_1(A_452,C_450,D_449)),u1_struct_0(k1_tsep_1(A_452,C_450,D_449)),u1_struct_0(B_451))
      | ~ v1_funct_1(k2_tmap_1(A_452,B_451,E_453,k1_tsep_1(A_452,C_450,D_449)))
      | ~ m1_subset_1(E_453,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_452),u1_struct_0(B_451))))
      | ~ v1_funct_2(E_453,u1_struct_0(A_452),u1_struct_0(B_451))
      | ~ v1_funct_1(E_453)
      | ~ r4_tsep_1(A_452,C_450,D_449)
      | ~ m1_pre_topc(D_449,A_452)
      | v2_struct_0(D_449)
      | ~ m1_pre_topc(C_450,A_452)
      | v2_struct_0(C_450)
      | ~ l1_pre_topc(B_451)
      | ~ v2_pre_topc(B_451)
      | v2_struct_0(B_451)
      | ~ l1_pre_topc(A_452)
      | ~ v2_pre_topc(A_452)
      | v2_struct_0(A_452) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1367,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1346,c_1364])).

tff(c_1370,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_46,c_34,c_28,c_44,c_42,c_40,c_1331,c_1342,c_1338,c_1367])).

tff(c_1371,plain,(
    ~ r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_50,c_38,c_32,c_1332,c_1370])).

tff(c_1374,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ v1_borsuk_1('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_borsuk_1('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_1371])).

tff(c_1377,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_36,c_34,c_30,c_28,c_1374])).

tff(c_1379,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1377])).

tff(c_1381,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_1380,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_104,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2'))
    | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_1393,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_1381,c_104])).

tff(c_102,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2')
    | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_1388,plain,(
    v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_1381,c_102])).

tff(c_100,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2'))))
    | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_1401,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_1381,c_100])).

tff(c_1422,plain,(
    ! [B_464,A_465,C_463,E_466,D_462] :
      ( v1_funct_1(k2_tmap_1(A_465,B_464,E_466,D_462))
      | ~ m1_subset_1(k2_tmap_1(A_465,B_464,E_466,k1_tsep_1(A_465,C_463,D_462)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_465,C_463,D_462)),u1_struct_0(B_464))))
      | ~ v5_pre_topc(k2_tmap_1(A_465,B_464,E_466,k1_tsep_1(A_465,C_463,D_462)),k1_tsep_1(A_465,C_463,D_462),B_464)
      | ~ v1_funct_2(k2_tmap_1(A_465,B_464,E_466,k1_tsep_1(A_465,C_463,D_462)),u1_struct_0(k1_tsep_1(A_465,C_463,D_462)),u1_struct_0(B_464))
      | ~ v1_funct_1(k2_tmap_1(A_465,B_464,E_466,k1_tsep_1(A_465,C_463,D_462)))
      | ~ m1_subset_1(E_466,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_465),u1_struct_0(B_464))))
      | ~ v1_funct_2(E_466,u1_struct_0(A_465),u1_struct_0(B_464))
      | ~ v1_funct_1(E_466)
      | ~ r4_tsep_1(A_465,C_463,D_462)
      | ~ m1_pre_topc(D_462,A_465)
      | v2_struct_0(D_462)
      | ~ m1_pre_topc(C_463,A_465)
      | v2_struct_0(C_463)
      | ~ l1_pre_topc(B_464)
      | ~ v2_pre_topc(B_464)
      | v2_struct_0(B_464)
      | ~ l1_pre_topc(A_465)
      | ~ v2_pre_topc(A_465)
      | v2_struct_0(A_465) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1425,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ v5_pre_topc(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),k1_tsep_1('#skF_1','#skF_4','#skF_5'),'#skF_2')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0(k1_tsep_1('#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3',k1_tsep_1('#skF_1','#skF_4','#skF_5')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1401,c_1422])).

tff(c_1428,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ r4_tsep_1('#skF_1','#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_46,c_34,c_28,c_44,c_42,c_40,c_1380,c_1393,c_1388,c_1425])).

tff(c_1429,plain,(
    ~ r4_tsep_1('#skF_1','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_50,c_38,c_32,c_1381,c_1428])).

tff(c_1440,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ v1_borsuk_1('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_borsuk_1('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_1429])).

tff(c_1443,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_36,c_34,c_30,c_28,c_1440])).

tff(c_1445,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1443])).

%------------------------------------------------------------------------------
