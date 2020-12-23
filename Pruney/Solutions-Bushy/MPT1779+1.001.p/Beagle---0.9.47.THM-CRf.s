%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1779+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:22 EST 2020

% Result     : Theorem 4.25s
% Output     : CNFRefutation 4.25s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 487 expanded)
%              Number of leaves         :   27 ( 207 expanded)
%              Depth                    :   14
%              Number of atoms          :  685 (5590 expanded)
%              Number of equality atoms :   12 (  33 expanded)
%              Maximal formula depth    :   33 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v5_pre_topc > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_223,negated_conjecture,(
    ~ ! [A] :
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
                   => ! [E] :
                        ( ( ~ v2_struct_0(E)
                          & m1_pre_topc(E,A) )
                       => ( ( m1_pre_topc(C,D)
                            & m1_pre_topc(E,C) )
                         => ! [F] :
                              ( ( v1_funct_1(F)
                                & v1_funct_2(F,u1_struct_0(D),u1_struct_0(B))
                                & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                             => ( ( v1_funct_1(k3_tmap_1(A,B,D,C,F))
                                  & v1_funct_2(k3_tmap_1(A,B,D,C,F),u1_struct_0(C),u1_struct_0(B))
                                  & v5_pre_topc(k3_tmap_1(A,B,D,C,F),C,B)
                                  & m1_subset_1(k3_tmap_1(A,B,D,C,F),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                               => ( v1_funct_1(k3_tmap_1(A,B,D,E,F))
                                  & v1_funct_2(k3_tmap_1(A,B,D,E,F),u1_struct_0(E),u1_struct_0(B))
                                  & v5_pre_topc(k3_tmap_1(A,B,D,E,F),E,B)
                                  & m1_subset_1(k3_tmap_1(A,B,D,E,F),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(E),u1_struct_0(B)))) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_tmap_1)).

tff(f_54,axiom,(
    ! [A,B,C,D,E] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & m1_pre_topc(C,A)
        & m1_pre_topc(D,A)
        & v1_funct_1(E)
        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
     => ( v1_funct_1(k3_tmap_1(A,B,C,D,E))
        & v1_funct_2(k3_tmap_1(A,B,C,D,E),u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(k3_tmap_1(A,B,C,D,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).

tff(f_116,axiom,(
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
                 => ! [E] :
                      ( ( ~ v2_struct_0(E)
                        & m1_pre_topc(E,A) )
                     => ( ( m1_pre_topc(D,C)
                          & m1_pre_topc(E,D) )
                       => ! [F] :
                            ( ( v1_funct_1(F)
                              & v1_funct_2(F,u1_struct_0(C),u1_struct_0(B))
                              & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                           => r2_funct_2(u1_struct_0(E),u1_struct_0(B),k3_tmap_1(A,B,D,E,k3_tmap_1(A,B,C,D,F)),k3_tmap_1(A,B,C,E,F)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_tmap_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_162,axiom,(
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
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & v5_pre_topc(E,C,B)
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ( m1_pre_topc(D,C)
                       => ( v1_funct_1(k3_tmap_1(A,B,C,D,E))
                          & v1_funct_2(k3_tmap_1(A,B,C,D,E),u1_struct_0(D),u1_struct_0(B))
                          & v5_pre_topc(k3_tmap_1(A,B,C,D,E),D,B)
                          & m1_subset_1(k3_tmap_1(A,B,C,D,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_tmap_1)).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_62,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_60,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_46,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_42,plain,(
    m1_pre_topc('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_56,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_54,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_36,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_34,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_32,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_190,plain,(
    ! [E_205,A_209,B_207,D_206,C_208] :
      ( v1_funct_2(k3_tmap_1(A_209,B_207,C_208,D_206,E_205),u1_struct_0(D_206),u1_struct_0(B_207))
      | ~ m1_subset_1(E_205,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_208),u1_struct_0(B_207))))
      | ~ v1_funct_2(E_205,u1_struct_0(C_208),u1_struct_0(B_207))
      | ~ v1_funct_1(E_205)
      | ~ m1_pre_topc(D_206,A_209)
      | ~ m1_pre_topc(C_208,A_209)
      | ~ l1_pre_topc(B_207)
      | ~ v2_pre_topc(B_207)
      | v2_struct_0(B_207)
      | ~ l1_pre_topc(A_209)
      | ~ v2_pre_topc(A_209)
      | v2_struct_0(A_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_196,plain,(
    ! [A_209,D_206] :
      ( v1_funct_2(k3_tmap_1(A_209,'#skF_2','#skF_4',D_206,'#skF_6'),u1_struct_0(D_206),u1_struct_0('#skF_2'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_206,A_209)
      | ~ m1_pre_topc('#skF_4',A_209)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_209)
      | ~ v2_pre_topc(A_209)
      | v2_struct_0(A_209) ) ),
    inference(resolution,[status(thm)],[c_32,c_190])).

tff(c_207,plain,(
    ! [A_209,D_206] :
      ( v1_funct_2(k3_tmap_1(A_209,'#skF_2','#skF_4',D_206,'#skF_6'),u1_struct_0(D_206),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_206,A_209)
      | ~ m1_pre_topc('#skF_4',A_209)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_209)
      | ~ v2_pre_topc(A_209)
      | v2_struct_0(A_209) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_36,c_34,c_196])).

tff(c_209,plain,(
    ! [A_210,D_211] :
      ( v1_funct_2(k3_tmap_1(A_210,'#skF_2','#skF_4',D_211,'#skF_6'),u1_struct_0(D_211),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_211,A_210)
      | ~ m1_pre_topc('#skF_4',A_210)
      | ~ l1_pre_topc(A_210)
      | ~ v2_pre_topc(A_210)
      | v2_struct_0(A_210) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_207])).

tff(c_145,plain,(
    ! [C_196,E_193,A_197,D_194,B_195] :
      ( m1_subset_1(k3_tmap_1(A_197,B_195,C_196,D_194,E_193),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_194),u1_struct_0(B_195))))
      | ~ m1_subset_1(E_193,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_196),u1_struct_0(B_195))))
      | ~ v1_funct_2(E_193,u1_struct_0(C_196),u1_struct_0(B_195))
      | ~ v1_funct_1(E_193)
      | ~ m1_pre_topc(D_194,A_197)
      | ~ m1_pre_topc(C_196,A_197)
      | ~ l1_pre_topc(B_195)
      | ~ v2_pre_topc(B_195)
      | v2_struct_0(B_195)
      | ~ l1_pre_topc(A_197)
      | ~ v2_pre_topc(A_197)
      | v2_struct_0(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_90,plain,(
    ! [C_171,D_169,E_168,A_172,B_170] :
      ( v1_funct_1(k3_tmap_1(A_172,B_170,C_171,D_169,E_168))
      | ~ m1_subset_1(E_168,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_171),u1_struct_0(B_170))))
      | ~ v1_funct_2(E_168,u1_struct_0(C_171),u1_struct_0(B_170))
      | ~ v1_funct_1(E_168)
      | ~ m1_pre_topc(D_169,A_172)
      | ~ m1_pre_topc(C_171,A_172)
      | ~ l1_pre_topc(B_170)
      | ~ v2_pre_topc(B_170)
      | v2_struct_0(B_170)
      | ~ l1_pre_topc(A_172)
      | ~ v2_pre_topc(A_172)
      | v2_struct_0(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_94,plain,(
    ! [A_172,D_169] :
      ( v1_funct_1(k3_tmap_1(A_172,'#skF_2','#skF_4',D_169,'#skF_6'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_169,A_172)
      | ~ m1_pre_topc('#skF_4',A_172)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_172)
      | ~ v2_pre_topc(A_172)
      | v2_struct_0(A_172) ) ),
    inference(resolution,[status(thm)],[c_32,c_90])).

tff(c_101,plain,(
    ! [A_172,D_169] :
      ( v1_funct_1(k3_tmap_1(A_172,'#skF_2','#skF_4',D_169,'#skF_6'))
      | ~ m1_pre_topc(D_169,A_172)
      | ~ m1_pre_topc('#skF_4',A_172)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_172)
      | ~ v2_pre_topc(A_172)
      | v2_struct_0(A_172) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_36,c_34,c_94])).

tff(c_103,plain,(
    ! [A_173,D_174] :
      ( v1_funct_1(k3_tmap_1(A_173,'#skF_2','#skF_4',D_174,'#skF_6'))
      | ~ m1_pre_topc(D_174,A_173)
      | ~ m1_pre_topc('#skF_4',A_173)
      | ~ l1_pre_topc(A_173)
      | ~ v2_pre_topc(A_173)
      | v2_struct_0(A_173) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_101])).

tff(c_22,plain,
    ( ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),'#skF_5','#skF_2')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_89,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_106,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_103,c_89])).

tff(c_109,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_46,c_42,c_106])).

tff(c_111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_109])).

tff(c_112,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),'#skF_5','#skF_2')
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_114,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_152,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_145,c_114])).

tff(c_159,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_46,c_42,c_36,c_34,c_32,c_152])).

tff(c_161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_159])).

tff(c_162,plain,
    ( ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),'#skF_5','#skF_2')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_169,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_162])).

tff(c_212,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_209,c_169])).

tff(c_215,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_46,c_42,c_212])).

tff(c_217,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_215])).

tff(c_218,plain,(
    ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),'#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_50,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_30,plain,(
    v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_26,plain,(
    v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),'#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_38,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_28,plain,(
    v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_269,plain,(
    ! [E_228,C_231,A_232,D_229,B_230] :
      ( m1_subset_1(k3_tmap_1(A_232,B_230,C_231,D_229,E_228),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_229),u1_struct_0(B_230))))
      | ~ m1_subset_1(E_228,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_231),u1_struct_0(B_230))))
      | ~ v1_funct_2(E_228,u1_struct_0(C_231),u1_struct_0(B_230))
      | ~ v1_funct_1(E_228)
      | ~ m1_pre_topc(D_229,A_232)
      | ~ m1_pre_topc(C_231,A_232)
      | ~ l1_pre_topc(B_230)
      | ~ v2_pre_topc(B_230)
      | v2_struct_0(B_230)
      | ~ l1_pre_topc(A_232)
      | ~ v2_pre_topc(A_232)
      | v2_struct_0(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4,plain,(
    ! [B_2,C_3,A_1,E_5,D_4] :
      ( v1_funct_2(k3_tmap_1(A_1,B_2,C_3,D_4,E_5),u1_struct_0(D_4),u1_struct_0(B_2))
      | ~ m1_subset_1(E_5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_3),u1_struct_0(B_2))))
      | ~ v1_funct_2(E_5,u1_struct_0(C_3),u1_struct_0(B_2))
      | ~ v1_funct_1(E_5)
      | ~ m1_pre_topc(D_4,A_1)
      | ~ m1_pre_topc(C_3,A_1)
      | ~ l1_pre_topc(B_2)
      | ~ v2_pre_topc(B_2)
      | v2_struct_0(B_2)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_276,plain,(
    ! [E_228,A_1,D_4,C_231,A_232,D_229,B_230] :
      ( v1_funct_2(k3_tmap_1(A_1,B_230,D_229,D_4,k3_tmap_1(A_232,B_230,C_231,D_229,E_228)),u1_struct_0(D_4),u1_struct_0(B_230))
      | ~ v1_funct_2(k3_tmap_1(A_232,B_230,C_231,D_229,E_228),u1_struct_0(D_229),u1_struct_0(B_230))
      | ~ v1_funct_1(k3_tmap_1(A_232,B_230,C_231,D_229,E_228))
      | ~ m1_pre_topc(D_4,A_1)
      | ~ m1_pre_topc(D_229,A_1)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1)
      | ~ m1_subset_1(E_228,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_231),u1_struct_0(B_230))))
      | ~ v1_funct_2(E_228,u1_struct_0(C_231),u1_struct_0(B_230))
      | ~ v1_funct_1(E_228)
      | ~ m1_pre_topc(D_229,A_232)
      | ~ m1_pre_topc(C_231,A_232)
      | ~ l1_pre_topc(B_230)
      | ~ v2_pre_topc(B_230)
      | v2_struct_0(B_230)
      | ~ l1_pre_topc(A_232)
      | ~ v2_pre_topc(A_232)
      | v2_struct_0(A_232) ) ),
    inference(resolution,[status(thm)],[c_269,c_4])).

tff(c_250,plain,(
    ! [C_226,E_223,B_225,D_224,A_227] :
      ( v1_funct_2(k3_tmap_1(A_227,B_225,C_226,D_224,E_223),u1_struct_0(D_224),u1_struct_0(B_225))
      | ~ m1_subset_1(E_223,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_226),u1_struct_0(B_225))))
      | ~ v1_funct_2(E_223,u1_struct_0(C_226),u1_struct_0(B_225))
      | ~ v1_funct_1(E_223)
      | ~ m1_pre_topc(D_224,A_227)
      | ~ m1_pre_topc(C_226,A_227)
      | ~ l1_pre_topc(B_225)
      | ~ v2_pre_topc(B_225)
      | v2_struct_0(B_225)
      | ~ l1_pre_topc(A_227)
      | ~ v2_pre_topc(A_227)
      | v2_struct_0(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_256,plain,(
    ! [A_227,D_224] :
      ( v1_funct_2(k3_tmap_1(A_227,'#skF_2','#skF_4',D_224,'#skF_6'),u1_struct_0(D_224),u1_struct_0('#skF_2'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_224,A_227)
      | ~ m1_pre_topc('#skF_4',A_227)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_227)
      | ~ v2_pre_topc(A_227)
      | v2_struct_0(A_227) ) ),
    inference(resolution,[status(thm)],[c_32,c_250])).

tff(c_267,plain,(
    ! [A_227,D_224] :
      ( v1_funct_2(k3_tmap_1(A_227,'#skF_2','#skF_4',D_224,'#skF_6'),u1_struct_0(D_224),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_224,A_227)
      | ~ m1_pre_topc('#skF_4',A_227)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_227)
      | ~ v2_pre_topc(A_227)
      | v2_struct_0(A_227) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_36,c_34,c_256])).

tff(c_268,plain,(
    ! [A_227,D_224] :
      ( v1_funct_2(k3_tmap_1(A_227,'#skF_2','#skF_4',D_224,'#skF_6'),u1_struct_0(D_224),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_224,A_227)
      | ~ m1_pre_topc('#skF_4',A_227)
      | ~ l1_pre_topc(A_227)
      | ~ v2_pre_topc(A_227)
      | v2_struct_0(A_227) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_267])).

tff(c_6,plain,(
    ! [B_2,C_3,A_1,E_5,D_4] :
      ( v1_funct_1(k3_tmap_1(A_1,B_2,C_3,D_4,E_5))
      | ~ m1_subset_1(E_5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_3),u1_struct_0(B_2))))
      | ~ v1_funct_2(E_5,u1_struct_0(C_3),u1_struct_0(B_2))
      | ~ v1_funct_1(E_5)
      | ~ m1_pre_topc(D_4,A_1)
      | ~ m1_pre_topc(C_3,A_1)
      | ~ l1_pre_topc(B_2)
      | ~ v2_pre_topc(B_2)
      | v2_struct_0(B_2)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_315,plain,(
    ! [A_263,A_260,E_262,D_261,D_259,C_258,B_257] :
      ( v1_funct_1(k3_tmap_1(A_263,B_257,D_259,D_261,k3_tmap_1(A_260,B_257,C_258,D_259,E_262)))
      | ~ v1_funct_2(k3_tmap_1(A_260,B_257,C_258,D_259,E_262),u1_struct_0(D_259),u1_struct_0(B_257))
      | ~ v1_funct_1(k3_tmap_1(A_260,B_257,C_258,D_259,E_262))
      | ~ m1_pre_topc(D_261,A_263)
      | ~ m1_pre_topc(D_259,A_263)
      | ~ l1_pre_topc(A_263)
      | ~ v2_pre_topc(A_263)
      | v2_struct_0(A_263)
      | ~ m1_subset_1(E_262,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_258),u1_struct_0(B_257))))
      | ~ v1_funct_2(E_262,u1_struct_0(C_258),u1_struct_0(B_257))
      | ~ v1_funct_1(E_262)
      | ~ m1_pre_topc(D_259,A_260)
      | ~ m1_pre_topc(C_258,A_260)
      | ~ l1_pre_topc(B_257)
      | ~ v2_pre_topc(B_257)
      | v2_struct_0(B_257)
      | ~ l1_pre_topc(A_260)
      | ~ v2_pre_topc(A_260)
      | v2_struct_0(A_260) ) ),
    inference(resolution,[status(thm)],[c_269,c_6])).

tff(c_321,plain,(
    ! [A_263,D_224,D_261,A_227] :
      ( v1_funct_1(k3_tmap_1(A_263,'#skF_2',D_224,D_261,k3_tmap_1(A_227,'#skF_2','#skF_4',D_224,'#skF_6')))
      | ~ v1_funct_1(k3_tmap_1(A_227,'#skF_2','#skF_4',D_224,'#skF_6'))
      | ~ m1_pre_topc(D_261,A_263)
      | ~ m1_pre_topc(D_224,A_263)
      | ~ l1_pre_topc(A_263)
      | ~ v2_pre_topc(A_263)
      | v2_struct_0(A_263)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(D_224,A_227)
      | ~ m1_pre_topc('#skF_4',A_227)
      | ~ l1_pre_topc(A_227)
      | ~ v2_pre_topc(A_227)
      | v2_struct_0(A_227) ) ),
    inference(resolution,[status(thm)],[c_268,c_315])).

tff(c_336,plain,(
    ! [A_263,D_224,D_261,A_227] :
      ( v1_funct_1(k3_tmap_1(A_263,'#skF_2',D_224,D_261,k3_tmap_1(A_227,'#skF_2','#skF_4',D_224,'#skF_6')))
      | ~ v1_funct_1(k3_tmap_1(A_227,'#skF_2','#skF_4',D_224,'#skF_6'))
      | ~ m1_pre_topc(D_261,A_263)
      | ~ m1_pre_topc(D_224,A_263)
      | ~ l1_pre_topc(A_263)
      | ~ v2_pre_topc(A_263)
      | v2_struct_0(A_263)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(D_224,A_227)
      | ~ m1_pre_topc('#skF_4',A_227)
      | ~ l1_pre_topc(A_227)
      | ~ v2_pre_topc(A_227)
      | v2_struct_0(A_227) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_36,c_34,c_32,c_321])).

tff(c_337,plain,(
    ! [A_263,D_224,D_261,A_227] :
      ( v1_funct_1(k3_tmap_1(A_263,'#skF_2',D_224,D_261,k3_tmap_1(A_227,'#skF_2','#skF_4',D_224,'#skF_6')))
      | ~ v1_funct_1(k3_tmap_1(A_227,'#skF_2','#skF_4',D_224,'#skF_6'))
      | ~ m1_pre_topc(D_261,A_263)
      | ~ m1_pre_topc(D_224,A_263)
      | ~ l1_pre_topc(A_263)
      | ~ v2_pre_topc(A_263)
      | v2_struct_0(A_263)
      | ~ m1_pre_topc(D_224,A_227)
      | ~ m1_pre_topc('#skF_4',A_227)
      | ~ l1_pre_topc(A_227)
      | ~ v2_pre_topc(A_227)
      | v2_struct_0(A_227) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_336])).

tff(c_40,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_24,plain,(
    m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_113,plain,(
    v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_219,plain,(
    v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_162])).

tff(c_163,plain,(
    m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,E_5,D_4] :
      ( m1_subset_1(k3_tmap_1(A_1,B_2,C_3,D_4,E_5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_4),u1_struct_0(B_2))))
      | ~ m1_subset_1(E_5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_3),u1_struct_0(B_2))))
      | ~ v1_funct_2(E_5,u1_struct_0(C_3),u1_struct_0(B_2))
      | ~ v1_funct_1(E_5)
      | ~ m1_pre_topc(D_4,A_1)
      | ~ m1_pre_topc(C_3,A_1)
      | ~ l1_pre_topc(B_2)
      | ~ v2_pre_topc(B_2)
      | v2_struct_0(B_2)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_311,plain,(
    ! [E_255,D_256,B_254,A_253,F_252,C_251] :
      ( r2_funct_2(u1_struct_0(E_255),u1_struct_0(B_254),k3_tmap_1(A_253,B_254,D_256,E_255,k3_tmap_1(A_253,B_254,C_251,D_256,F_252)),k3_tmap_1(A_253,B_254,C_251,E_255,F_252))
      | ~ m1_subset_1(F_252,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_251),u1_struct_0(B_254))))
      | ~ v1_funct_2(F_252,u1_struct_0(C_251),u1_struct_0(B_254))
      | ~ v1_funct_1(F_252)
      | ~ m1_pre_topc(E_255,D_256)
      | ~ m1_pre_topc(D_256,C_251)
      | ~ m1_pre_topc(E_255,A_253)
      | v2_struct_0(E_255)
      | ~ m1_pre_topc(D_256,A_253)
      | v2_struct_0(D_256)
      | ~ m1_pre_topc(C_251,A_253)
      | v2_struct_0(C_251)
      | ~ l1_pre_topc(B_254)
      | ~ v2_pre_topc(B_254)
      | v2_struct_0(B_254)
      | ~ l1_pre_topc(A_253)
      | ~ v2_pre_topc(A_253)
      | v2_struct_0(A_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_10,plain,(
    ! [D_9,C_8,A_6,B_7] :
      ( D_9 = C_8
      | ~ r2_funct_2(A_6,B_7,C_8,D_9)
      | ~ m1_subset_1(D_9,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7)))
      | ~ v1_funct_2(D_9,A_6,B_7)
      | ~ v1_funct_1(D_9)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7)))
      | ~ v1_funct_2(C_8,A_6,B_7)
      | ~ v1_funct_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_406,plain,(
    ! [D_313,A_314,B_312,C_311,F_315,E_316] :
      ( k3_tmap_1(A_314,B_312,D_313,E_316,k3_tmap_1(A_314,B_312,C_311,D_313,F_315)) = k3_tmap_1(A_314,B_312,C_311,E_316,F_315)
      | ~ m1_subset_1(k3_tmap_1(A_314,B_312,C_311,E_316,F_315),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(E_316),u1_struct_0(B_312))))
      | ~ v1_funct_2(k3_tmap_1(A_314,B_312,C_311,E_316,F_315),u1_struct_0(E_316),u1_struct_0(B_312))
      | ~ v1_funct_1(k3_tmap_1(A_314,B_312,C_311,E_316,F_315))
      | ~ m1_subset_1(k3_tmap_1(A_314,B_312,D_313,E_316,k3_tmap_1(A_314,B_312,C_311,D_313,F_315)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(E_316),u1_struct_0(B_312))))
      | ~ v1_funct_2(k3_tmap_1(A_314,B_312,D_313,E_316,k3_tmap_1(A_314,B_312,C_311,D_313,F_315)),u1_struct_0(E_316),u1_struct_0(B_312))
      | ~ v1_funct_1(k3_tmap_1(A_314,B_312,D_313,E_316,k3_tmap_1(A_314,B_312,C_311,D_313,F_315)))
      | ~ m1_subset_1(F_315,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_311),u1_struct_0(B_312))))
      | ~ v1_funct_2(F_315,u1_struct_0(C_311),u1_struct_0(B_312))
      | ~ v1_funct_1(F_315)
      | ~ m1_pre_topc(E_316,D_313)
      | ~ m1_pre_topc(D_313,C_311)
      | ~ m1_pre_topc(E_316,A_314)
      | v2_struct_0(E_316)
      | ~ m1_pre_topc(D_313,A_314)
      | v2_struct_0(D_313)
      | ~ m1_pre_topc(C_311,A_314)
      | v2_struct_0(C_311)
      | ~ l1_pre_topc(B_312)
      | ~ v2_pre_topc(B_312)
      | v2_struct_0(B_312)
      | ~ l1_pre_topc(A_314)
      | ~ v2_pre_topc(A_314)
      | v2_struct_0(A_314) ) ),
    inference(resolution,[status(thm)],[c_311,c_10])).

tff(c_490,plain,(
    ! [C_381,B_383,A_385,F_380,C_384,D_382] :
      ( k3_tmap_1(A_385,B_383,C_384,D_382,k3_tmap_1(A_385,B_383,C_381,C_384,F_380)) = k3_tmap_1(A_385,B_383,C_381,D_382,F_380)
      | ~ m1_subset_1(k3_tmap_1(A_385,B_383,C_381,D_382,F_380),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_382),u1_struct_0(B_383))))
      | ~ v1_funct_2(k3_tmap_1(A_385,B_383,C_381,D_382,F_380),u1_struct_0(D_382),u1_struct_0(B_383))
      | ~ v1_funct_1(k3_tmap_1(A_385,B_383,C_381,D_382,F_380))
      | ~ v1_funct_2(k3_tmap_1(A_385,B_383,C_384,D_382,k3_tmap_1(A_385,B_383,C_381,C_384,F_380)),u1_struct_0(D_382),u1_struct_0(B_383))
      | ~ v1_funct_1(k3_tmap_1(A_385,B_383,C_384,D_382,k3_tmap_1(A_385,B_383,C_381,C_384,F_380)))
      | ~ m1_subset_1(F_380,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_381),u1_struct_0(B_383))))
      | ~ v1_funct_2(F_380,u1_struct_0(C_381),u1_struct_0(B_383))
      | ~ v1_funct_1(F_380)
      | ~ m1_pre_topc(D_382,C_384)
      | ~ m1_pre_topc(C_384,C_381)
      | v2_struct_0(D_382)
      | v2_struct_0(C_384)
      | ~ m1_pre_topc(C_381,A_385)
      | v2_struct_0(C_381)
      | ~ m1_subset_1(k3_tmap_1(A_385,B_383,C_381,C_384,F_380),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_384),u1_struct_0(B_383))))
      | ~ v1_funct_2(k3_tmap_1(A_385,B_383,C_381,C_384,F_380),u1_struct_0(C_384),u1_struct_0(B_383))
      | ~ v1_funct_1(k3_tmap_1(A_385,B_383,C_381,C_384,F_380))
      | ~ m1_pre_topc(D_382,A_385)
      | ~ m1_pre_topc(C_384,A_385)
      | ~ l1_pre_topc(B_383)
      | ~ v2_pre_topc(B_383)
      | v2_struct_0(B_383)
      | ~ l1_pre_topc(A_385)
      | ~ v2_pre_topc(A_385)
      | v2_struct_0(A_385) ) ),
    inference(resolution,[status(thm)],[c_2,c_406])).

tff(c_494,plain,(
    ! [C_384] :
      ( k3_tmap_1('#skF_1','#skF_2',C_384,'#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4',C_384,'#skF_6')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6')
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',C_384,'#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4',C_384,'#skF_6')),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',C_384,'#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4',C_384,'#skF_6')))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc('#skF_5',C_384)
      | ~ m1_pre_topc(C_384,'#skF_4')
      | v2_struct_0('#skF_5')
      | v2_struct_0(C_384)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_4',C_384,'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_384),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4',C_384,'#skF_6'),u1_struct_0(C_384),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4',C_384,'#skF_6'))
      | ~ m1_pre_topc('#skF_5','#skF_1')
      | ~ m1_pre_topc(C_384,'#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_163,c_490])).

tff(c_500,plain,(
    ! [C_384] :
      ( k3_tmap_1('#skF_1','#skF_2',C_384,'#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4',C_384,'#skF_6')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6')
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',C_384,'#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4',C_384,'#skF_6')),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',C_384,'#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4',C_384,'#skF_6')))
      | ~ m1_pre_topc('#skF_5',C_384)
      | ~ m1_pre_topc(C_384,'#skF_4')
      | v2_struct_0('#skF_5')
      | v2_struct_0(C_384)
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_4',C_384,'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_384),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4',C_384,'#skF_6'),u1_struct_0(C_384),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4',C_384,'#skF_6'))
      | ~ m1_pre_topc(C_384,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_42,c_46,c_36,c_34,c_32,c_113,c_219,c_494])).

tff(c_506,plain,(
    ! [C_386] :
      ( k3_tmap_1('#skF_1','#skF_2',C_386,'#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4',C_386,'#skF_6')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6')
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',C_386,'#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4',C_386,'#skF_6')),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',C_386,'#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4',C_386,'#skF_6')))
      | ~ m1_pre_topc('#skF_5',C_386)
      | ~ m1_pre_topc(C_386,'#skF_4')
      | v2_struct_0(C_386)
      | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_4',C_386,'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_386),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4',C_386,'#skF_6'),u1_struct_0(C_386),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4',C_386,'#skF_6'))
      | ~ m1_pre_topc(C_386,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_48,c_44,c_500])).

tff(c_516,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')))
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | v2_struct_0('#skF_3')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'))
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_506])).

tff(c_527,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_30,c_28,c_40,c_38,c_516])).

tff(c_528,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_527])).

tff(c_529,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_528])).

tff(c_532,plain,
    ( ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'))
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_337,c_529])).

tff(c_538,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_46,c_50,c_42,c_30,c_532])).

tff(c_540,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_538])).

tff(c_541,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')),u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_528])).

tff(c_544,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')),u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_541])).

tff(c_547,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'))
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_276,c_544])).

tff(c_553,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_46,c_50,c_36,c_34,c_32,c_42,c_30,c_28,c_547])).

tff(c_555,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_553])).

tff(c_556,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_5',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_541])).

tff(c_282,plain,(
    ! [E_239,A_243,B_242,D_241,C_240] :
      ( v5_pre_topc(k3_tmap_1(A_243,B_242,C_240,D_241,E_239),D_241,B_242)
      | ~ m1_pre_topc(D_241,C_240)
      | ~ m1_subset_1(E_239,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_240),u1_struct_0(B_242))))
      | ~ v5_pre_topc(E_239,C_240,B_242)
      | ~ v1_funct_2(E_239,u1_struct_0(C_240),u1_struct_0(B_242))
      | ~ v1_funct_1(E_239)
      | ~ m1_pre_topc(D_241,A_243)
      | v2_struct_0(D_241)
      | ~ m1_pre_topc(C_240,A_243)
      | v2_struct_0(C_240)
      | ~ l1_pre_topc(B_242)
      | ~ v2_pre_topc(B_242)
      | v2_struct_0(B_242)
      | ~ l1_pre_topc(A_243)
      | ~ v2_pre_topc(A_243)
      | v2_struct_0(A_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_353,plain,(
    ! [D_285,A_289,A_288,B_286,D_283,E_284,C_287] :
      ( v5_pre_topc(k3_tmap_1(A_289,B_286,D_285,D_283,k3_tmap_1(A_288,B_286,C_287,D_285,E_284)),D_283,B_286)
      | ~ m1_pre_topc(D_283,D_285)
      | ~ v5_pre_topc(k3_tmap_1(A_288,B_286,C_287,D_285,E_284),D_285,B_286)
      | ~ v1_funct_2(k3_tmap_1(A_288,B_286,C_287,D_285,E_284),u1_struct_0(D_285),u1_struct_0(B_286))
      | ~ v1_funct_1(k3_tmap_1(A_288,B_286,C_287,D_285,E_284))
      | ~ m1_pre_topc(D_283,A_289)
      | v2_struct_0(D_283)
      | ~ m1_pre_topc(D_285,A_289)
      | v2_struct_0(D_285)
      | ~ l1_pre_topc(A_289)
      | ~ v2_pre_topc(A_289)
      | v2_struct_0(A_289)
      | ~ m1_subset_1(E_284,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_287),u1_struct_0(B_286))))
      | ~ v1_funct_2(E_284,u1_struct_0(C_287),u1_struct_0(B_286))
      | ~ v1_funct_1(E_284)
      | ~ m1_pre_topc(D_285,A_288)
      | ~ m1_pre_topc(C_287,A_288)
      | ~ l1_pre_topc(B_286)
      | ~ v2_pre_topc(B_286)
      | v2_struct_0(B_286)
      | ~ l1_pre_topc(A_288)
      | ~ v2_pre_topc(A_288)
      | v2_struct_0(A_288) ) ),
    inference(resolution,[status(thm)],[c_2,c_282])).

tff(c_361,plain,(
    ! [A_289,D_224,D_283,A_227] :
      ( v5_pre_topc(k3_tmap_1(A_289,'#skF_2',D_224,D_283,k3_tmap_1(A_227,'#skF_2','#skF_4',D_224,'#skF_6')),D_283,'#skF_2')
      | ~ m1_pre_topc(D_283,D_224)
      | ~ v5_pre_topc(k3_tmap_1(A_227,'#skF_2','#skF_4',D_224,'#skF_6'),D_224,'#skF_2')
      | ~ v1_funct_1(k3_tmap_1(A_227,'#skF_2','#skF_4',D_224,'#skF_6'))
      | ~ m1_pre_topc(D_283,A_289)
      | v2_struct_0(D_283)
      | ~ m1_pre_topc(D_224,A_289)
      | v2_struct_0(D_224)
      | ~ l1_pre_topc(A_289)
      | ~ v2_pre_topc(A_289)
      | v2_struct_0(A_289)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(D_224,A_227)
      | ~ m1_pre_topc('#skF_4',A_227)
      | ~ l1_pre_topc(A_227)
      | ~ v2_pre_topc(A_227)
      | v2_struct_0(A_227) ) ),
    inference(resolution,[status(thm)],[c_268,c_353])).

tff(c_377,plain,(
    ! [A_289,D_224,D_283,A_227] :
      ( v5_pre_topc(k3_tmap_1(A_289,'#skF_2',D_224,D_283,k3_tmap_1(A_227,'#skF_2','#skF_4',D_224,'#skF_6')),D_283,'#skF_2')
      | ~ m1_pre_topc(D_283,D_224)
      | ~ v5_pre_topc(k3_tmap_1(A_227,'#skF_2','#skF_4',D_224,'#skF_6'),D_224,'#skF_2')
      | ~ v1_funct_1(k3_tmap_1(A_227,'#skF_2','#skF_4',D_224,'#skF_6'))
      | ~ m1_pre_topc(D_283,A_289)
      | v2_struct_0(D_283)
      | ~ m1_pre_topc(D_224,A_289)
      | v2_struct_0(D_224)
      | ~ l1_pre_topc(A_289)
      | ~ v2_pre_topc(A_289)
      | v2_struct_0(A_289)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(D_224,A_227)
      | ~ m1_pre_topc('#skF_4',A_227)
      | ~ l1_pre_topc(A_227)
      | ~ v2_pre_topc(A_227)
      | v2_struct_0(A_227) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_36,c_34,c_32,c_361])).

tff(c_378,plain,(
    ! [A_289,D_224,D_283,A_227] :
      ( v5_pre_topc(k3_tmap_1(A_289,'#skF_2',D_224,D_283,k3_tmap_1(A_227,'#skF_2','#skF_4',D_224,'#skF_6')),D_283,'#skF_2')
      | ~ m1_pre_topc(D_283,D_224)
      | ~ v5_pre_topc(k3_tmap_1(A_227,'#skF_2','#skF_4',D_224,'#skF_6'),D_224,'#skF_2')
      | ~ v1_funct_1(k3_tmap_1(A_227,'#skF_2','#skF_4',D_224,'#skF_6'))
      | ~ m1_pre_topc(D_283,A_289)
      | v2_struct_0(D_283)
      | ~ m1_pre_topc(D_224,A_289)
      | v2_struct_0(D_224)
      | ~ l1_pre_topc(A_289)
      | ~ v2_pre_topc(A_289)
      | v2_struct_0(A_289)
      | ~ m1_pre_topc(D_224,A_227)
      | ~ m1_pre_topc('#skF_4',A_227)
      | ~ l1_pre_topc(A_227)
      | ~ v2_pre_topc(A_227)
      | v2_struct_0(A_227) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_377])).

tff(c_631,plain,
    ( v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),'#skF_5','#skF_2')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_6'))
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_556,c_378])).

tff(c_705,plain,
    ( v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_5','#skF_6'),'#skF_5','#skF_2')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_46,c_50,c_62,c_60,c_50,c_42,c_30,c_26,c_38,c_631])).

tff(c_707,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_52,c_44,c_218,c_705])).

%------------------------------------------------------------------------------
