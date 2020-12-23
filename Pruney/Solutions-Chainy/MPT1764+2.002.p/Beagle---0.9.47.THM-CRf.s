%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:13 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 280 expanded)
%              Number of leaves         :   40 ( 121 expanded)
%              Depth                    :   15
%              Number of atoms          :  274 (1656 expanded)
%              Number of equality atoms :   38 ( 118 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_192,negated_conjecture,(
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
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(D),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                       => ( m1_pre_topc(C,D)
                         => ! [F] :
                              ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(D)))
                             => ( r1_tarski(F,u1_struct_0(C))
                               => k7_relset_1(u1_struct_0(D),u1_struct_0(B),E,F) = k7_relset_1(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,D,C,E),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_tmap_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_98,axiom,(
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
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_148,axiom,(
    ! [A,B,C,D] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B)
        & v1_funct_1(C)
        & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B))))
        & l1_struct_0(D) )
     => ( v1_funct_1(k2_tmap_1(A,B,C,D))
        & v1_funct_2(k2_tmap_1(A,B,C,D),u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(k2_tmap_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

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
              ( m1_pre_topc(C,A)
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ( m1_pre_topc(D,C)
                       => k3_tmap_1(A,B,C,D,E) = k2_partfun1(u1_struct_0(C),u1_struct_0(B),E,u1_struct_0(D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

tff(c_56,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_46,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_63,plain,(
    ! [B_136,A_137] :
      ( l1_pre_topc(B_136)
      | ~ m1_pre_topc(B_136,A_137)
      | ~ l1_pre_topc(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_69,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_63])).

tff(c_78,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_69])).

tff(c_14,plain,(
    ! [A_22] :
      ( l1_struct_0(A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_34,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_30,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_82,plain,(
    ! [B_138,A_139] :
      ( v1_relat_1(B_138)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(A_139))
      | ~ v1_relat_1(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_85,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_36,c_82])).

tff(c_91,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_85])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_58,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_42,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_94,plain,(
    ! [B_140,A_141] :
      ( v2_pre_topc(B_140)
      | ~ m1_pre_topc(B_140,A_141)
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_97,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_94])).

tff(c_106,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_97])).

tff(c_66,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_63])).

tff(c_75,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_66])).

tff(c_52,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_38,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_138,plain,(
    ! [A_150,B_151,C_152,D_153] :
      ( k2_partfun1(A_150,B_151,C_152,D_153) = k7_relat_1(C_152,D_153)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151)))
      | ~ v1_funct_1(C_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_140,plain,(
    ! [D_153] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_153) = k7_relat_1('#skF_5',D_153)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_138])).

tff(c_143,plain,(
    ! [D_153] : k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_153) = k7_relat_1('#skF_5',D_153) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_140])).

tff(c_234,plain,(
    ! [A_181,B_182,C_183,D_184] :
      ( k2_partfun1(u1_struct_0(A_181),u1_struct_0(B_182),C_183,u1_struct_0(D_184)) = k2_tmap_1(A_181,B_182,C_183,D_184)
      | ~ m1_pre_topc(D_184,A_181)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_181),u1_struct_0(B_182))))
      | ~ v1_funct_2(C_183,u1_struct_0(A_181),u1_struct_0(B_182))
      | ~ v1_funct_1(C_183)
      | ~ l1_pre_topc(B_182)
      | ~ v2_pre_topc(B_182)
      | v2_struct_0(B_182)
      | ~ l1_pre_topc(A_181)
      | ~ v2_pre_topc(A_181)
      | v2_struct_0(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_238,plain,(
    ! [D_184] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_184)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_184)
      | ~ m1_pre_topc(D_184,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_234])).

tff(c_242,plain,(
    ! [D_184] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_184)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_184)
      | ~ m1_pre_topc(D_184,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_75,c_52,c_50,c_40,c_38,c_143,c_238])).

tff(c_244,plain,(
    ! [D_185] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_185)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_185)
      | ~ m1_pre_topc(D_185,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_54,c_242])).

tff(c_6,plain,(
    ! [A_6,C_10,B_9] :
      ( k9_relat_1(k7_relat_1(A_6,C_10),B_9) = k9_relat_1(A_6,B_9)
      | ~ r1_tarski(B_9,C_10)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_250,plain,(
    ! [D_185,B_9] :
      ( k9_relat_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_185),B_9) = k9_relat_1('#skF_5',B_9)
      | ~ r1_tarski(B_9,u1_struct_0(D_185))
      | ~ v1_relat_1('#skF_5')
      | ~ m1_pre_topc(D_185,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_6])).

tff(c_258,plain,(
    ! [D_186,B_187] :
      ( k9_relat_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_186),B_187) = k9_relat_1('#skF_5',B_187)
      | ~ r1_tarski(B_187,u1_struct_0(D_186))
      | ~ m1_pre_topc(D_186,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_250])).

tff(c_261,plain,
    ( k9_relat_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') = k9_relat_1('#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_258])).

tff(c_264,plain,(
    k9_relat_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') = k9_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_261])).

tff(c_153,plain,(
    ! [A_155,B_156,C_157,D_158] :
      ( v1_funct_1(k2_tmap_1(A_155,B_156,C_157,D_158))
      | ~ l1_struct_0(D_158)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_155),u1_struct_0(B_156))))
      | ~ v1_funct_2(C_157,u1_struct_0(A_155),u1_struct_0(B_156))
      | ~ v1_funct_1(C_157)
      | ~ l1_struct_0(B_156)
      | ~ l1_struct_0(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_155,plain,(
    ! [D_158] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_158))
      | ~ l1_struct_0(D_158)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_153])).

tff(c_158,plain,(
    ! [D_158] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_158))
      | ~ l1_struct_0(D_158)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_155])).

tff(c_159,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_158])).

tff(c_162,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_159])).

tff(c_166,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_162])).

tff(c_168,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_167,plain,(
    ! [D_158] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_158))
      | ~ l1_struct_0(D_158) ) ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_169,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_167])).

tff(c_172,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_169])).

tff(c_176,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_172])).

tff(c_178,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_187,plain,(
    ! [A_165,B_166,C_167,D_168] :
      ( m1_subset_1(k2_tmap_1(A_165,B_166,C_167,D_168),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_168),u1_struct_0(B_166))))
      | ~ l1_struct_0(D_168)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_165),u1_struct_0(B_166))))
      | ~ v1_funct_2(C_167,u1_struct_0(A_165),u1_struct_0(B_166))
      | ~ v1_funct_1(C_167)
      | ~ l1_struct_0(B_166)
      | ~ l1_struct_0(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_8,plain,(
    ! [A_11,B_12,C_13,D_14] :
      ( k7_relset_1(A_11,B_12,C_13,D_14) = k9_relat_1(C_13,D_14)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_216,plain,(
    ! [D_177,A_176,D_178,B_175,C_174] :
      ( k7_relset_1(u1_struct_0(D_177),u1_struct_0(B_175),k2_tmap_1(A_176,B_175,C_174,D_177),D_178) = k9_relat_1(k2_tmap_1(A_176,B_175,C_174,D_177),D_178)
      | ~ l1_struct_0(D_177)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_176),u1_struct_0(B_175))))
      | ~ v1_funct_2(C_174,u1_struct_0(A_176),u1_struct_0(B_175))
      | ~ v1_funct_1(C_174)
      | ~ l1_struct_0(B_175)
      | ~ l1_struct_0(A_176) ) ),
    inference(resolution,[status(thm)],[c_187,c_8])).

tff(c_220,plain,(
    ! [D_177,D_178] :
      ( k7_relset_1(u1_struct_0(D_177),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5',D_177),D_178) = k9_relat_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_177),D_178)
      | ~ l1_struct_0(D_177)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_216])).

tff(c_224,plain,(
    ! [D_177,D_178] :
      ( k7_relset_1(u1_struct_0(D_177),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5',D_177),D_178) = k9_relat_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_177),D_178)
      | ~ l1_struct_0(D_177) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_178,c_40,c_38,c_220])).

tff(c_243,plain,(
    ! [D_184] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_184)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_184)
      | ~ m1_pre_topc(D_184,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_54,c_242])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_265,plain,(
    ! [D_192,A_188,B_190,E_189,C_191] :
      ( k3_tmap_1(A_188,B_190,C_191,D_192,E_189) = k2_partfun1(u1_struct_0(C_191),u1_struct_0(B_190),E_189,u1_struct_0(D_192))
      | ~ m1_pre_topc(D_192,C_191)
      | ~ m1_subset_1(E_189,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_191),u1_struct_0(B_190))))
      | ~ v1_funct_2(E_189,u1_struct_0(C_191),u1_struct_0(B_190))
      | ~ v1_funct_1(E_189)
      | ~ m1_pre_topc(D_192,A_188)
      | ~ m1_pre_topc(C_191,A_188)
      | ~ l1_pre_topc(B_190)
      | ~ v2_pre_topc(B_190)
      | v2_struct_0(B_190)
      | ~ l1_pre_topc(A_188)
      | ~ v2_pre_topc(A_188)
      | v2_struct_0(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_269,plain,(
    ! [A_188,D_192] :
      ( k3_tmap_1(A_188,'#skF_2','#skF_4',D_192,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_192))
      | ~ m1_pre_topc(D_192,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_192,A_188)
      | ~ m1_pre_topc('#skF_4',A_188)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_188)
      | ~ v2_pre_topc(A_188)
      | v2_struct_0(A_188) ) ),
    inference(resolution,[status(thm)],[c_36,c_265])).

tff(c_273,plain,(
    ! [D_192,A_188] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_192)) = k3_tmap_1(A_188,'#skF_2','#skF_4',D_192,'#skF_5')
      | ~ m1_pre_topc(D_192,'#skF_4')
      | ~ m1_pre_topc(D_192,A_188)
      | ~ m1_pre_topc('#skF_4',A_188)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_188)
      | ~ v2_pre_topc(A_188)
      | v2_struct_0(A_188) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_40,c_38,c_143,c_269])).

tff(c_279,plain,(
    ! [D_193,A_194] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_193)) = k3_tmap_1(A_194,'#skF_2','#skF_4',D_193,'#skF_5')
      | ~ m1_pre_topc(D_193,'#skF_4')
      | ~ m1_pre_topc(D_193,A_194)
      | ~ m1_pre_topc('#skF_4',A_194)
      | ~ l1_pre_topc(A_194)
      | ~ v2_pre_topc(A_194)
      | v2_struct_0(A_194) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_273])).

tff(c_283,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_279])).

tff(c_292,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_42,c_34,c_283])).

tff(c_293,plain,(
    k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_292])).

tff(c_308,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_293])).

tff(c_316,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_308])).

tff(c_124,plain,(
    ! [A_145,B_146,C_147,D_148] :
      ( k7_relset_1(A_145,B_146,C_147,D_148) = k9_relat_1(C_147,D_148)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_127,plain,(
    ! [D_148] : k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_148) = k9_relat_1('#skF_5',D_148) ),
    inference(resolution,[status(thm)],[c_36,c_124])).

tff(c_28,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_128,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k9_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_28])).

tff(c_319,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') != k9_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_128])).

tff(c_358,plain,
    ( k9_relat_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') != k9_relat_1('#skF_5','#skF_6')
    | ~ l1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_319])).

tff(c_360,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_358])).

tff(c_363,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_360])).

tff(c_367,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_363])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:12:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.38  
% 2.94/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.38  %$ v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.94/1.38  
% 2.94/1.38  %Foreground sorts:
% 2.94/1.38  
% 2.94/1.38  
% 2.94/1.38  %Background operators:
% 2.94/1.38  
% 2.94/1.38  
% 2.94/1.38  %Foreground operators:
% 2.94/1.38  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.94/1.38  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 2.94/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.94/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.94/1.38  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.94/1.38  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.94/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.94/1.38  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.94/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.94/1.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.94/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.94/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.94/1.38  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.94/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.94/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.94/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.94/1.38  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.94/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.94/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.94/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.94/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.94/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.94/1.38  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.94/1.38  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.94/1.38  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.94/1.38  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 2.94/1.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.94/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.94/1.38  
% 2.94/1.40  tff(f_192, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (r1_tarski(F, u1_struct_0(C)) => (k7_relset_1(u1_struct_0(D), u1_struct_0(B), E, F) = k7_relset_1(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, E), F)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_tmap_1)).
% 2.94/1.40  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.94/1.40  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.94/1.40  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.94/1.40  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.94/1.40  tff(f_60, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 2.94/1.40  tff(f_51, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.94/1.40  tff(f_98, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 2.94/1.40  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 2.94/1.40  tff(f_148, axiom, (![A, B, C, D]: ((((((l1_struct_0(A) & l1_struct_0(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & l1_struct_0(D)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 2.94/1.40  tff(f_45, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.94/1.40  tff(f_130, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 2.94/1.40  tff(c_56, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_192])).
% 2.94/1.40  tff(c_46, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_192])).
% 2.94/1.40  tff(c_63, plain, (![B_136, A_137]: (l1_pre_topc(B_136) | ~m1_pre_topc(B_136, A_137) | ~l1_pre_topc(A_137))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.94/1.40  tff(c_69, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_63])).
% 2.94/1.40  tff(c_78, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_69])).
% 2.94/1.40  tff(c_14, plain, (![A_22]: (l1_struct_0(A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.94/1.40  tff(c_34, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_192])).
% 2.94/1.40  tff(c_30, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_192])).
% 2.94/1.40  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.94/1.40  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_192])).
% 2.94/1.40  tff(c_82, plain, (![B_138, A_139]: (v1_relat_1(B_138) | ~m1_subset_1(B_138, k1_zfmisc_1(A_139)) | ~v1_relat_1(A_139))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.94/1.40  tff(c_85, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_36, c_82])).
% 2.94/1.40  tff(c_91, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_85])).
% 2.94/1.40  tff(c_44, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_192])).
% 2.94/1.40  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 2.94/1.40  tff(c_58, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_192])).
% 2.94/1.40  tff(c_42, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_192])).
% 2.94/1.40  tff(c_94, plain, (![B_140, A_141]: (v2_pre_topc(B_140) | ~m1_pre_topc(B_140, A_141) | ~l1_pre_topc(A_141) | ~v2_pre_topc(A_141))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.94/1.40  tff(c_97, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_94])).
% 2.94/1.40  tff(c_106, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_97])).
% 2.94/1.40  tff(c_66, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_63])).
% 2.94/1.40  tff(c_75, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_66])).
% 2.94/1.40  tff(c_52, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 2.94/1.40  tff(c_50, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_192])).
% 2.94/1.40  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_192])).
% 2.94/1.40  tff(c_38, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_192])).
% 2.94/1.40  tff(c_138, plain, (![A_150, B_151, C_152, D_153]: (k2_partfun1(A_150, B_151, C_152, D_153)=k7_relat_1(C_152, D_153) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))) | ~v1_funct_1(C_152))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.94/1.40  tff(c_140, plain, (![D_153]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_153)=k7_relat_1('#skF_5', D_153) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_36, c_138])).
% 2.94/1.40  tff(c_143, plain, (![D_153]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_153)=k7_relat_1('#skF_5', D_153))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_140])).
% 2.94/1.40  tff(c_234, plain, (![A_181, B_182, C_183, D_184]: (k2_partfun1(u1_struct_0(A_181), u1_struct_0(B_182), C_183, u1_struct_0(D_184))=k2_tmap_1(A_181, B_182, C_183, D_184) | ~m1_pre_topc(D_184, A_181) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_181), u1_struct_0(B_182)))) | ~v1_funct_2(C_183, u1_struct_0(A_181), u1_struct_0(B_182)) | ~v1_funct_1(C_183) | ~l1_pre_topc(B_182) | ~v2_pre_topc(B_182) | v2_struct_0(B_182) | ~l1_pre_topc(A_181) | ~v2_pre_topc(A_181) | v2_struct_0(A_181))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.94/1.40  tff(c_238, plain, (![D_184]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_184))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_184) | ~m1_pre_topc(D_184, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_36, c_234])).
% 2.94/1.40  tff(c_242, plain, (![D_184]: (k7_relat_1('#skF_5', u1_struct_0(D_184))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_184) | ~m1_pre_topc(D_184, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_75, c_52, c_50, c_40, c_38, c_143, c_238])).
% 2.94/1.40  tff(c_244, plain, (![D_185]: (k7_relat_1('#skF_5', u1_struct_0(D_185))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_185) | ~m1_pre_topc(D_185, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_44, c_54, c_242])).
% 2.94/1.40  tff(c_6, plain, (![A_6, C_10, B_9]: (k9_relat_1(k7_relat_1(A_6, C_10), B_9)=k9_relat_1(A_6, B_9) | ~r1_tarski(B_9, C_10) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.94/1.40  tff(c_250, plain, (![D_185, B_9]: (k9_relat_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_185), B_9)=k9_relat_1('#skF_5', B_9) | ~r1_tarski(B_9, u1_struct_0(D_185)) | ~v1_relat_1('#skF_5') | ~m1_pre_topc(D_185, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_244, c_6])).
% 2.94/1.40  tff(c_258, plain, (![D_186, B_187]: (k9_relat_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_186), B_187)=k9_relat_1('#skF_5', B_187) | ~r1_tarski(B_187, u1_struct_0(D_186)) | ~m1_pre_topc(D_186, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_250])).
% 2.94/1.40  tff(c_261, plain, (k9_relat_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')=k9_relat_1('#skF_5', '#skF_6') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_258])).
% 2.94/1.40  tff(c_264, plain, (k9_relat_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')=k9_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_261])).
% 2.94/1.40  tff(c_153, plain, (![A_155, B_156, C_157, D_158]: (v1_funct_1(k2_tmap_1(A_155, B_156, C_157, D_158)) | ~l1_struct_0(D_158) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_155), u1_struct_0(B_156)))) | ~v1_funct_2(C_157, u1_struct_0(A_155), u1_struct_0(B_156)) | ~v1_funct_1(C_157) | ~l1_struct_0(B_156) | ~l1_struct_0(A_155))), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.94/1.40  tff(c_155, plain, (![D_158]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_158)) | ~l1_struct_0(D_158) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_36, c_153])).
% 2.94/1.40  tff(c_158, plain, (![D_158]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_158)) | ~l1_struct_0(D_158) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_155])).
% 2.94/1.40  tff(c_159, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_158])).
% 2.94/1.40  tff(c_162, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_14, c_159])).
% 2.94/1.40  tff(c_166, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_162])).
% 2.94/1.40  tff(c_168, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_158])).
% 2.94/1.40  tff(c_167, plain, (![D_158]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_158)) | ~l1_struct_0(D_158))), inference(splitRight, [status(thm)], [c_158])).
% 2.94/1.40  tff(c_169, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_167])).
% 2.94/1.40  tff(c_172, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_169])).
% 2.94/1.40  tff(c_176, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_172])).
% 2.94/1.40  tff(c_178, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_167])).
% 2.94/1.40  tff(c_187, plain, (![A_165, B_166, C_167, D_168]: (m1_subset_1(k2_tmap_1(A_165, B_166, C_167, D_168), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_168), u1_struct_0(B_166)))) | ~l1_struct_0(D_168) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_165), u1_struct_0(B_166)))) | ~v1_funct_2(C_167, u1_struct_0(A_165), u1_struct_0(B_166)) | ~v1_funct_1(C_167) | ~l1_struct_0(B_166) | ~l1_struct_0(A_165))), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.94/1.40  tff(c_8, plain, (![A_11, B_12, C_13, D_14]: (k7_relset_1(A_11, B_12, C_13, D_14)=k9_relat_1(C_13, D_14) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.94/1.40  tff(c_216, plain, (![D_177, A_176, D_178, B_175, C_174]: (k7_relset_1(u1_struct_0(D_177), u1_struct_0(B_175), k2_tmap_1(A_176, B_175, C_174, D_177), D_178)=k9_relat_1(k2_tmap_1(A_176, B_175, C_174, D_177), D_178) | ~l1_struct_0(D_177) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_176), u1_struct_0(B_175)))) | ~v1_funct_2(C_174, u1_struct_0(A_176), u1_struct_0(B_175)) | ~v1_funct_1(C_174) | ~l1_struct_0(B_175) | ~l1_struct_0(A_176))), inference(resolution, [status(thm)], [c_187, c_8])).
% 2.94/1.40  tff(c_220, plain, (![D_177, D_178]: (k7_relset_1(u1_struct_0(D_177), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_177), D_178)=k9_relat_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_177), D_178) | ~l1_struct_0(D_177) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_36, c_216])).
% 2.94/1.40  tff(c_224, plain, (![D_177, D_178]: (k7_relset_1(u1_struct_0(D_177), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_177), D_178)=k9_relat_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_177), D_178) | ~l1_struct_0(D_177))), inference(demodulation, [status(thm), theory('equality')], [c_168, c_178, c_40, c_38, c_220])).
% 2.94/1.40  tff(c_243, plain, (![D_184]: (k7_relat_1('#skF_5', u1_struct_0(D_184))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_184) | ~m1_pre_topc(D_184, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_44, c_54, c_242])).
% 2.94/1.40  tff(c_60, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_192])).
% 2.94/1.40  tff(c_265, plain, (![D_192, A_188, B_190, E_189, C_191]: (k3_tmap_1(A_188, B_190, C_191, D_192, E_189)=k2_partfun1(u1_struct_0(C_191), u1_struct_0(B_190), E_189, u1_struct_0(D_192)) | ~m1_pre_topc(D_192, C_191) | ~m1_subset_1(E_189, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_191), u1_struct_0(B_190)))) | ~v1_funct_2(E_189, u1_struct_0(C_191), u1_struct_0(B_190)) | ~v1_funct_1(E_189) | ~m1_pre_topc(D_192, A_188) | ~m1_pre_topc(C_191, A_188) | ~l1_pre_topc(B_190) | ~v2_pre_topc(B_190) | v2_struct_0(B_190) | ~l1_pre_topc(A_188) | ~v2_pre_topc(A_188) | v2_struct_0(A_188))), inference(cnfTransformation, [status(thm)], [f_130])).
% 2.94/1.40  tff(c_269, plain, (![A_188, D_192]: (k3_tmap_1(A_188, '#skF_2', '#skF_4', D_192, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_192)) | ~m1_pre_topc(D_192, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_192, A_188) | ~m1_pre_topc('#skF_4', A_188) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_188) | ~v2_pre_topc(A_188) | v2_struct_0(A_188))), inference(resolution, [status(thm)], [c_36, c_265])).
% 2.94/1.40  tff(c_273, plain, (![D_192, A_188]: (k7_relat_1('#skF_5', u1_struct_0(D_192))=k3_tmap_1(A_188, '#skF_2', '#skF_4', D_192, '#skF_5') | ~m1_pre_topc(D_192, '#skF_4') | ~m1_pre_topc(D_192, A_188) | ~m1_pre_topc('#skF_4', A_188) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_188) | ~v2_pre_topc(A_188) | v2_struct_0(A_188))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_40, c_38, c_143, c_269])).
% 2.94/1.40  tff(c_279, plain, (![D_193, A_194]: (k7_relat_1('#skF_5', u1_struct_0(D_193))=k3_tmap_1(A_194, '#skF_2', '#skF_4', D_193, '#skF_5') | ~m1_pre_topc(D_193, '#skF_4') | ~m1_pre_topc(D_193, A_194) | ~m1_pre_topc('#skF_4', A_194) | ~l1_pre_topc(A_194) | ~v2_pre_topc(A_194) | v2_struct_0(A_194))), inference(negUnitSimplification, [status(thm)], [c_54, c_273])).
% 2.94/1.40  tff(c_283, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_279])).
% 2.94/1.40  tff(c_292, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_42, c_34, c_283])).
% 2.94/1.40  tff(c_293, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_60, c_292])).
% 2.94/1.40  tff(c_308, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_243, c_293])).
% 2.94/1.40  tff(c_316, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_308])).
% 2.94/1.40  tff(c_124, plain, (![A_145, B_146, C_147, D_148]: (k7_relset_1(A_145, B_146, C_147, D_148)=k9_relat_1(C_147, D_148) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.94/1.40  tff(c_127, plain, (![D_148]: (k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_148)=k9_relat_1('#skF_5', D_148))), inference(resolution, [status(thm)], [c_36, c_124])).
% 2.94/1.40  tff(c_28, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_192])).
% 2.94/1.40  tff(c_128, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k9_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_28])).
% 2.94/1.40  tff(c_319, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')!=k9_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_316, c_128])).
% 2.94/1.40  tff(c_358, plain, (k9_relat_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')!=k9_relat_1('#skF_5', '#skF_6') | ~l1_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_224, c_319])).
% 2.94/1.40  tff(c_360, plain, (~l1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_264, c_358])).
% 2.94/1.40  tff(c_363, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_14, c_360])).
% 2.94/1.40  tff(c_367, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_363])).
% 2.94/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.40  
% 2.94/1.40  Inference rules
% 2.94/1.40  ----------------------
% 2.94/1.40  #Ref     : 0
% 2.94/1.40  #Sup     : 60
% 2.94/1.40  #Fact    : 0
% 2.94/1.40  #Define  : 0
% 2.94/1.40  #Split   : 4
% 2.94/1.40  #Chain   : 0
% 2.94/1.40  #Close   : 0
% 2.94/1.40  
% 2.94/1.40  Ordering : KBO
% 2.94/1.40  
% 2.94/1.40  Simplification rules
% 2.94/1.40  ----------------------
% 2.94/1.40  #Subsume      : 1
% 2.94/1.40  #Demod        : 71
% 2.94/1.40  #Tautology    : 23
% 2.94/1.40  #SimpNegUnit  : 5
% 2.94/1.40  #BackRed      : 3
% 2.94/1.40  
% 2.94/1.40  #Partial instantiations: 0
% 2.94/1.40  #Strategies tried      : 1
% 2.94/1.40  
% 2.94/1.40  Timing (in seconds)
% 2.94/1.40  ----------------------
% 2.94/1.40  Preprocessing        : 0.36
% 2.94/1.40  Parsing              : 0.19
% 2.94/1.40  CNF conversion       : 0.03
% 2.94/1.40  Main loop            : 0.27
% 2.94/1.40  Inferencing          : 0.10
% 2.94/1.40  Reduction            : 0.09
% 2.94/1.40  Demodulation         : 0.06
% 2.94/1.40  BG Simplification    : 0.02
% 2.94/1.41  Subsumption          : 0.04
% 2.94/1.41  Abstraction          : 0.02
% 2.94/1.41  MUC search           : 0.00
% 2.94/1.41  Cooper               : 0.00
% 2.94/1.41  Total                : 0.67
% 2.94/1.41  Index Insertion      : 0.00
% 2.94/1.41  Index Deletion       : 0.00
% 2.94/1.41  Index Matching       : 0.00
% 2.94/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
