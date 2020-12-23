%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:14 EST 2020

% Result     : Theorem 5.95s
% Output     : CNFRefutation 5.95s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 238 expanded)
%              Number of leaves         :   44 ( 107 expanded)
%              Depth                    :   12
%              Number of atoms          :  205 (1282 expanded)
%              Number of equality atoms :   32 ( 107 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k7_relset_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_165,negated_conjecture,(
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

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_121,axiom,(
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

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ( r1_tarski(A,D)
       => m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_34,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_75,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_40,c_2])).

tff(c_78,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_75])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_62,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_60,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_46,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_38,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_50,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_56,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_54,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_42,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_174,plain,(
    ! [A_170,B_171,C_172,D_173] :
      ( k2_partfun1(A_170,B_171,C_172,D_173) = k7_relat_1(C_172,D_173)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171)))
      | ~ v1_funct_1(C_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_178,plain,(
    ! [D_173] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_173) = k7_relat_1('#skF_5',D_173)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_174])).

tff(c_182,plain,(
    ! [D_173] : k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_173) = k7_relat_1('#skF_5',D_173) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_178])).

tff(c_230,plain,(
    ! [D_188,C_185,B_186,E_187,A_184] :
      ( k3_tmap_1(A_184,B_186,C_185,D_188,E_187) = k2_partfun1(u1_struct_0(C_185),u1_struct_0(B_186),E_187,u1_struct_0(D_188))
      | ~ m1_pre_topc(D_188,C_185)
      | ~ m1_subset_1(E_187,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_185),u1_struct_0(B_186))))
      | ~ v1_funct_2(E_187,u1_struct_0(C_185),u1_struct_0(B_186))
      | ~ v1_funct_1(E_187)
      | ~ m1_pre_topc(D_188,A_184)
      | ~ m1_pre_topc(C_185,A_184)
      | ~ l1_pre_topc(B_186)
      | ~ v2_pre_topc(B_186)
      | v2_struct_0(B_186)
      | ~ l1_pre_topc(A_184)
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_238,plain,(
    ! [A_184,D_188] :
      ( k3_tmap_1(A_184,'#skF_2','#skF_4',D_188,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_188))
      | ~ m1_pre_topc(D_188,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_188,A_184)
      | ~ m1_pre_topc('#skF_4',A_184)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_184)
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184) ) ),
    inference(resolution,[status(thm)],[c_40,c_230])).

tff(c_243,plain,(
    ! [D_188,A_184] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_188)) = k3_tmap_1(A_184,'#skF_2','#skF_4',D_188,'#skF_5')
      | ~ m1_pre_topc(D_188,'#skF_4')
      | ~ m1_pre_topc(D_188,A_184)
      | ~ m1_pre_topc('#skF_4',A_184)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_184)
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_44,c_42,c_182,c_238])).

tff(c_258,plain,(
    ! [D_194,A_195] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_194)) = k3_tmap_1(A_195,'#skF_2','#skF_4',D_194,'#skF_5')
      | ~ m1_pre_topc(D_194,'#skF_4')
      | ~ m1_pre_topc(D_194,A_195)
      | ~ m1_pre_topc('#skF_4',A_195)
      | ~ l1_pre_topc(A_195)
      | ~ v2_pre_topc(A_195)
      | v2_struct_0(A_195) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_243])).

tff(c_260,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_258])).

tff(c_267,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_46,c_38,c_260])).

tff(c_268,plain,(
    k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_267])).

tff(c_10,plain,(
    ! [A_8,C_12,B_11] :
      ( k9_relat_1(k7_relat_1(A_8,C_12),B_11) = k9_relat_1(A_8,B_11)
      | ~ r1_tarski(B_11,C_12)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_287,plain,(
    ! [B_11] :
      ( k9_relat_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),B_11) = k9_relat_1('#skF_5',B_11)
      | ~ r1_tarski(B_11,u1_struct_0('#skF_3'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_10])).

tff(c_506,plain,(
    ! [B_246] :
      ( k9_relat_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),B_246) = k9_relat_1('#skF_5',B_246)
      | ~ r1_tarski(B_246,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_287])).

tff(c_529,plain,(
    k9_relat_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') = k9_relat_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_506])).

tff(c_14,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k7_relat_1(B_16,A_15),B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_125,plain,(
    ! [A_155,B_156,C_157,D_158] :
      ( m1_subset_1(A_155,k1_zfmisc_1(k2_zfmisc_1(B_156,C_157)))
      | ~ r1_tarski(A_155,D_158)
      | ~ m1_subset_1(D_158,k1_zfmisc_1(k2_zfmisc_1(B_156,C_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_192,plain,(
    ! [B_175,A_176,B_177,C_178] :
      ( m1_subset_1(k7_relat_1(B_175,A_176),k1_zfmisc_1(k2_zfmisc_1(B_177,C_178)))
      | ~ m1_subset_1(B_175,k1_zfmisc_1(k2_zfmisc_1(B_177,C_178)))
      | ~ v1_relat_1(B_175) ) ),
    inference(resolution,[status(thm)],[c_14,c_125])).

tff(c_16,plain,(
    ! [C_19,A_17,B_18] :
      ( v1_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_217,plain,(
    ! [B_179,A_180,B_181,C_182] :
      ( v1_relat_1(k7_relat_1(B_179,A_180))
      | ~ m1_subset_1(B_179,k1_zfmisc_1(k2_zfmisc_1(B_181,C_182)))
      | ~ v1_relat_1(B_179) ) ),
    inference(resolution,[status(thm)],[c_192,c_16])).

tff(c_223,plain,(
    ! [A_180] :
      ( v1_relat_1(k7_relat_1('#skF_5',A_180))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_217])).

tff(c_228,plain,(
    ! [A_180] : v1_relat_1(k7_relat_1('#skF_5',A_180)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_223])).

tff(c_18,plain,(
    ! [C_22,B_21,A_20] :
      ( v5_relat_1(C_22,B_21)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_356,plain,(
    ! [B_200,A_201,C_202,B_203] :
      ( v5_relat_1(k7_relat_1(B_200,A_201),C_202)
      | ~ m1_subset_1(B_200,k1_zfmisc_1(k2_zfmisc_1(B_203,C_202)))
      | ~ v1_relat_1(B_200) ) ),
    inference(resolution,[status(thm)],[c_192,c_18])).

tff(c_364,plain,(
    ! [A_201] :
      ( v5_relat_1(k7_relat_1('#skF_5',A_201),u1_struct_0('#skF_2'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_356])).

tff(c_370,plain,(
    ! [A_201] : v5_relat_1(k7_relat_1('#skF_5',A_201),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_364])).

tff(c_12,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_14,A_13)),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_138,plain,(
    ! [C_159,A_160,B_161] :
      ( m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161)))
      | ~ r1_tarski(k2_relat_1(C_159),B_161)
      | ~ r1_tarski(k1_relat_1(C_159),A_160)
      | ~ v1_relat_1(C_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_22,plain,(
    ! [A_23,B_24,C_25,D_26] :
      ( k7_relset_1(A_23,B_24,C_25,D_26) = k9_relat_1(C_25,D_26)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_486,plain,(
    ! [A_230,B_231,C_232,D_233] :
      ( k7_relset_1(A_230,B_231,C_232,D_233) = k9_relat_1(C_232,D_233)
      | ~ r1_tarski(k2_relat_1(C_232),B_231)
      | ~ r1_tarski(k1_relat_1(C_232),A_230)
      | ~ v1_relat_1(C_232) ) ),
    inference(resolution,[status(thm)],[c_138,c_22])).

tff(c_641,plain,(
    ! [A_287,A_288,B_289,D_290] :
      ( k7_relset_1(A_287,A_288,B_289,D_290) = k9_relat_1(B_289,D_290)
      | ~ r1_tarski(k1_relat_1(B_289),A_287)
      | ~ v5_relat_1(B_289,A_288)
      | ~ v1_relat_1(B_289) ) ),
    inference(resolution,[status(thm)],[c_6,c_486])).

tff(c_2395,plain,(
    ! [A_693,A_694,B_695,D_696] :
      ( k7_relset_1(A_693,A_694,k7_relat_1(B_695,A_693),D_696) = k9_relat_1(k7_relat_1(B_695,A_693),D_696)
      | ~ v5_relat_1(k7_relat_1(B_695,A_693),A_694)
      | ~ v1_relat_1(k7_relat_1(B_695,A_693))
      | ~ v1_relat_1(B_695) ) ),
    inference(resolution,[status(thm)],[c_12,c_641])).

tff(c_2411,plain,(
    ! [A_201,D_696] :
      ( k7_relset_1(A_201,u1_struct_0('#skF_2'),k7_relat_1('#skF_5',A_201),D_696) = k9_relat_1(k7_relat_1('#skF_5',A_201),D_696)
      | ~ v1_relat_1(k7_relat_1('#skF_5',A_201))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_370,c_2395])).

tff(c_2434,plain,(
    ! [A_697,D_698] : k7_relset_1(A_697,u1_struct_0('#skF_2'),k7_relat_1('#skF_5',A_697),D_698) = k9_relat_1(k7_relat_1('#skF_5',A_697),D_698) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_228,c_2411])).

tff(c_2451,plain,(
    ! [D_698] : k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),D_698) = k9_relat_1(k7_relat_1('#skF_5',u1_struct_0('#skF_3')),D_698) ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_2434])).

tff(c_2456,plain,(
    ! [D_698] : k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),D_698) = k9_relat_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),D_698) ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_2451])).

tff(c_111,plain,(
    ! [A_150,B_151,C_152,D_153] :
      ( k7_relset_1(A_150,B_151,C_152,D_153) = k9_relat_1(C_152,D_153)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_114,plain,(
    ! [D_153] : k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_153) = k9_relat_1('#skF_5',D_153) ),
    inference(resolution,[status(thm)],[c_40,c_111])).

tff(c_32,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_115,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k9_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_32])).

tff(c_2470,plain,(
    k9_relat_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k9_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2456,c_115])).

tff(c_2473,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_529,c_2470])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:06:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.95/2.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.95/2.21  
% 5.95/2.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.95/2.21  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k7_relset_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.95/2.21  
% 5.95/2.21  %Foreground sorts:
% 5.95/2.21  
% 5.95/2.21  
% 5.95/2.21  %Background operators:
% 5.95/2.21  
% 5.95/2.21  
% 5.95/2.21  %Foreground operators:
% 5.95/2.21  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.95/2.21  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 5.95/2.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.95/2.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.95/2.21  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.95/2.21  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.95/2.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.95/2.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.95/2.21  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 5.95/2.21  tff('#skF_5', type, '#skF_5': $i).
% 5.95/2.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.95/2.21  tff('#skF_6', type, '#skF_6': $i).
% 5.95/2.21  tff('#skF_2', type, '#skF_2': $i).
% 5.95/2.22  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.95/2.22  tff('#skF_3', type, '#skF_3': $i).
% 5.95/2.22  tff('#skF_1', type, '#skF_1': $i).
% 5.95/2.22  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.95/2.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.95/2.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.95/2.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.95/2.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.95/2.22  tff('#skF_4', type, '#skF_4': $i).
% 5.95/2.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.95/2.22  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.95/2.22  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 5.95/2.22  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.95/2.22  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.95/2.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.95/2.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.95/2.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.95/2.22  
% 5.95/2.23  tff(f_165, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (r1_tarski(F, u1_struct_0(C)) => (k7_relset_1(u1_struct_0(D), u1_struct_0(B), E, F) = k7_relset_1(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, E), F)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_tmap_1)).
% 5.95/2.23  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.95/2.23  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.95/2.23  tff(f_89, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 5.95/2.23  tff(f_121, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 5.95/2.23  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 5.95/2.23  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 5.95/2.23  tff(f_83, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => (r1_tarski(A, D) => m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_relset_1)).
% 5.95/2.23  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.95/2.23  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.95/2.23  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 5.95/2.23  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 5.95/2.23  tff(f_77, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 5.95/2.23  tff(f_69, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.95/2.23  tff(c_34, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.95/2.23  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.95/2.23  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.95/2.23  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.95/2.23  tff(c_75, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_40, c_2])).
% 5.95/2.23  tff(c_78, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_75])).
% 5.95/2.23  tff(c_64, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.95/2.23  tff(c_62, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.95/2.23  tff(c_60, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.95/2.23  tff(c_46, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.95/2.23  tff(c_38, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.95/2.23  tff(c_50, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.95/2.23  tff(c_58, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.95/2.23  tff(c_56, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.95/2.23  tff(c_54, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.95/2.23  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.95/2.23  tff(c_42, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.95/2.23  tff(c_174, plain, (![A_170, B_171, C_172, D_173]: (k2_partfun1(A_170, B_171, C_172, D_173)=k7_relat_1(C_172, D_173) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))) | ~v1_funct_1(C_172))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.95/2.23  tff(c_178, plain, (![D_173]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_173)=k7_relat_1('#skF_5', D_173) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_174])).
% 5.95/2.23  tff(c_182, plain, (![D_173]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_173)=k7_relat_1('#skF_5', D_173))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_178])).
% 5.95/2.23  tff(c_230, plain, (![D_188, C_185, B_186, E_187, A_184]: (k3_tmap_1(A_184, B_186, C_185, D_188, E_187)=k2_partfun1(u1_struct_0(C_185), u1_struct_0(B_186), E_187, u1_struct_0(D_188)) | ~m1_pre_topc(D_188, C_185) | ~m1_subset_1(E_187, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_185), u1_struct_0(B_186)))) | ~v1_funct_2(E_187, u1_struct_0(C_185), u1_struct_0(B_186)) | ~v1_funct_1(E_187) | ~m1_pre_topc(D_188, A_184) | ~m1_pre_topc(C_185, A_184) | ~l1_pre_topc(B_186) | ~v2_pre_topc(B_186) | v2_struct_0(B_186) | ~l1_pre_topc(A_184) | ~v2_pre_topc(A_184) | v2_struct_0(A_184))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.95/2.23  tff(c_238, plain, (![A_184, D_188]: (k3_tmap_1(A_184, '#skF_2', '#skF_4', D_188, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_188)) | ~m1_pre_topc(D_188, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_188, A_184) | ~m1_pre_topc('#skF_4', A_184) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_184) | ~v2_pre_topc(A_184) | v2_struct_0(A_184))), inference(resolution, [status(thm)], [c_40, c_230])).
% 5.95/2.23  tff(c_243, plain, (![D_188, A_184]: (k7_relat_1('#skF_5', u1_struct_0(D_188))=k3_tmap_1(A_184, '#skF_2', '#skF_4', D_188, '#skF_5') | ~m1_pre_topc(D_188, '#skF_4') | ~m1_pre_topc(D_188, A_184) | ~m1_pre_topc('#skF_4', A_184) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_184) | ~v2_pre_topc(A_184) | v2_struct_0(A_184))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_44, c_42, c_182, c_238])).
% 5.95/2.23  tff(c_258, plain, (![D_194, A_195]: (k7_relat_1('#skF_5', u1_struct_0(D_194))=k3_tmap_1(A_195, '#skF_2', '#skF_4', D_194, '#skF_5') | ~m1_pre_topc(D_194, '#skF_4') | ~m1_pre_topc(D_194, A_195) | ~m1_pre_topc('#skF_4', A_195) | ~l1_pre_topc(A_195) | ~v2_pre_topc(A_195) | v2_struct_0(A_195))), inference(negUnitSimplification, [status(thm)], [c_58, c_243])).
% 5.95/2.23  tff(c_260, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_258])).
% 5.95/2.23  tff(c_267, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_46, c_38, c_260])).
% 5.95/2.23  tff(c_268, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_64, c_267])).
% 5.95/2.23  tff(c_10, plain, (![A_8, C_12, B_11]: (k9_relat_1(k7_relat_1(A_8, C_12), B_11)=k9_relat_1(A_8, B_11) | ~r1_tarski(B_11, C_12) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.95/2.23  tff(c_287, plain, (![B_11]: (k9_relat_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), B_11)=k9_relat_1('#skF_5', B_11) | ~r1_tarski(B_11, u1_struct_0('#skF_3')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_268, c_10])).
% 5.95/2.23  tff(c_506, plain, (![B_246]: (k9_relat_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), B_246)=k9_relat_1('#skF_5', B_246) | ~r1_tarski(B_246, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_287])).
% 5.95/2.23  tff(c_529, plain, (k9_relat_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')=k9_relat_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_34, c_506])).
% 5.95/2.23  tff(c_14, plain, (![B_16, A_15]: (r1_tarski(k7_relat_1(B_16, A_15), B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.95/2.23  tff(c_125, plain, (![A_155, B_156, C_157, D_158]: (m1_subset_1(A_155, k1_zfmisc_1(k2_zfmisc_1(B_156, C_157))) | ~r1_tarski(A_155, D_158) | ~m1_subset_1(D_158, k1_zfmisc_1(k2_zfmisc_1(B_156, C_157))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.95/2.23  tff(c_192, plain, (![B_175, A_176, B_177, C_178]: (m1_subset_1(k7_relat_1(B_175, A_176), k1_zfmisc_1(k2_zfmisc_1(B_177, C_178))) | ~m1_subset_1(B_175, k1_zfmisc_1(k2_zfmisc_1(B_177, C_178))) | ~v1_relat_1(B_175))), inference(resolution, [status(thm)], [c_14, c_125])).
% 5.95/2.23  tff(c_16, plain, (![C_19, A_17, B_18]: (v1_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.95/2.23  tff(c_217, plain, (![B_179, A_180, B_181, C_182]: (v1_relat_1(k7_relat_1(B_179, A_180)) | ~m1_subset_1(B_179, k1_zfmisc_1(k2_zfmisc_1(B_181, C_182))) | ~v1_relat_1(B_179))), inference(resolution, [status(thm)], [c_192, c_16])).
% 5.95/2.23  tff(c_223, plain, (![A_180]: (v1_relat_1(k7_relat_1('#skF_5', A_180)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_217])).
% 5.95/2.23  tff(c_228, plain, (![A_180]: (v1_relat_1(k7_relat_1('#skF_5', A_180)))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_223])).
% 5.95/2.23  tff(c_18, plain, (![C_22, B_21, A_20]: (v5_relat_1(C_22, B_21) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.95/2.23  tff(c_356, plain, (![B_200, A_201, C_202, B_203]: (v5_relat_1(k7_relat_1(B_200, A_201), C_202) | ~m1_subset_1(B_200, k1_zfmisc_1(k2_zfmisc_1(B_203, C_202))) | ~v1_relat_1(B_200))), inference(resolution, [status(thm)], [c_192, c_18])).
% 5.95/2.23  tff(c_364, plain, (![A_201]: (v5_relat_1(k7_relat_1('#skF_5', A_201), u1_struct_0('#skF_2')) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_356])).
% 5.95/2.23  tff(c_370, plain, (![A_201]: (v5_relat_1(k7_relat_1('#skF_5', A_201), u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_364])).
% 5.95/2.23  tff(c_12, plain, (![B_14, A_13]: (r1_tarski(k1_relat_1(k7_relat_1(B_14, A_13)), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.95/2.23  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.95/2.23  tff(c_138, plain, (![C_159, A_160, B_161]: (m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))) | ~r1_tarski(k2_relat_1(C_159), B_161) | ~r1_tarski(k1_relat_1(C_159), A_160) | ~v1_relat_1(C_159))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.95/2.23  tff(c_22, plain, (![A_23, B_24, C_25, D_26]: (k7_relset_1(A_23, B_24, C_25, D_26)=k9_relat_1(C_25, D_26) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.95/2.23  tff(c_486, plain, (![A_230, B_231, C_232, D_233]: (k7_relset_1(A_230, B_231, C_232, D_233)=k9_relat_1(C_232, D_233) | ~r1_tarski(k2_relat_1(C_232), B_231) | ~r1_tarski(k1_relat_1(C_232), A_230) | ~v1_relat_1(C_232))), inference(resolution, [status(thm)], [c_138, c_22])).
% 5.95/2.23  tff(c_641, plain, (![A_287, A_288, B_289, D_290]: (k7_relset_1(A_287, A_288, B_289, D_290)=k9_relat_1(B_289, D_290) | ~r1_tarski(k1_relat_1(B_289), A_287) | ~v5_relat_1(B_289, A_288) | ~v1_relat_1(B_289))), inference(resolution, [status(thm)], [c_6, c_486])).
% 5.95/2.23  tff(c_2395, plain, (![A_693, A_694, B_695, D_696]: (k7_relset_1(A_693, A_694, k7_relat_1(B_695, A_693), D_696)=k9_relat_1(k7_relat_1(B_695, A_693), D_696) | ~v5_relat_1(k7_relat_1(B_695, A_693), A_694) | ~v1_relat_1(k7_relat_1(B_695, A_693)) | ~v1_relat_1(B_695))), inference(resolution, [status(thm)], [c_12, c_641])).
% 5.95/2.23  tff(c_2411, plain, (![A_201, D_696]: (k7_relset_1(A_201, u1_struct_0('#skF_2'), k7_relat_1('#skF_5', A_201), D_696)=k9_relat_1(k7_relat_1('#skF_5', A_201), D_696) | ~v1_relat_1(k7_relat_1('#skF_5', A_201)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_370, c_2395])).
% 5.95/2.23  tff(c_2434, plain, (![A_697, D_698]: (k7_relset_1(A_697, u1_struct_0('#skF_2'), k7_relat_1('#skF_5', A_697), D_698)=k9_relat_1(k7_relat_1('#skF_5', A_697), D_698))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_228, c_2411])).
% 5.95/2.23  tff(c_2451, plain, (![D_698]: (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), D_698)=k9_relat_1(k7_relat_1('#skF_5', u1_struct_0('#skF_3')), D_698))), inference(superposition, [status(thm), theory('equality')], [c_268, c_2434])).
% 5.95/2.23  tff(c_2456, plain, (![D_698]: (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), D_698)=k9_relat_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), D_698))), inference(demodulation, [status(thm), theory('equality')], [c_268, c_2451])).
% 5.95/2.23  tff(c_111, plain, (![A_150, B_151, C_152, D_153]: (k7_relset_1(A_150, B_151, C_152, D_153)=k9_relat_1(C_152, D_153) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.95/2.23  tff(c_114, plain, (![D_153]: (k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_153)=k9_relat_1('#skF_5', D_153))), inference(resolution, [status(thm)], [c_40, c_111])).
% 5.95/2.23  tff(c_32, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_165])).
% 5.95/2.23  tff(c_115, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k9_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_32])).
% 5.95/2.23  tff(c_2470, plain, (k9_relat_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k9_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2456, c_115])).
% 5.95/2.23  tff(c_2473, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_529, c_2470])).
% 5.95/2.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.95/2.23  
% 5.95/2.23  Inference rules
% 5.95/2.23  ----------------------
% 5.95/2.23  #Ref     : 0
% 5.95/2.23  #Sup     : 565
% 5.95/2.23  #Fact    : 0
% 5.95/2.23  #Define  : 0
% 5.95/2.23  #Split   : 11
% 5.95/2.23  #Chain   : 0
% 5.95/2.23  #Close   : 0
% 5.95/2.23  
% 5.95/2.23  Ordering : KBO
% 5.95/2.23  
% 5.95/2.23  Simplification rules
% 5.95/2.23  ----------------------
% 5.95/2.23  #Subsume      : 92
% 5.95/2.23  #Demod        : 353
% 5.95/2.23  #Tautology    : 66
% 5.95/2.23  #SimpNegUnit  : 33
% 5.95/2.23  #BackRed      : 5
% 5.95/2.23  
% 5.95/2.23  #Partial instantiations: 0
% 5.95/2.23  #Strategies tried      : 1
% 5.95/2.23  
% 5.95/2.23  Timing (in seconds)
% 5.95/2.23  ----------------------
% 5.95/2.24  Preprocessing        : 0.38
% 5.95/2.24  Parsing              : 0.20
% 5.95/2.24  CNF conversion       : 0.04
% 5.95/2.24  Main loop            : 1.03
% 5.95/2.24  Inferencing          : 0.38
% 5.95/2.24  Reduction            : 0.33
% 5.95/2.24  Demodulation         : 0.24
% 5.95/2.24  BG Simplification    : 0.04
% 5.95/2.24  Subsumption          : 0.21
% 5.95/2.24  Abstraction          : 0.05
% 5.95/2.24  MUC search           : 0.00
% 5.95/2.24  Cooper               : 0.00
% 5.95/2.24  Total                : 1.45
% 5.95/2.24  Index Insertion      : 0.00
% 5.95/2.24  Index Deletion       : 0.00
% 5.95/2.24  Index Matching       : 0.00
% 5.95/2.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
