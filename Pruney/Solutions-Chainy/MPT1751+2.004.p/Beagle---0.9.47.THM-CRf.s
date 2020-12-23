%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:58 EST 2020

% Result     : Theorem 8.29s
% Output     : CNFRefutation 8.29s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 191 expanded)
%              Number of leaves         :   42 (  91 expanded)
%              Depth                    :   12
%              Number of atoms          :  192 ( 901 expanded)
%              Number of equality atoms :   33 (  92 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_147,negated_conjecture,(
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
                  & m1_pre_topc(C,B) )
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,u1_struct_0(B),u1_struct_0(A))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(B)))
                       => ( r1_tarski(E,u1_struct_0(C))
                         => k7_relset_1(u1_struct_0(B),u1_struct_0(A),D,E) = k7_relset_1(u1_struct_0(C),u1_struct_0(A),k2_tmap_1(B,A,D,C),E) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_tmap_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_111,axiom,(
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

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k7_relat_1(B,A)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_42,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_32,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_16,plain,(
    ! [C_19,A_17,B_18] :
      ( v1_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_62,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_16])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_38,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_280,plain,(
    ! [A_135,B_136,C_137,D_138] :
      ( k2_partfun1(A_135,B_136,C_137,D_138) = k7_relat_1(C_137,D_138)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136)))
      | ~ v1_funct_1(C_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_282,plain,(
    ! [D_138] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_138) = k7_relat_1('#skF_4',D_138)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_280])).

tff(c_285,plain,(
    ! [D_138] : k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_138) = k7_relat_1('#skF_4',D_138) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_282])).

tff(c_531,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_536,plain,(
    ! [D_184] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_184)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_184)
      | ~ m1_pre_topc(D_184,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_36,c_531])).

tff(c_540,plain,(
    ! [D_184] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_184)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_184)
      | ~ m1_pre_topc(D_184,'#skF_2')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_54,c_52,c_40,c_38,c_285,c_536])).

tff(c_542,plain,(
    ! [D_185] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_185)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_185)
      | ~ m1_pre_topc(D_185,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_56,c_540])).

tff(c_10,plain,(
    ! [A_8,C_12,B_11] :
      ( k9_relat_1(k7_relat_1(A_8,C_12),B_11) = k9_relat_1(A_8,B_11)
      | ~ r1_tarski(B_11,C_12)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_574,plain,(
    ! [D_185,B_11] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_185),B_11) = k9_relat_1('#skF_4',B_11)
      | ~ r1_tarski(B_11,u1_struct_0(D_185))
      | ~ v1_relat_1('#skF_4')
      | ~ m1_pre_topc(D_185,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_542,c_10])).

tff(c_1412,plain,(
    ! [D_262,B_263] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_262),B_263) = k9_relat_1('#skF_4',B_263)
      | ~ r1_tarski(B_263,u1_struct_0(D_262))
      | ~ m1_pre_topc(D_262,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_574])).

tff(c_1470,plain,
    ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') = k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_1412])).

tff(c_1499,plain,(
    k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') = k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1470])).

tff(c_541,plain,(
    ! [D_184] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_184)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_184)
      | ~ m1_pre_topc(D_184,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_56,c_540])).

tff(c_81,plain,(
    ! [C_88,B_89,A_90] :
      ( v5_relat_1(C_88,B_89)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_90,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_85,plain,(
    v5_relat_1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_36,c_81])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k7_relat_1(A_6,B_7))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_16,A_15)),k2_relat_1(B_16))
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_86,plain,(
    ! [B_91,A_92] :
      ( r1_tarski(k2_relat_1(B_91),A_92)
      | ~ v5_relat_1(B_91,A_92)
      | ~ v1_relat_1(B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_143,plain,(
    ! [A_106,A_107,B_108] :
      ( r1_tarski(A_106,A_107)
      | ~ r1_tarski(A_106,k2_relat_1(B_108))
      | ~ v5_relat_1(B_108,A_107)
      | ~ v1_relat_1(B_108) ) ),
    inference(resolution,[status(thm)],[c_86,c_2])).

tff(c_155,plain,(
    ! [B_109,A_110,A_111] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_109,A_110)),A_111)
      | ~ v5_relat_1(B_109,A_111)
      | ~ v1_relat_1(B_109) ) ),
    inference(resolution,[status(thm)],[c_14,c_143])).

tff(c_4,plain,(
    ! [B_5,A_4] :
      ( v5_relat_1(B_5,A_4)
      | ~ r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_173,plain,(
    ! [B_109,A_110,A_111] :
      ( v5_relat_1(k7_relat_1(B_109,A_110),A_111)
      | ~ v1_relat_1(k7_relat_1(B_109,A_110))
      | ~ v5_relat_1(B_109,A_111)
      | ~ v1_relat_1(B_109) ) ),
    inference(resolution,[status(thm)],[c_155,c_4])).

tff(c_12,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_14,A_13)),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_419,plain,(
    ! [C_165,A_166,B_167] :
      ( m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167)))
      | ~ r1_tarski(k2_relat_1(C_165),B_167)
      | ~ r1_tarski(k1_relat_1(C_165),A_166)
      | ~ v1_relat_1(C_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_22,plain,(
    ! [A_23,B_24,C_25,D_26] :
      ( k7_relset_1(A_23,B_24,C_25,D_26) = k9_relat_1(C_25,D_26)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_761,plain,(
    ! [A_196,B_197,C_198,D_199] :
      ( k7_relset_1(A_196,B_197,C_198,D_199) = k9_relat_1(C_198,D_199)
      | ~ r1_tarski(k2_relat_1(C_198),B_197)
      | ~ r1_tarski(k1_relat_1(C_198),A_196)
      | ~ v1_relat_1(C_198) ) ),
    inference(resolution,[status(thm)],[c_419,c_22])).

tff(c_1521,plain,(
    ! [A_265,A_266,B_267,D_268] :
      ( k7_relset_1(A_265,A_266,B_267,D_268) = k9_relat_1(B_267,D_268)
      | ~ r1_tarski(k1_relat_1(B_267),A_265)
      | ~ v5_relat_1(B_267,A_266)
      | ~ v1_relat_1(B_267) ) ),
    inference(resolution,[status(thm)],[c_6,c_761])).

tff(c_5159,plain,(
    ! [A_590,A_591,B_592,D_593] :
      ( k7_relset_1(A_590,A_591,k7_relat_1(B_592,A_590),D_593) = k9_relat_1(k7_relat_1(B_592,A_590),D_593)
      | ~ v5_relat_1(k7_relat_1(B_592,A_590),A_591)
      | ~ v1_relat_1(k7_relat_1(B_592,A_590))
      | ~ v1_relat_1(B_592) ) ),
    inference(resolution,[status(thm)],[c_12,c_1521])).

tff(c_5193,plain,(
    ! [A_594,A_595,B_596,D_597] :
      ( k7_relset_1(A_594,A_595,k7_relat_1(B_596,A_594),D_597) = k9_relat_1(k7_relat_1(B_596,A_594),D_597)
      | ~ v1_relat_1(k7_relat_1(B_596,A_594))
      | ~ v5_relat_1(B_596,A_595)
      | ~ v1_relat_1(B_596) ) ),
    inference(resolution,[status(thm)],[c_173,c_5159])).

tff(c_5201,plain,(
    ! [B_598,A_599,A_600,D_601] :
      ( k7_relset_1(B_598,A_599,k7_relat_1(A_600,B_598),D_601) = k9_relat_1(k7_relat_1(A_600,B_598),D_601)
      | ~ v5_relat_1(A_600,A_599)
      | ~ v1_relat_1(A_600) ) ),
    inference(resolution,[status(thm)],[c_8,c_5193])).

tff(c_5241,plain,(
    ! [D_184,A_599,D_601] :
      ( k7_relset_1(u1_struct_0(D_184),A_599,k2_tmap_1('#skF_2','#skF_1','#skF_4',D_184),D_601) = k9_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_184)),D_601)
      | ~ v5_relat_1('#skF_4',A_599)
      | ~ v1_relat_1('#skF_4')
      | ~ m1_pre_topc(D_184,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_5201])).

tff(c_7188,plain,(
    ! [D_755,A_756,D_757] :
      ( k7_relset_1(u1_struct_0(D_755),A_756,k2_tmap_1('#skF_2','#skF_1','#skF_4',D_755),D_757) = k9_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_755)),D_757)
      | ~ v5_relat_1('#skF_4',A_756)
      | ~ m1_pre_topc(D_755,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_5241])).

tff(c_251,plain,(
    ! [A_127,B_128,C_129,D_130] :
      ( k7_relset_1(A_127,B_128,C_129,D_130) = k9_relat_1(C_129,D_130)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_254,plain,(
    ! [D_130] : k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_130) = k9_relat_1('#skF_4',D_130) ),
    inference(resolution,[status(thm)],[c_36,c_251])).

tff(c_30,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_255,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_30])).

tff(c_7202,plain,
    ( k9_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ v5_relat_1('#skF_4',u1_struct_0('#skF_1'))
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_7188,c_255])).

tff(c_7220,plain,(
    k9_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_85,c_7202])).

tff(c_7228,plain,
    ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_7220])).

tff(c_7234,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1499,c_7228])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:28:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.29/3.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.29/3.01  
% 8.29/3.01  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.29/3.01  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.29/3.01  
% 8.29/3.01  %Foreground sorts:
% 8.29/3.01  
% 8.29/3.01  
% 8.29/3.01  %Background operators:
% 8.29/3.01  
% 8.29/3.01  
% 8.29/3.01  %Foreground operators:
% 8.29/3.01  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.29/3.01  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.29/3.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.29/3.01  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.29/3.01  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.29/3.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.29/3.01  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.29/3.01  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 8.29/3.01  tff('#skF_5', type, '#skF_5': $i).
% 8.29/3.01  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.29/3.01  tff('#skF_2', type, '#skF_2': $i).
% 8.29/3.01  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.29/3.01  tff('#skF_3', type, '#skF_3': $i).
% 8.29/3.01  tff('#skF_1', type, '#skF_1': $i).
% 8.29/3.01  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.29/3.01  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.29/3.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.29/3.01  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.29/3.01  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.29/3.01  tff('#skF_4', type, '#skF_4': $i).
% 8.29/3.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.29/3.01  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 8.29/3.01  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 8.29/3.01  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.29/3.01  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.29/3.01  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 8.29/3.01  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.29/3.01  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.29/3.01  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.29/3.01  
% 8.29/3.03  tff(f_147, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (r1_tarski(E, u1_struct_0(C)) => (k7_relset_1(u1_struct_0(B), u1_struct_0(A), D, E) = k7_relset_1(u1_struct_0(C), u1_struct_0(A), k2_tmap_1(B, A, D, C), E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_tmap_1)).
% 8.29/3.03  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.29/3.03  tff(f_84, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 8.29/3.03  tff(f_111, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 8.29/3.03  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 8.29/3.03  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.29/3.03  tff(f_41, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 8.29/3.03  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k7_relat_1(B, A)), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_relat_1)).
% 8.29/3.03  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 8.29/3.03  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 8.29/3.03  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 8.29/3.03  tff(f_78, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 8.29/3.03  tff(f_70, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 8.29/3.03  tff(c_42, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.29/3.03  tff(c_32, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.29/3.03  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.29/3.03  tff(c_16, plain, (![C_19, A_17, B_18]: (v1_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.29/3.03  tff(c_62, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_16])).
% 8.29/3.03  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.29/3.03  tff(c_56, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.29/3.03  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.29/3.03  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.29/3.03  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.29/3.03  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.29/3.03  tff(c_40, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.29/3.03  tff(c_38, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.29/3.03  tff(c_280, plain, (![A_135, B_136, C_137, D_138]: (k2_partfun1(A_135, B_136, C_137, D_138)=k7_relat_1(C_137, D_138) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))) | ~v1_funct_1(C_137))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.29/3.03  tff(c_282, plain, (![D_138]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_138)=k7_relat_1('#skF_4', D_138) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_36, c_280])).
% 8.29/3.03  tff(c_285, plain, (![D_138]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_138)=k7_relat_1('#skF_4', D_138))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_282])).
% 8.29/3.03  tff(c_531, plain, (![A_181, B_182, C_183, D_184]: (k2_partfun1(u1_struct_0(A_181), u1_struct_0(B_182), C_183, u1_struct_0(D_184))=k2_tmap_1(A_181, B_182, C_183, D_184) | ~m1_pre_topc(D_184, A_181) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_181), u1_struct_0(B_182)))) | ~v1_funct_2(C_183, u1_struct_0(A_181), u1_struct_0(B_182)) | ~v1_funct_1(C_183) | ~l1_pre_topc(B_182) | ~v2_pre_topc(B_182) | v2_struct_0(B_182) | ~l1_pre_topc(A_181) | ~v2_pre_topc(A_181) | v2_struct_0(A_181))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.29/3.03  tff(c_536, plain, (![D_184]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_184))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_184) | ~m1_pre_topc(D_184, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_531])).
% 8.29/3.03  tff(c_540, plain, (![D_184]: (k7_relat_1('#skF_4', u1_struct_0(D_184))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_184) | ~m1_pre_topc(D_184, '#skF_2') | v2_struct_0('#skF_1') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_54, c_52, c_40, c_38, c_285, c_536])).
% 8.29/3.03  tff(c_542, plain, (![D_185]: (k7_relat_1('#skF_4', u1_struct_0(D_185))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_185) | ~m1_pre_topc(D_185, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_56, c_540])).
% 8.29/3.03  tff(c_10, plain, (![A_8, C_12, B_11]: (k9_relat_1(k7_relat_1(A_8, C_12), B_11)=k9_relat_1(A_8, B_11) | ~r1_tarski(B_11, C_12) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.29/3.03  tff(c_574, plain, (![D_185, B_11]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_185), B_11)=k9_relat_1('#skF_4', B_11) | ~r1_tarski(B_11, u1_struct_0(D_185)) | ~v1_relat_1('#skF_4') | ~m1_pre_topc(D_185, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_542, c_10])).
% 8.29/3.03  tff(c_1412, plain, (![D_262, B_263]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_262), B_263)=k9_relat_1('#skF_4', B_263) | ~r1_tarski(B_263, u1_struct_0(D_262)) | ~m1_pre_topc(D_262, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_574])).
% 8.29/3.03  tff(c_1470, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_1412])).
% 8.29/3.03  tff(c_1499, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1470])).
% 8.29/3.03  tff(c_541, plain, (![D_184]: (k7_relat_1('#skF_4', u1_struct_0(D_184))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_184) | ~m1_pre_topc(D_184, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_56, c_540])).
% 8.29/3.03  tff(c_81, plain, (![C_88, B_89, A_90]: (v5_relat_1(C_88, B_89) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_90, B_89))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.29/3.03  tff(c_85, plain, (v5_relat_1('#skF_4', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_81])).
% 8.29/3.03  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k7_relat_1(A_6, B_7)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.29/3.03  tff(c_14, plain, (![B_16, A_15]: (r1_tarski(k2_relat_1(k7_relat_1(B_16, A_15)), k2_relat_1(B_16)) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.29/3.03  tff(c_86, plain, (![B_91, A_92]: (r1_tarski(k2_relat_1(B_91), A_92) | ~v5_relat_1(B_91, A_92) | ~v1_relat_1(B_91))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.29/3.03  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.29/3.03  tff(c_143, plain, (![A_106, A_107, B_108]: (r1_tarski(A_106, A_107) | ~r1_tarski(A_106, k2_relat_1(B_108)) | ~v5_relat_1(B_108, A_107) | ~v1_relat_1(B_108))), inference(resolution, [status(thm)], [c_86, c_2])).
% 8.29/3.03  tff(c_155, plain, (![B_109, A_110, A_111]: (r1_tarski(k2_relat_1(k7_relat_1(B_109, A_110)), A_111) | ~v5_relat_1(B_109, A_111) | ~v1_relat_1(B_109))), inference(resolution, [status(thm)], [c_14, c_143])).
% 8.29/3.03  tff(c_4, plain, (![B_5, A_4]: (v5_relat_1(B_5, A_4) | ~r1_tarski(k2_relat_1(B_5), A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.29/3.03  tff(c_173, plain, (![B_109, A_110, A_111]: (v5_relat_1(k7_relat_1(B_109, A_110), A_111) | ~v1_relat_1(k7_relat_1(B_109, A_110)) | ~v5_relat_1(B_109, A_111) | ~v1_relat_1(B_109))), inference(resolution, [status(thm)], [c_155, c_4])).
% 8.29/3.03  tff(c_12, plain, (![B_14, A_13]: (r1_tarski(k1_relat_1(k7_relat_1(B_14, A_13)), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.29/3.03  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.29/3.03  tff(c_419, plain, (![C_165, A_166, B_167]: (m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))) | ~r1_tarski(k2_relat_1(C_165), B_167) | ~r1_tarski(k1_relat_1(C_165), A_166) | ~v1_relat_1(C_165))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.29/3.03  tff(c_22, plain, (![A_23, B_24, C_25, D_26]: (k7_relset_1(A_23, B_24, C_25, D_26)=k9_relat_1(C_25, D_26) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.29/3.03  tff(c_761, plain, (![A_196, B_197, C_198, D_199]: (k7_relset_1(A_196, B_197, C_198, D_199)=k9_relat_1(C_198, D_199) | ~r1_tarski(k2_relat_1(C_198), B_197) | ~r1_tarski(k1_relat_1(C_198), A_196) | ~v1_relat_1(C_198))), inference(resolution, [status(thm)], [c_419, c_22])).
% 8.29/3.03  tff(c_1521, plain, (![A_265, A_266, B_267, D_268]: (k7_relset_1(A_265, A_266, B_267, D_268)=k9_relat_1(B_267, D_268) | ~r1_tarski(k1_relat_1(B_267), A_265) | ~v5_relat_1(B_267, A_266) | ~v1_relat_1(B_267))), inference(resolution, [status(thm)], [c_6, c_761])).
% 8.29/3.03  tff(c_5159, plain, (![A_590, A_591, B_592, D_593]: (k7_relset_1(A_590, A_591, k7_relat_1(B_592, A_590), D_593)=k9_relat_1(k7_relat_1(B_592, A_590), D_593) | ~v5_relat_1(k7_relat_1(B_592, A_590), A_591) | ~v1_relat_1(k7_relat_1(B_592, A_590)) | ~v1_relat_1(B_592))), inference(resolution, [status(thm)], [c_12, c_1521])).
% 8.29/3.03  tff(c_5193, plain, (![A_594, A_595, B_596, D_597]: (k7_relset_1(A_594, A_595, k7_relat_1(B_596, A_594), D_597)=k9_relat_1(k7_relat_1(B_596, A_594), D_597) | ~v1_relat_1(k7_relat_1(B_596, A_594)) | ~v5_relat_1(B_596, A_595) | ~v1_relat_1(B_596))), inference(resolution, [status(thm)], [c_173, c_5159])).
% 8.29/3.03  tff(c_5201, plain, (![B_598, A_599, A_600, D_601]: (k7_relset_1(B_598, A_599, k7_relat_1(A_600, B_598), D_601)=k9_relat_1(k7_relat_1(A_600, B_598), D_601) | ~v5_relat_1(A_600, A_599) | ~v1_relat_1(A_600))), inference(resolution, [status(thm)], [c_8, c_5193])).
% 8.29/3.03  tff(c_5241, plain, (![D_184, A_599, D_601]: (k7_relset_1(u1_struct_0(D_184), A_599, k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_184), D_601)=k9_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_184)), D_601) | ~v5_relat_1('#skF_4', A_599) | ~v1_relat_1('#skF_4') | ~m1_pre_topc(D_184, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_541, c_5201])).
% 8.29/3.03  tff(c_7188, plain, (![D_755, A_756, D_757]: (k7_relset_1(u1_struct_0(D_755), A_756, k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_755), D_757)=k9_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_755)), D_757) | ~v5_relat_1('#skF_4', A_756) | ~m1_pre_topc(D_755, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_5241])).
% 8.29/3.03  tff(c_251, plain, (![A_127, B_128, C_129, D_130]: (k7_relset_1(A_127, B_128, C_129, D_130)=k9_relat_1(C_129, D_130) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.29/3.03  tff(c_254, plain, (![D_130]: (k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_130)=k9_relat_1('#skF_4', D_130))), inference(resolution, [status(thm)], [c_36, c_251])).
% 8.29/3.03  tff(c_30, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.29/3.03  tff(c_255, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_254, c_30])).
% 8.29/3.03  tff(c_7202, plain, (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~v5_relat_1('#skF_4', u1_struct_0('#skF_1')) | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_7188, c_255])).
% 8.29/3.03  tff(c_7220, plain, (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_85, c_7202])).
% 8.29/3.03  tff(c_7228, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_541, c_7220])).
% 8.29/3.03  tff(c_7234, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_1499, c_7228])).
% 8.29/3.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.29/3.03  
% 8.29/3.03  Inference rules
% 8.29/3.03  ----------------------
% 8.29/3.03  #Ref     : 0
% 8.29/3.03  #Sup     : 1745
% 8.29/3.03  #Fact    : 0
% 8.29/3.03  #Define  : 0
% 8.29/3.03  #Split   : 10
% 8.29/3.03  #Chain   : 0
% 8.29/3.03  #Close   : 0
% 8.29/3.03  
% 8.29/3.03  Ordering : KBO
% 8.29/3.03  
% 8.29/3.03  Simplification rules
% 8.29/3.03  ----------------------
% 8.29/3.03  #Subsume      : 290
% 8.29/3.03  #Demod        : 193
% 8.29/3.03  #Tautology    : 80
% 8.29/3.03  #SimpNegUnit  : 7
% 8.29/3.03  #BackRed      : 1
% 8.29/3.03  
% 8.29/3.03  #Partial instantiations: 0
% 8.29/3.03  #Strategies tried      : 1
% 8.29/3.03  
% 8.29/3.03  Timing (in seconds)
% 8.29/3.03  ----------------------
% 8.29/3.03  Preprocessing        : 0.33
% 8.29/3.03  Parsing              : 0.18
% 8.29/3.03  CNF conversion       : 0.03
% 8.29/3.03  Main loop            : 1.92
% 8.29/3.03  Inferencing          : 0.53
% 8.29/3.03  Reduction            : 0.44
% 8.29/3.03  Demodulation         : 0.28
% 8.29/3.03  BG Simplification    : 0.06
% 8.29/3.03  Subsumption          : 0.73
% 8.29/3.03  Abstraction          : 0.10
% 8.29/3.03  MUC search           : 0.00
% 8.29/3.03  Cooper               : 0.00
% 8.29/3.03  Total                : 2.29
% 8.29/3.03  Index Insertion      : 0.00
% 8.29/3.03  Index Deletion       : 0.00
% 8.29/3.03  Index Matching       : 0.00
% 8.29/3.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
