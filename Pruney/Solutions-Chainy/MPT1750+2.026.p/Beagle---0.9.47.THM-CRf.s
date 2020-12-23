%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:55 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :  121 (1027 expanded)
%              Number of leaves         :   45 ( 376 expanded)
%              Depth                    :   19
%              Number of atoms          :  278 (4283 expanded)
%              Number of equality atoms :   27 ( 304 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(r1_funct_2,type,(
    r1_funct_2: ( $i * $i * $i * $i * $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_183,negated_conjecture,(
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
                   => ( g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                     => r1_funct_2(u1_struct_0(B),u1_struct_0(A),u1_struct_0(C),u1_struct_0(A),D,k2_tmap_1(B,A,D,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_tmap_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_150,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_146,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_112,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(B)
        & ~ v1_xboole_0(D)
        & v1_funct_1(E)
        & v1_funct_2(E,A,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,C,D)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => r1_funct_2(A,B,C,D,E,E) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r1_funct_2)).

tff(f_76,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_139,axiom,(
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

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(c_62,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_22,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_56,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_52,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_73,plain,(
    ! [B_70,A_71] :
      ( l1_pre_topc(B_70)
      | ~ m1_pre_topc(B_70,A_71)
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_79,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_73])).

tff(c_83,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_79])).

tff(c_40,plain,(
    ! [A_52] :
      ( m1_pre_topc(A_52,A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_44,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_227,plain,(
    ! [A_111,B_112] :
      ( m1_pre_topc(A_111,g1_pre_topc(u1_struct_0(B_112),u1_pre_topc(B_112)))
      | ~ m1_pre_topc(A_111,B_112)
      | ~ l1_pre_topc(B_112)
      | ~ l1_pre_topc(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_240,plain,(
    ! [A_111] :
      ( m1_pre_topc(A_111,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_111,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_227])).

tff(c_255,plain,(
    ! [A_114] :
      ( m1_pre_topc(A_114,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_114,'#skF_2')
      | ~ l1_pre_topc(A_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_240])).

tff(c_28,plain,(
    ! [B_24,A_22] :
      ( m1_pre_topc(B_24,A_22)
      | ~ m1_pre_topc(B_24,g1_pre_topc(u1_struct_0(A_22),u1_pre_topc(A_22)))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_261,plain,(
    ! [A_114] :
      ( m1_pre_topc(A_114,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_pre_topc(A_114,'#skF_2')
      | ~ l1_pre_topc(A_114) ) ),
    inference(resolution,[status(thm)],[c_255,c_28])).

tff(c_270,plain,(
    ! [A_115] :
      ( m1_pre_topc(A_115,'#skF_3')
      | ~ m1_pre_topc(A_115,'#skF_2')
      | ~ l1_pre_topc(A_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_261])).

tff(c_277,plain,
    ( m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_270])).

tff(c_284,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_277])).

tff(c_186,plain,(
    ! [B_102,A_103] :
      ( m1_subset_1(u1_struct_0(B_102),k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ m1_pre_topc(B_102,A_103)
      | ~ l1_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_190,plain,(
    ! [B_102,A_103] :
      ( r1_tarski(u1_struct_0(B_102),u1_struct_0(A_103))
      | ~ m1_pre_topc(B_102,A_103)
      | ~ l1_pre_topc(A_103) ) ),
    inference(resolution,[status(thm)],[c_186,c_8])).

tff(c_204,plain,(
    ! [B_106,A_107] :
      ( r1_tarski(u1_struct_0(B_106),u1_struct_0(A_107))
      | ~ m1_pre_topc(B_106,A_107)
      | ~ l1_pre_topc(A_107) ) ),
    inference(resolution,[status(thm)],[c_186,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_300,plain,(
    ! [B_116,A_117] :
      ( u1_struct_0(B_116) = u1_struct_0(A_117)
      | ~ r1_tarski(u1_struct_0(A_117),u1_struct_0(B_116))
      | ~ m1_pre_topc(B_116,A_117)
      | ~ l1_pre_topc(A_117) ) ),
    inference(resolution,[status(thm)],[c_204,c_2])).

tff(c_311,plain,(
    ! [B_118,A_119] :
      ( u1_struct_0(B_118) = u1_struct_0(A_119)
      | ~ m1_pre_topc(A_119,B_118)
      | ~ l1_pre_topc(B_118)
      | ~ m1_pre_topc(B_118,A_119)
      | ~ l1_pre_topc(A_119) ) ),
    inference(resolution,[status(thm)],[c_190,c_300])).

tff(c_315,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_284,c_311])).

tff(c_332,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_83,c_315])).

tff(c_48,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_350,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_48])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_349,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_46])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_421,plain,(
    ! [F_124,E_125,A_126,D_129,C_127,B_128] :
      ( r1_funct_2(A_126,B_128,C_127,D_129,E_125,E_125)
      | ~ m1_subset_1(F_124,k1_zfmisc_1(k2_zfmisc_1(C_127,D_129)))
      | ~ v1_funct_2(F_124,C_127,D_129)
      | ~ v1_funct_1(F_124)
      | ~ m1_subset_1(E_125,k1_zfmisc_1(k2_zfmisc_1(A_126,B_128)))
      | ~ v1_funct_2(E_125,A_126,B_128)
      | ~ v1_funct_1(E_125)
      | v1_xboole_0(D_129)
      | v1_xboole_0(B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_875,plain,(
    ! [C_158,B_159,D_160,A_157,A_162,E_161] :
      ( r1_funct_2(A_157,B_159,C_158,D_160,E_161,E_161)
      | ~ v1_funct_2(A_162,C_158,D_160)
      | ~ v1_funct_1(A_162)
      | ~ m1_subset_1(E_161,k1_zfmisc_1(k2_zfmisc_1(A_157,B_159)))
      | ~ v1_funct_2(E_161,A_157,B_159)
      | ~ v1_funct_1(E_161)
      | v1_xboole_0(D_160)
      | v1_xboole_0(B_159)
      | ~ r1_tarski(A_162,k2_zfmisc_1(C_158,D_160)) ) ),
    inference(resolution,[status(thm)],[c_10,c_421])).

tff(c_877,plain,(
    ! [C_158,D_160,A_162] :
      ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),C_158,D_160,'#skF_4','#skF_4')
      | ~ v1_funct_2(A_162,C_158,D_160)
      | ~ v1_funct_1(A_162)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(D_160)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_162,k2_zfmisc_1(C_158,D_160)) ) ),
    inference(resolution,[status(thm)],[c_349,c_875])).

tff(c_883,plain,(
    ! [C_158,D_160,A_162] :
      ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),C_158,D_160,'#skF_4','#skF_4')
      | ~ v1_funct_2(A_162,C_158,D_160)
      | ~ v1_funct_1(A_162)
      | v1_xboole_0(D_160)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_162,k2_zfmisc_1(C_158,D_160)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_350,c_877])).

tff(c_909,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_883])).

tff(c_26,plain,(
    ! [A_21] :
      ( ~ v1_xboole_0(u1_struct_0(A_21))
      | ~ l1_struct_0(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_917,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_909,c_26])).

tff(c_920,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_917])).

tff(c_923,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_920])).

tff(c_927,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_923])).

tff(c_929,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_883])).

tff(c_64,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_20,plain,(
    ! [A_13,B_14,C_15,D_16] :
      ( k2_partfun1(A_13,B_14,C_15,D_16) = k7_relat_1(C_15,D_16)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_447,plain,(
    ! [D_16] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',D_16) = k7_relat_1('#skF_4',D_16)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_349,c_20])).

tff(c_465,plain,(
    ! [D_16] : k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',D_16) = k7_relat_1('#skF_4',D_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_447])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_58,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_528,plain,(
    ! [A_132,B_133,C_134,D_135] :
      ( k2_partfun1(u1_struct_0(A_132),u1_struct_0(B_133),C_134,u1_struct_0(D_135)) = k2_tmap_1(A_132,B_133,C_134,D_135)
      | ~ m1_pre_topc(D_135,A_132)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_132),u1_struct_0(B_133))))
      | ~ v1_funct_2(C_134,u1_struct_0(A_132),u1_struct_0(B_133))
      | ~ v1_funct_1(C_134)
      | ~ l1_pre_topc(B_133)
      | ~ v2_pre_topc(B_133)
      | v2_struct_0(B_133)
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132)
      | v2_struct_0(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_532,plain,(
    ! [B_133,C_134,D_135] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0(B_133),C_134,u1_struct_0(D_135)) = k2_tmap_1('#skF_2',B_133,C_134,D_135)
      | ~ m1_pre_topc(D_135,'#skF_2')
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_133))))
      | ~ v1_funct_2(C_134,u1_struct_0('#skF_2'),u1_struct_0(B_133))
      | ~ v1_funct_1(C_134)
      | ~ l1_pre_topc(B_133)
      | ~ v2_pre_topc(B_133)
      | v2_struct_0(B_133)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_528])).

tff(c_543,plain,(
    ! [B_133,C_134,D_135] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_133),C_134,u1_struct_0(D_135)) = k2_tmap_1('#skF_2',B_133,C_134,D_135)
      | ~ m1_pre_topc(D_135,'#skF_2')
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_133))))
      | ~ v1_funct_2(C_134,u1_struct_0('#skF_3'),u1_struct_0(B_133))
      | ~ v1_funct_1(C_134)
      | ~ l1_pre_topc(B_133)
      | ~ v2_pre_topc(B_133)
      | v2_struct_0(B_133)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_332,c_332,c_532])).

tff(c_825,plain,(
    ! [B_153,C_154,D_155] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_153),C_154,u1_struct_0(D_155)) = k2_tmap_1('#skF_2',B_153,C_154,D_155)
      | ~ m1_pre_topc(D_155,'#skF_2')
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_153))))
      | ~ v1_funct_2(C_154,u1_struct_0('#skF_3'),u1_struct_0(B_153))
      | ~ v1_funct_1(C_154)
      | ~ l1_pre_topc(B_153)
      | ~ v2_pre_topc(B_153)
      | v2_struct_0(B_153) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_543])).

tff(c_827,plain,(
    ! [D_155] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_155)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_155)
      | ~ m1_pre_topc(D_155,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_349,c_825])).

tff(c_835,plain,(
    ! [D_155] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_155)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_155)
      | ~ m1_pre_topc(D_155,'#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_50,c_350,c_465,c_827])).

tff(c_841,plain,(
    ! [D_156] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_156)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_156)
      | ~ m1_pre_topc(D_156,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_835])).

tff(c_103,plain,(
    ! [C_76,A_77,B_78] :
      ( v1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_111,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_103])).

tff(c_125,plain,(
    ! [C_84,A_85,B_86] :
      ( v4_relat_1(C_84,A_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_133,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_46,c_125])).

tff(c_173,plain,(
    ! [B_100,A_101] :
      ( k7_relat_1(B_100,A_101) = B_100
      | ~ v4_relat_1(B_100,A_101)
      | ~ v1_relat_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_179,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_133,c_173])).

tff(c_185,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_179])).

tff(c_345,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_185])).

tff(c_847,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_841,c_345])).

tff(c_859,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_847])).

tff(c_42,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_344,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_42])).

tff(c_865,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_859,c_344])).

tff(c_99,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_46,c_8])).

tff(c_348,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_99])).

tff(c_930,plain,(
    ! [C_167,D_168,A_169] :
      ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),C_167,D_168,'#skF_4','#skF_4')
      | ~ v1_funct_2(A_169,C_167,D_168)
      | ~ v1_funct_1(A_169)
      | v1_xboole_0(D_168)
      | ~ r1_tarski(A_169,k2_zfmisc_1(C_167,D_168)) ) ),
    inference(splitRight,[status(thm)],[c_883])).

tff(c_932,plain,
    ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_348,c_930])).

tff(c_938,plain,
    ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_350,c_932])).

tff(c_940,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_929,c_865,c_938])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:24:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.52  
% 3.32/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.52  %$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.32/1.52  
% 3.32/1.52  %Foreground sorts:
% 3.32/1.52  
% 3.32/1.52  
% 3.32/1.52  %Background operators:
% 3.32/1.52  
% 3.32/1.52  
% 3.32/1.52  %Foreground operators:
% 3.32/1.52  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.32/1.52  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.32/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.32/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.52  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.32/1.52  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.32/1.52  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.32/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.32/1.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.32/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.32/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.32/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.32/1.52  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.32/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.32/1.52  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.32/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.32/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.32/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.32/1.52  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 3.32/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.52  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.32/1.52  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.32/1.52  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.32/1.52  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.32/1.52  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.32/1.52  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.32/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.32/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.32/1.52  
% 3.52/1.55  tff(f_183, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_tmap_1)).
% 3.52/1.55  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.52/1.55  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.52/1.55  tff(f_150, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 3.52/1.55  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 3.52/1.55  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 3.52/1.55  tff(f_146, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.52/1.55  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.52/1.55  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.52/1.55  tff(f_112, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => r1_funct_2(A, B, C, D, E, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r1_funct_2)).
% 3.52/1.55  tff(f_76, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.52/1.55  tff(f_57, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.52/1.55  tff(f_139, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.52/1.55  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.52/1.55  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.52/1.55  tff(f_41, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.52/1.55  tff(c_62, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.52/1.55  tff(c_22, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.52/1.55  tff(c_66, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.52/1.55  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.52/1.55  tff(c_56, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.52/1.55  tff(c_52, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.52/1.55  tff(c_73, plain, (![B_70, A_71]: (l1_pre_topc(B_70) | ~m1_pre_topc(B_70, A_71) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.52/1.55  tff(c_79, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_52, c_73])).
% 3.52/1.55  tff(c_83, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_79])).
% 3.52/1.55  tff(c_40, plain, (![A_52]: (m1_pre_topc(A_52, A_52) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.52/1.55  tff(c_44, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.52/1.55  tff(c_227, plain, (![A_111, B_112]: (m1_pre_topc(A_111, g1_pre_topc(u1_struct_0(B_112), u1_pre_topc(B_112))) | ~m1_pre_topc(A_111, B_112) | ~l1_pre_topc(B_112) | ~l1_pre_topc(A_111))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.52/1.55  tff(c_240, plain, (![A_111]: (m1_pre_topc(A_111, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_111, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_111))), inference(superposition, [status(thm), theory('equality')], [c_44, c_227])).
% 3.52/1.55  tff(c_255, plain, (![A_114]: (m1_pre_topc(A_114, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_114, '#skF_2') | ~l1_pre_topc(A_114))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_240])).
% 3.52/1.55  tff(c_28, plain, (![B_24, A_22]: (m1_pre_topc(B_24, A_22) | ~m1_pre_topc(B_24, g1_pre_topc(u1_struct_0(A_22), u1_pre_topc(A_22))) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.52/1.55  tff(c_261, plain, (![A_114]: (m1_pre_topc(A_114, '#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc(A_114, '#skF_2') | ~l1_pre_topc(A_114))), inference(resolution, [status(thm)], [c_255, c_28])).
% 3.52/1.55  tff(c_270, plain, (![A_115]: (m1_pre_topc(A_115, '#skF_3') | ~m1_pre_topc(A_115, '#skF_2') | ~l1_pre_topc(A_115))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_261])).
% 3.52/1.55  tff(c_277, plain, (m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_270])).
% 3.52/1.55  tff(c_284, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_277])).
% 3.52/1.55  tff(c_186, plain, (![B_102, A_103]: (m1_subset_1(u1_struct_0(B_102), k1_zfmisc_1(u1_struct_0(A_103))) | ~m1_pre_topc(B_102, A_103) | ~l1_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.52/1.55  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.52/1.55  tff(c_190, plain, (![B_102, A_103]: (r1_tarski(u1_struct_0(B_102), u1_struct_0(A_103)) | ~m1_pre_topc(B_102, A_103) | ~l1_pre_topc(A_103))), inference(resolution, [status(thm)], [c_186, c_8])).
% 3.52/1.55  tff(c_204, plain, (![B_106, A_107]: (r1_tarski(u1_struct_0(B_106), u1_struct_0(A_107)) | ~m1_pre_topc(B_106, A_107) | ~l1_pre_topc(A_107))), inference(resolution, [status(thm)], [c_186, c_8])).
% 3.52/1.55  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.52/1.55  tff(c_300, plain, (![B_116, A_117]: (u1_struct_0(B_116)=u1_struct_0(A_117) | ~r1_tarski(u1_struct_0(A_117), u1_struct_0(B_116)) | ~m1_pre_topc(B_116, A_117) | ~l1_pre_topc(A_117))), inference(resolution, [status(thm)], [c_204, c_2])).
% 3.52/1.55  tff(c_311, plain, (![B_118, A_119]: (u1_struct_0(B_118)=u1_struct_0(A_119) | ~m1_pre_topc(A_119, B_118) | ~l1_pre_topc(B_118) | ~m1_pre_topc(B_118, A_119) | ~l1_pre_topc(A_119))), inference(resolution, [status(thm)], [c_190, c_300])).
% 3.52/1.55  tff(c_315, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_284, c_311])).
% 3.52/1.55  tff(c_332, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_83, c_315])).
% 3.52/1.55  tff(c_48, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.52/1.55  tff(c_350, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_332, c_48])).
% 3.52/1.55  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.52/1.55  tff(c_349, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_332, c_46])).
% 3.52/1.55  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.52/1.55  tff(c_421, plain, (![F_124, E_125, A_126, D_129, C_127, B_128]: (r1_funct_2(A_126, B_128, C_127, D_129, E_125, E_125) | ~m1_subset_1(F_124, k1_zfmisc_1(k2_zfmisc_1(C_127, D_129))) | ~v1_funct_2(F_124, C_127, D_129) | ~v1_funct_1(F_124) | ~m1_subset_1(E_125, k1_zfmisc_1(k2_zfmisc_1(A_126, B_128))) | ~v1_funct_2(E_125, A_126, B_128) | ~v1_funct_1(E_125) | v1_xboole_0(D_129) | v1_xboole_0(B_128))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.52/1.55  tff(c_875, plain, (![C_158, B_159, D_160, A_157, A_162, E_161]: (r1_funct_2(A_157, B_159, C_158, D_160, E_161, E_161) | ~v1_funct_2(A_162, C_158, D_160) | ~v1_funct_1(A_162) | ~m1_subset_1(E_161, k1_zfmisc_1(k2_zfmisc_1(A_157, B_159))) | ~v1_funct_2(E_161, A_157, B_159) | ~v1_funct_1(E_161) | v1_xboole_0(D_160) | v1_xboole_0(B_159) | ~r1_tarski(A_162, k2_zfmisc_1(C_158, D_160)))), inference(resolution, [status(thm)], [c_10, c_421])).
% 3.52/1.55  tff(c_877, plain, (![C_158, D_160, A_162]: (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), C_158, D_160, '#skF_4', '#skF_4') | ~v1_funct_2(A_162, C_158, D_160) | ~v1_funct_1(A_162) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(D_160) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski(A_162, k2_zfmisc_1(C_158, D_160)))), inference(resolution, [status(thm)], [c_349, c_875])).
% 3.52/1.55  tff(c_883, plain, (![C_158, D_160, A_162]: (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), C_158, D_160, '#skF_4', '#skF_4') | ~v1_funct_2(A_162, C_158, D_160) | ~v1_funct_1(A_162) | v1_xboole_0(D_160) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski(A_162, k2_zfmisc_1(C_158, D_160)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_350, c_877])).
% 3.52/1.55  tff(c_909, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_883])).
% 3.52/1.55  tff(c_26, plain, (![A_21]: (~v1_xboole_0(u1_struct_0(A_21)) | ~l1_struct_0(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.52/1.55  tff(c_917, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_909, c_26])).
% 3.52/1.55  tff(c_920, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_66, c_917])).
% 3.52/1.55  tff(c_923, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_920])).
% 3.52/1.55  tff(c_927, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_923])).
% 3.52/1.55  tff(c_929, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_883])).
% 3.52/1.55  tff(c_64, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.52/1.55  tff(c_20, plain, (![A_13, B_14, C_15, D_16]: (k2_partfun1(A_13, B_14, C_15, D_16)=k7_relat_1(C_15, D_16) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_1(C_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.52/1.55  tff(c_447, plain, (![D_16]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', D_16)=k7_relat_1('#skF_4', D_16) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_349, c_20])).
% 3.52/1.55  tff(c_465, plain, (![D_16]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', D_16)=k7_relat_1('#skF_4', D_16))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_447])).
% 3.52/1.55  tff(c_60, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.52/1.55  tff(c_58, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.52/1.55  tff(c_528, plain, (![A_132, B_133, C_134, D_135]: (k2_partfun1(u1_struct_0(A_132), u1_struct_0(B_133), C_134, u1_struct_0(D_135))=k2_tmap_1(A_132, B_133, C_134, D_135) | ~m1_pre_topc(D_135, A_132) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_132), u1_struct_0(B_133)))) | ~v1_funct_2(C_134, u1_struct_0(A_132), u1_struct_0(B_133)) | ~v1_funct_1(C_134) | ~l1_pre_topc(B_133) | ~v2_pre_topc(B_133) | v2_struct_0(B_133) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132) | v2_struct_0(A_132))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.52/1.55  tff(c_532, plain, (![B_133, C_134, D_135]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0(B_133), C_134, u1_struct_0(D_135))=k2_tmap_1('#skF_2', B_133, C_134, D_135) | ~m1_pre_topc(D_135, '#skF_2') | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_133)))) | ~v1_funct_2(C_134, u1_struct_0('#skF_2'), u1_struct_0(B_133)) | ~v1_funct_1(C_134) | ~l1_pre_topc(B_133) | ~v2_pre_topc(B_133) | v2_struct_0(B_133) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_332, c_528])).
% 3.52/1.55  tff(c_543, plain, (![B_133, C_134, D_135]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_133), C_134, u1_struct_0(D_135))=k2_tmap_1('#skF_2', B_133, C_134, D_135) | ~m1_pre_topc(D_135, '#skF_2') | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_133)))) | ~v1_funct_2(C_134, u1_struct_0('#skF_3'), u1_struct_0(B_133)) | ~v1_funct_1(C_134) | ~l1_pre_topc(B_133) | ~v2_pre_topc(B_133) | v2_struct_0(B_133) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_332, c_332, c_532])).
% 3.52/1.55  tff(c_825, plain, (![B_153, C_154, D_155]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_153), C_154, u1_struct_0(D_155))=k2_tmap_1('#skF_2', B_153, C_154, D_155) | ~m1_pre_topc(D_155, '#skF_2') | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_153)))) | ~v1_funct_2(C_154, u1_struct_0('#skF_3'), u1_struct_0(B_153)) | ~v1_funct_1(C_154) | ~l1_pre_topc(B_153) | ~v2_pre_topc(B_153) | v2_struct_0(B_153))), inference(negUnitSimplification, [status(thm)], [c_60, c_543])).
% 3.52/1.55  tff(c_827, plain, (![D_155]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_155))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_155) | ~m1_pre_topc(D_155, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_349, c_825])).
% 3.52/1.55  tff(c_835, plain, (![D_155]: (k7_relat_1('#skF_4', u1_struct_0(D_155))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_155) | ~m1_pre_topc(D_155, '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_50, c_350, c_465, c_827])).
% 3.52/1.55  tff(c_841, plain, (![D_156]: (k7_relat_1('#skF_4', u1_struct_0(D_156))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_156) | ~m1_pre_topc(D_156, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_66, c_835])).
% 3.52/1.55  tff(c_103, plain, (![C_76, A_77, B_78]: (v1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.52/1.55  tff(c_111, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_103])).
% 3.52/1.55  tff(c_125, plain, (![C_84, A_85, B_86]: (v4_relat_1(C_84, A_85) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.52/1.55  tff(c_133, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_46, c_125])).
% 3.52/1.55  tff(c_173, plain, (![B_100, A_101]: (k7_relat_1(B_100, A_101)=B_100 | ~v4_relat_1(B_100, A_101) | ~v1_relat_1(B_100))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.52/1.55  tff(c_179, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_133, c_173])).
% 3.52/1.55  tff(c_185, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_111, c_179])).
% 3.52/1.55  tff(c_345, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_332, c_185])).
% 3.52/1.55  tff(c_847, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_841, c_345])).
% 3.52/1.55  tff(c_859, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_847])).
% 3.52/1.55  tff(c_42, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_183])).
% 3.52/1.55  tff(c_344, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_332, c_42])).
% 3.52/1.55  tff(c_865, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_859, c_344])).
% 3.52/1.55  tff(c_99, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_46, c_8])).
% 3.52/1.55  tff(c_348, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_332, c_99])).
% 3.52/1.55  tff(c_930, plain, (![C_167, D_168, A_169]: (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), C_167, D_168, '#skF_4', '#skF_4') | ~v1_funct_2(A_169, C_167, D_168) | ~v1_funct_1(A_169) | v1_xboole_0(D_168) | ~r1_tarski(A_169, k2_zfmisc_1(C_167, D_168)))), inference(splitRight, [status(thm)], [c_883])).
% 3.52/1.55  tff(c_932, plain, (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_348, c_930])).
% 3.52/1.55  tff(c_938, plain, (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_350, c_932])).
% 3.52/1.55  tff(c_940, plain, $false, inference(negUnitSimplification, [status(thm)], [c_929, c_865, c_938])).
% 3.52/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.55  
% 3.52/1.55  Inference rules
% 3.52/1.55  ----------------------
% 3.52/1.55  #Ref     : 0
% 3.52/1.55  #Sup     : 167
% 3.52/1.55  #Fact    : 0
% 3.52/1.55  #Define  : 0
% 3.52/1.55  #Split   : 6
% 3.52/1.55  #Chain   : 0
% 3.52/1.55  #Close   : 0
% 3.52/1.55  
% 3.52/1.55  Ordering : KBO
% 3.52/1.55  
% 3.52/1.55  Simplification rules
% 3.52/1.55  ----------------------
% 3.52/1.55  #Subsume      : 26
% 3.52/1.55  #Demod        : 212
% 3.52/1.55  #Tautology    : 75
% 3.52/1.55  #SimpNegUnit  : 8
% 3.52/1.55  #BackRed      : 9
% 3.52/1.55  
% 3.52/1.55  #Partial instantiations: 0
% 3.52/1.55  #Strategies tried      : 1
% 3.52/1.55  
% 3.52/1.55  Timing (in seconds)
% 3.52/1.55  ----------------------
% 3.52/1.55  Preprocessing        : 0.37
% 3.52/1.55  Parsing              : 0.20
% 3.52/1.55  CNF conversion       : 0.03
% 3.52/1.55  Main loop            : 0.40
% 3.52/1.55  Inferencing          : 0.14
% 3.52/1.55  Reduction            : 0.14
% 3.52/1.55  Demodulation         : 0.09
% 3.52/1.55  BG Simplification    : 0.02
% 3.52/1.55  Subsumption          : 0.08
% 3.52/1.55  Abstraction          : 0.02
% 3.52/1.55  MUC search           : 0.00
% 3.52/1.55  Cooper               : 0.00
% 3.52/1.55  Total                : 0.82
% 3.52/1.55  Index Insertion      : 0.00
% 3.52/1.55  Index Deletion       : 0.00
% 3.52/1.55  Index Matching       : 0.00
% 3.52/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
