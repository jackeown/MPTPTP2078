%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:54 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :  121 (1025 expanded)
%              Number of leaves         :   45 ( 375 expanded)
%              Depth                    :   21
%              Number of atoms          :  272 (4257 expanded)
%              Number of equality atoms :   28 ( 306 expanded)
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

tff(f_185,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_tmap_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_152,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_148,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_114,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(B)
        & ~ v1_xboole_0(D)
        & v1_funct_1(E)
        & v1_funct_2(E,A,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,C,D)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( r1_funct_2(A,B,C,D,E,F)
      <=> E = F ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

tff(f_76,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_141,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(c_64,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_22,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_58,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_54,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_80,plain,(
    ! [B_72,A_73] :
      ( l1_pre_topc(B_72)
      | ~ m1_pre_topc(B_72,A_73)
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_86,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_80])).

tff(c_90,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_86])).

tff(c_42,plain,(
    ! [A_52] :
      ( m1_pre_topc(A_52,A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_46,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_229,plain,(
    ! [A_111,B_112] :
      ( m1_pre_topc(A_111,g1_pre_topc(u1_struct_0(B_112),u1_pre_topc(B_112)))
      | ~ m1_pre_topc(A_111,B_112)
      | ~ l1_pre_topc(B_112)
      | ~ l1_pre_topc(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_242,plain,(
    ! [A_111] :
      ( m1_pre_topc(A_111,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_111,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_229])).

tff(c_257,plain,(
    ! [A_114] :
      ( m1_pre_topc(A_114,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_114,'#skF_2')
      | ~ l1_pre_topc(A_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_242])).

tff(c_28,plain,(
    ! [B_24,A_22] :
      ( m1_pre_topc(B_24,A_22)
      | ~ m1_pre_topc(B_24,g1_pre_topc(u1_struct_0(A_22),u1_pre_topc(A_22)))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_263,plain,(
    ! [A_114] :
      ( m1_pre_topc(A_114,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_pre_topc(A_114,'#skF_2')
      | ~ l1_pre_topc(A_114) ) ),
    inference(resolution,[status(thm)],[c_257,c_28])).

tff(c_272,plain,(
    ! [A_115] :
      ( m1_pre_topc(A_115,'#skF_3')
      | ~ m1_pre_topc(A_115,'#skF_2')
      | ~ l1_pre_topc(A_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_263])).

tff(c_279,plain,
    ( m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_272])).

tff(c_286,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_279])).

tff(c_188,plain,(
    ! [B_102,A_103] :
      ( m1_subset_1(u1_struct_0(B_102),k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ m1_pre_topc(B_102,A_103)
      | ~ l1_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_192,plain,(
    ! [B_102,A_103] :
      ( r1_tarski(u1_struct_0(B_102),u1_struct_0(A_103))
      | ~ m1_pre_topc(B_102,A_103)
      | ~ l1_pre_topc(A_103) ) ),
    inference(resolution,[status(thm)],[c_188,c_8])).

tff(c_206,plain,(
    ! [B_106,A_107] :
      ( r1_tarski(u1_struct_0(B_106),u1_struct_0(A_107))
      | ~ m1_pre_topc(B_106,A_107)
      | ~ l1_pre_topc(A_107) ) ),
    inference(resolution,[status(thm)],[c_188,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_302,plain,(
    ! [B_116,A_117] :
      ( u1_struct_0(B_116) = u1_struct_0(A_117)
      | ~ r1_tarski(u1_struct_0(A_117),u1_struct_0(B_116))
      | ~ m1_pre_topc(B_116,A_117)
      | ~ l1_pre_topc(A_117) ) ),
    inference(resolution,[status(thm)],[c_206,c_2])).

tff(c_313,plain,(
    ! [B_118,A_119] :
      ( u1_struct_0(B_118) = u1_struct_0(A_119)
      | ~ m1_pre_topc(A_119,B_118)
      | ~ l1_pre_topc(B_118)
      | ~ m1_pre_topc(B_118,A_119)
      | ~ l1_pre_topc(A_119) ) ),
    inference(resolution,[status(thm)],[c_192,c_302])).

tff(c_317,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_286,c_313])).

tff(c_334,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_90,c_317])).

tff(c_50,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_352,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_50])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_351,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_48])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_423,plain,(
    ! [C_126,F_124,B_127,A_125,D_128] :
      ( r1_funct_2(A_125,B_127,C_126,D_128,F_124,F_124)
      | ~ m1_subset_1(F_124,k1_zfmisc_1(k2_zfmisc_1(C_126,D_128)))
      | ~ v1_funct_2(F_124,C_126,D_128)
      | ~ m1_subset_1(F_124,k1_zfmisc_1(k2_zfmisc_1(A_125,B_127)))
      | ~ v1_funct_2(F_124,A_125,B_127)
      | ~ v1_funct_1(F_124)
      | v1_xboole_0(D_128)
      | v1_xboole_0(B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_850,plain,(
    ! [D_161,C_163,A_164,B_165,A_162] :
      ( r1_funct_2(A_164,B_165,C_163,D_161,A_162,A_162)
      | ~ v1_funct_2(A_162,C_163,D_161)
      | ~ m1_subset_1(A_162,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165)))
      | ~ v1_funct_2(A_162,A_164,B_165)
      | ~ v1_funct_1(A_162)
      | v1_xboole_0(D_161)
      | v1_xboole_0(B_165)
      | ~ r1_tarski(A_162,k2_zfmisc_1(C_163,D_161)) ) ),
    inference(resolution,[status(thm)],[c_10,c_423])).

tff(c_852,plain,(
    ! [C_163,D_161] :
      ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),C_163,D_161,'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',C_163,D_161)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(D_161)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(C_163,D_161)) ) ),
    inference(resolution,[status(thm)],[c_351,c_850])).

tff(c_858,plain,(
    ! [C_163,D_161] :
      ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),C_163,D_161,'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',C_163,D_161)
      | v1_xboole_0(D_161)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(C_163,D_161)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_352,c_852])).

tff(c_884,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_858])).

tff(c_26,plain,(
    ! [A_21] :
      ( ~ v1_xboole_0(u1_struct_0(A_21))
      | ~ l1_struct_0(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_892,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_884,c_26])).

tff(c_895,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_892])).

tff(c_898,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_895])).

tff(c_902,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_898])).

tff(c_904,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_858])).

tff(c_104,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_48,c_8])).

tff(c_350,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_104])).

tff(c_905,plain,(
    ! [C_170,D_171] :
      ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),C_170,D_171,'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',C_170,D_171)
      | v1_xboole_0(D_171)
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(C_170,D_171)) ) ),
    inference(splitRight,[status(thm)],[c_858])).

tff(c_66,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_20,plain,(
    ! [A_13,B_14,C_15,D_16] :
      ( k2_partfun1(A_13,B_14,C_15,D_16) = k7_relat_1(C_15,D_16)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_449,plain,(
    ! [D_16] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',D_16) = k7_relat_1('#skF_4',D_16)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_351,c_20])).

tff(c_467,plain,(
    ! [D_16] : k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',D_16) = k7_relat_1('#skF_4',D_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_449])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_60,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_640,plain,(
    ! [A_142,B_143,C_144,D_145] :
      ( k2_partfun1(u1_struct_0(A_142),u1_struct_0(B_143),C_144,u1_struct_0(D_145)) = k2_tmap_1(A_142,B_143,C_144,D_145)
      | ~ m1_pre_topc(D_145,A_142)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_142),u1_struct_0(B_143))))
      | ~ v1_funct_2(C_144,u1_struct_0(A_142),u1_struct_0(B_143))
      | ~ v1_funct_1(C_144)
      | ~ l1_pre_topc(B_143)
      | ~ v2_pre_topc(B_143)
      | v2_struct_0(B_143)
      | ~ l1_pre_topc(A_142)
      | ~ v2_pre_topc(A_142)
      | v2_struct_0(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_644,plain,(
    ! [B_143,C_144,D_145] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0(B_143),C_144,u1_struct_0(D_145)) = k2_tmap_1('#skF_2',B_143,C_144,D_145)
      | ~ m1_pre_topc(D_145,'#skF_2')
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_143))))
      | ~ v1_funct_2(C_144,u1_struct_0('#skF_2'),u1_struct_0(B_143))
      | ~ v1_funct_1(C_144)
      | ~ l1_pre_topc(B_143)
      | ~ v2_pre_topc(B_143)
      | v2_struct_0(B_143)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_640])).

tff(c_655,plain,(
    ! [B_143,C_144,D_145] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_143),C_144,u1_struct_0(D_145)) = k2_tmap_1('#skF_2',B_143,C_144,D_145)
      | ~ m1_pre_topc(D_145,'#skF_2')
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_143))))
      | ~ v1_funct_2(C_144,u1_struct_0('#skF_3'),u1_struct_0(B_143))
      | ~ v1_funct_1(C_144)
      | ~ l1_pre_topc(B_143)
      | ~ v2_pre_topc(B_143)
      | v2_struct_0(B_143)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_334,c_334,c_644])).

tff(c_800,plain,(
    ! [B_157,C_158,D_159] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_157),C_158,u1_struct_0(D_159)) = k2_tmap_1('#skF_2',B_157,C_158,D_159)
      | ~ m1_pre_topc(D_159,'#skF_2')
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_157))))
      | ~ v1_funct_2(C_158,u1_struct_0('#skF_3'),u1_struct_0(B_157))
      | ~ v1_funct_1(C_158)
      | ~ l1_pre_topc(B_157)
      | ~ v2_pre_topc(B_157)
      | v2_struct_0(B_157) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_655])).

tff(c_802,plain,(
    ! [D_159] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_159)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_159)
      | ~ m1_pre_topc(D_159,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_351,c_800])).

tff(c_810,plain,(
    ! [D_159] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_159)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_159)
      | ~ m1_pre_topc(D_159,'#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_52,c_352,c_467,c_802])).

tff(c_816,plain,(
    ! [D_160] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_160)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_160)
      | ~ m1_pre_topc(D_160,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_810])).

tff(c_14,plain,(
    ! [C_9,A_7,B_8] :
      ( v1_relat_1(C_9)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_103,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_14])).

tff(c_127,plain,(
    ! [C_84,A_85,B_86] :
      ( v4_relat_1(C_84,A_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_135,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_127])).

tff(c_175,plain,(
    ! [B_100,A_101] :
      ( k7_relat_1(B_100,A_101) = B_100
      | ~ v4_relat_1(B_100,A_101)
      | ~ v1_relat_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_181,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_135,c_175])).

tff(c_187,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_181])).

tff(c_347,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_187])).

tff(c_822,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_816,c_347])).

tff(c_834,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_822])).

tff(c_44,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_346,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_44])).

tff(c_840,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_834,c_346])).

tff(c_908,plain,
    ( ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_905,c_840])).

tff(c_913,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_352,c_908])).

tff(c_915,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_904,c_913])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:04:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.33/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.49  
% 3.33/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.50  %$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.33/1.50  
% 3.33/1.50  %Foreground sorts:
% 3.33/1.50  
% 3.33/1.50  
% 3.33/1.50  %Background operators:
% 3.33/1.50  
% 3.33/1.50  
% 3.33/1.50  %Foreground operators:
% 3.33/1.50  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.33/1.50  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.33/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.33/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.33/1.50  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.33/1.50  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.33/1.50  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.33/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.33/1.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.33/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.33/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.33/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.33/1.50  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.33/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.33/1.50  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.33/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.33/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.33/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.33/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.33/1.50  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 3.33/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.33/1.50  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.33/1.50  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.33/1.50  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.33/1.50  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.33/1.50  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.33/1.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.33/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.33/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.33/1.50  
% 3.33/1.52  tff(f_185, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_tmap_1)).
% 3.33/1.52  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.33/1.52  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.33/1.52  tff(f_152, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 3.33/1.52  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 3.33/1.52  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 3.33/1.52  tff(f_148, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.33/1.52  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.33/1.52  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.33/1.52  tff(f_114, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 3.33/1.52  tff(f_76, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.33/1.52  tff(f_57, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.33/1.52  tff(f_141, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.33/1.52  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.33/1.52  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.33/1.52  tff(f_41, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.33/1.52  tff(c_64, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.33/1.52  tff(c_22, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.33/1.52  tff(c_68, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.33/1.52  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.33/1.52  tff(c_58, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.33/1.52  tff(c_54, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.33/1.52  tff(c_80, plain, (![B_72, A_73]: (l1_pre_topc(B_72) | ~m1_pre_topc(B_72, A_73) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.33/1.52  tff(c_86, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_80])).
% 3.33/1.52  tff(c_90, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_86])).
% 3.33/1.52  tff(c_42, plain, (![A_52]: (m1_pre_topc(A_52, A_52) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.33/1.52  tff(c_46, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.33/1.52  tff(c_229, plain, (![A_111, B_112]: (m1_pre_topc(A_111, g1_pre_topc(u1_struct_0(B_112), u1_pre_topc(B_112))) | ~m1_pre_topc(A_111, B_112) | ~l1_pre_topc(B_112) | ~l1_pre_topc(A_111))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.33/1.52  tff(c_242, plain, (![A_111]: (m1_pre_topc(A_111, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_111, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_111))), inference(superposition, [status(thm), theory('equality')], [c_46, c_229])).
% 3.33/1.52  tff(c_257, plain, (![A_114]: (m1_pre_topc(A_114, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_114, '#skF_2') | ~l1_pre_topc(A_114))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_242])).
% 3.33/1.52  tff(c_28, plain, (![B_24, A_22]: (m1_pre_topc(B_24, A_22) | ~m1_pre_topc(B_24, g1_pre_topc(u1_struct_0(A_22), u1_pre_topc(A_22))) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.33/1.52  tff(c_263, plain, (![A_114]: (m1_pre_topc(A_114, '#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc(A_114, '#skF_2') | ~l1_pre_topc(A_114))), inference(resolution, [status(thm)], [c_257, c_28])).
% 3.33/1.52  tff(c_272, plain, (![A_115]: (m1_pre_topc(A_115, '#skF_3') | ~m1_pre_topc(A_115, '#skF_2') | ~l1_pre_topc(A_115))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_263])).
% 3.33/1.52  tff(c_279, plain, (m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_272])).
% 3.33/1.52  tff(c_286, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_279])).
% 3.33/1.52  tff(c_188, plain, (![B_102, A_103]: (m1_subset_1(u1_struct_0(B_102), k1_zfmisc_1(u1_struct_0(A_103))) | ~m1_pre_topc(B_102, A_103) | ~l1_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.33/1.52  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.33/1.52  tff(c_192, plain, (![B_102, A_103]: (r1_tarski(u1_struct_0(B_102), u1_struct_0(A_103)) | ~m1_pre_topc(B_102, A_103) | ~l1_pre_topc(A_103))), inference(resolution, [status(thm)], [c_188, c_8])).
% 3.33/1.52  tff(c_206, plain, (![B_106, A_107]: (r1_tarski(u1_struct_0(B_106), u1_struct_0(A_107)) | ~m1_pre_topc(B_106, A_107) | ~l1_pre_topc(A_107))), inference(resolution, [status(thm)], [c_188, c_8])).
% 3.33/1.52  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.33/1.52  tff(c_302, plain, (![B_116, A_117]: (u1_struct_0(B_116)=u1_struct_0(A_117) | ~r1_tarski(u1_struct_0(A_117), u1_struct_0(B_116)) | ~m1_pre_topc(B_116, A_117) | ~l1_pre_topc(A_117))), inference(resolution, [status(thm)], [c_206, c_2])).
% 3.33/1.52  tff(c_313, plain, (![B_118, A_119]: (u1_struct_0(B_118)=u1_struct_0(A_119) | ~m1_pre_topc(A_119, B_118) | ~l1_pre_topc(B_118) | ~m1_pre_topc(B_118, A_119) | ~l1_pre_topc(A_119))), inference(resolution, [status(thm)], [c_192, c_302])).
% 3.33/1.52  tff(c_317, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_286, c_313])).
% 3.33/1.52  tff(c_334, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_90, c_317])).
% 3.33/1.52  tff(c_50, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.33/1.52  tff(c_352, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_334, c_50])).
% 3.33/1.52  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.33/1.52  tff(c_351, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_334, c_48])).
% 3.33/1.52  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.33/1.52  tff(c_423, plain, (![C_126, F_124, B_127, A_125, D_128]: (r1_funct_2(A_125, B_127, C_126, D_128, F_124, F_124) | ~m1_subset_1(F_124, k1_zfmisc_1(k2_zfmisc_1(C_126, D_128))) | ~v1_funct_2(F_124, C_126, D_128) | ~m1_subset_1(F_124, k1_zfmisc_1(k2_zfmisc_1(A_125, B_127))) | ~v1_funct_2(F_124, A_125, B_127) | ~v1_funct_1(F_124) | v1_xboole_0(D_128) | v1_xboole_0(B_127))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.33/1.52  tff(c_850, plain, (![D_161, C_163, A_164, B_165, A_162]: (r1_funct_2(A_164, B_165, C_163, D_161, A_162, A_162) | ~v1_funct_2(A_162, C_163, D_161) | ~m1_subset_1(A_162, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))) | ~v1_funct_2(A_162, A_164, B_165) | ~v1_funct_1(A_162) | v1_xboole_0(D_161) | v1_xboole_0(B_165) | ~r1_tarski(A_162, k2_zfmisc_1(C_163, D_161)))), inference(resolution, [status(thm)], [c_10, c_423])).
% 3.33/1.52  tff(c_852, plain, (![C_163, D_161]: (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), C_163, D_161, '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', C_163, D_161) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(D_161) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski('#skF_4', k2_zfmisc_1(C_163, D_161)))), inference(resolution, [status(thm)], [c_351, c_850])).
% 3.33/1.52  tff(c_858, plain, (![C_163, D_161]: (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), C_163, D_161, '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', C_163, D_161) | v1_xboole_0(D_161) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski('#skF_4', k2_zfmisc_1(C_163, D_161)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_352, c_852])).
% 3.33/1.52  tff(c_884, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_858])).
% 3.33/1.52  tff(c_26, plain, (![A_21]: (~v1_xboole_0(u1_struct_0(A_21)) | ~l1_struct_0(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.33/1.52  tff(c_892, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_884, c_26])).
% 3.33/1.52  tff(c_895, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_68, c_892])).
% 3.33/1.52  tff(c_898, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_895])).
% 3.33/1.52  tff(c_902, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_898])).
% 3.33/1.52  tff(c_904, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_858])).
% 3.33/1.52  tff(c_104, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_48, c_8])).
% 3.33/1.52  tff(c_350, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_334, c_104])).
% 3.33/1.52  tff(c_905, plain, (![C_170, D_171]: (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), C_170, D_171, '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', C_170, D_171) | v1_xboole_0(D_171) | ~r1_tarski('#skF_4', k2_zfmisc_1(C_170, D_171)))), inference(splitRight, [status(thm)], [c_858])).
% 3.33/1.52  tff(c_66, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.33/1.52  tff(c_20, plain, (![A_13, B_14, C_15, D_16]: (k2_partfun1(A_13, B_14, C_15, D_16)=k7_relat_1(C_15, D_16) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_1(C_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.33/1.52  tff(c_449, plain, (![D_16]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', D_16)=k7_relat_1('#skF_4', D_16) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_351, c_20])).
% 3.33/1.52  tff(c_467, plain, (![D_16]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', D_16)=k7_relat_1('#skF_4', D_16))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_449])).
% 3.33/1.52  tff(c_62, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.33/1.52  tff(c_60, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.33/1.52  tff(c_640, plain, (![A_142, B_143, C_144, D_145]: (k2_partfun1(u1_struct_0(A_142), u1_struct_0(B_143), C_144, u1_struct_0(D_145))=k2_tmap_1(A_142, B_143, C_144, D_145) | ~m1_pre_topc(D_145, A_142) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_142), u1_struct_0(B_143)))) | ~v1_funct_2(C_144, u1_struct_0(A_142), u1_struct_0(B_143)) | ~v1_funct_1(C_144) | ~l1_pre_topc(B_143) | ~v2_pre_topc(B_143) | v2_struct_0(B_143) | ~l1_pre_topc(A_142) | ~v2_pre_topc(A_142) | v2_struct_0(A_142))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.33/1.52  tff(c_644, plain, (![B_143, C_144, D_145]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0(B_143), C_144, u1_struct_0(D_145))=k2_tmap_1('#skF_2', B_143, C_144, D_145) | ~m1_pre_topc(D_145, '#skF_2') | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_143)))) | ~v1_funct_2(C_144, u1_struct_0('#skF_2'), u1_struct_0(B_143)) | ~v1_funct_1(C_144) | ~l1_pre_topc(B_143) | ~v2_pre_topc(B_143) | v2_struct_0(B_143) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_334, c_640])).
% 3.33/1.52  tff(c_655, plain, (![B_143, C_144, D_145]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_143), C_144, u1_struct_0(D_145))=k2_tmap_1('#skF_2', B_143, C_144, D_145) | ~m1_pre_topc(D_145, '#skF_2') | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_143)))) | ~v1_funct_2(C_144, u1_struct_0('#skF_3'), u1_struct_0(B_143)) | ~v1_funct_1(C_144) | ~l1_pre_topc(B_143) | ~v2_pre_topc(B_143) | v2_struct_0(B_143) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_334, c_334, c_644])).
% 3.33/1.52  tff(c_800, plain, (![B_157, C_158, D_159]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_157), C_158, u1_struct_0(D_159))=k2_tmap_1('#skF_2', B_157, C_158, D_159) | ~m1_pre_topc(D_159, '#skF_2') | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_157)))) | ~v1_funct_2(C_158, u1_struct_0('#skF_3'), u1_struct_0(B_157)) | ~v1_funct_1(C_158) | ~l1_pre_topc(B_157) | ~v2_pre_topc(B_157) | v2_struct_0(B_157))), inference(negUnitSimplification, [status(thm)], [c_62, c_655])).
% 3.33/1.52  tff(c_802, plain, (![D_159]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_159))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_159) | ~m1_pre_topc(D_159, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_351, c_800])).
% 3.33/1.52  tff(c_810, plain, (![D_159]: (k7_relat_1('#skF_4', u1_struct_0(D_159))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_159) | ~m1_pre_topc(D_159, '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_52, c_352, c_467, c_802])).
% 3.33/1.52  tff(c_816, plain, (![D_160]: (k7_relat_1('#skF_4', u1_struct_0(D_160))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_160) | ~m1_pre_topc(D_160, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_68, c_810])).
% 3.33/1.52  tff(c_14, plain, (![C_9, A_7, B_8]: (v1_relat_1(C_9) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.33/1.52  tff(c_103, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_14])).
% 3.33/1.52  tff(c_127, plain, (![C_84, A_85, B_86]: (v4_relat_1(C_84, A_85) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.33/1.52  tff(c_135, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_127])).
% 3.33/1.52  tff(c_175, plain, (![B_100, A_101]: (k7_relat_1(B_100, A_101)=B_100 | ~v4_relat_1(B_100, A_101) | ~v1_relat_1(B_100))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.33/1.52  tff(c_181, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_135, c_175])).
% 3.33/1.52  tff(c_187, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_103, c_181])).
% 3.33/1.52  tff(c_347, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_334, c_187])).
% 3.33/1.52  tff(c_822, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_816, c_347])).
% 3.33/1.52  tff(c_834, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_822])).
% 3.33/1.52  tff(c_44, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_185])).
% 3.33/1.52  tff(c_346, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_334, c_44])).
% 3.33/1.52  tff(c_840, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_834, c_346])).
% 3.33/1.52  tff(c_908, plain, (~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_905, c_840])).
% 3.33/1.52  tff(c_913, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_350, c_352, c_908])).
% 3.33/1.52  tff(c_915, plain, $false, inference(negUnitSimplification, [status(thm)], [c_904, c_913])).
% 3.33/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.52  
% 3.33/1.52  Inference rules
% 3.33/1.52  ----------------------
% 3.33/1.52  #Ref     : 0
% 3.33/1.52  #Sup     : 162
% 3.33/1.52  #Fact    : 0
% 3.33/1.52  #Define  : 0
% 3.33/1.52  #Split   : 6
% 3.33/1.52  #Chain   : 0
% 3.33/1.52  #Close   : 0
% 3.33/1.52  
% 3.33/1.52  Ordering : KBO
% 3.33/1.52  
% 3.33/1.52  Simplification rules
% 3.33/1.52  ----------------------
% 3.33/1.52  #Subsume      : 25
% 3.33/1.52  #Demod        : 197
% 3.33/1.52  #Tautology    : 72
% 3.33/1.52  #SimpNegUnit  : 8
% 3.33/1.52  #BackRed      : 9
% 3.33/1.52  
% 3.33/1.52  #Partial instantiations: 0
% 3.33/1.52  #Strategies tried      : 1
% 3.33/1.52  
% 3.33/1.52  Timing (in seconds)
% 3.33/1.52  ----------------------
% 3.33/1.52  Preprocessing        : 0.35
% 3.33/1.52  Parsing              : 0.19
% 3.33/1.52  CNF conversion       : 0.03
% 3.33/1.52  Main loop            : 0.38
% 3.33/1.52  Inferencing          : 0.13
% 3.33/1.52  Reduction            : 0.13
% 3.33/1.52  Demodulation         : 0.09
% 3.33/1.52  BG Simplification    : 0.02
% 3.33/1.52  Subsumption          : 0.08
% 3.33/1.52  Abstraction          : 0.02
% 3.33/1.52  MUC search           : 0.00
% 3.33/1.52  Cooper               : 0.00
% 3.33/1.52  Total                : 0.78
% 3.33/1.52  Index Insertion      : 0.00
% 3.33/1.52  Index Deletion       : 0.00
% 3.33/1.52  Index Matching       : 0.00
% 3.33/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
