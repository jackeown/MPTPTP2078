%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:56 EST 2020

% Result     : Theorem 3.76s
% Output     : CNFRefutation 4.08s
% Verified   : 
% Statistics : Number of formulae       :  129 (1032 expanded)
%              Number of leaves         :   48 ( 378 expanded)
%              Depth                    :   21
%              Number of atoms          :  288 (4272 expanded)
%              Number of equality atoms :   30 ( 308 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_196,negated_conjecture,(
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

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_163,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_159,axiom,(
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

tff(f_125,axiom,(
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

tff(f_87,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_152,axiom,(
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

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(c_70,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_28,plain,(
    ! [A_21] :
      ( l1_struct_0(A_21)
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_64,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_60,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_82,plain,(
    ! [B_76,A_77] :
      ( l1_pre_topc(B_76)
      | ~ m1_pre_topc(B_76,A_77)
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_88,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_82])).

tff(c_92,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_88])).

tff(c_48,plain,(
    ! [A_56] :
      ( m1_pre_topc(A_56,A_56)
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_52,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_356,plain,(
    ! [A_141,B_142] :
      ( m1_pre_topc(A_141,g1_pre_topc(u1_struct_0(B_142),u1_pre_topc(B_142)))
      | ~ m1_pre_topc(A_141,B_142)
      | ~ l1_pre_topc(B_142)
      | ~ l1_pre_topc(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_369,plain,(
    ! [A_141] :
      ( m1_pre_topc(A_141,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_141,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_141) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_356])).

tff(c_384,plain,(
    ! [A_144] :
      ( m1_pre_topc(A_144,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_144,'#skF_2')
      | ~ l1_pre_topc(A_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_369])).

tff(c_34,plain,(
    ! [B_28,A_26] :
      ( m1_pre_topc(B_28,A_26)
      | ~ m1_pre_topc(B_28,g1_pre_topc(u1_struct_0(A_26),u1_pre_topc(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_390,plain,(
    ! [A_144] :
      ( m1_pre_topc(A_144,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_pre_topc(A_144,'#skF_2')
      | ~ l1_pre_topc(A_144) ) ),
    inference(resolution,[status(thm)],[c_384,c_34])).

tff(c_409,plain,(
    ! [A_149] :
      ( m1_pre_topc(A_149,'#skF_3')
      | ~ m1_pre_topc(A_149,'#skF_2')
      | ~ l1_pre_topc(A_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_390])).

tff(c_416,plain,
    ( m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_409])).

tff(c_423,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_416])).

tff(c_275,plain,(
    ! [B_116,A_117] :
      ( m1_subset_1(u1_struct_0(B_116),k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ m1_pre_topc(B_116,A_117)
      | ~ l1_pre_topc(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_283,plain,(
    ! [B_116,A_117] :
      ( r1_tarski(u1_struct_0(B_116),u1_struct_0(A_117))
      | ~ m1_pre_topc(B_116,A_117)
      | ~ l1_pre_topc(A_117) ) ),
    inference(resolution,[status(thm)],[c_275,c_8])).

tff(c_285,plain,(
    ! [B_120,A_121] :
      ( r1_tarski(u1_struct_0(B_120),u1_struct_0(A_121))
      | ~ m1_pre_topc(B_120,A_121)
      | ~ l1_pre_topc(A_121) ) ),
    inference(resolution,[status(thm)],[c_275,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_448,plain,(
    ! [B_151,A_152] :
      ( u1_struct_0(B_151) = u1_struct_0(A_152)
      | ~ r1_tarski(u1_struct_0(A_152),u1_struct_0(B_151))
      | ~ m1_pre_topc(B_151,A_152)
      | ~ l1_pre_topc(A_152) ) ),
    inference(resolution,[status(thm)],[c_285,c_2])).

tff(c_459,plain,(
    ! [B_153,A_154] :
      ( u1_struct_0(B_153) = u1_struct_0(A_154)
      | ~ m1_pre_topc(A_154,B_153)
      | ~ l1_pre_topc(B_153)
      | ~ m1_pre_topc(B_153,A_154)
      | ~ l1_pre_topc(A_154) ) ),
    inference(resolution,[status(thm)],[c_283,c_448])).

tff(c_463,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_423,c_459])).

tff(c_480,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_92,c_463])).

tff(c_56,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_500,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_56])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_499,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_54])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_549,plain,(
    ! [B_155,A_158,D_159,F_156,C_157] :
      ( r1_funct_2(A_158,B_155,C_157,D_159,F_156,F_156)
      | ~ m1_subset_1(F_156,k1_zfmisc_1(k2_zfmisc_1(C_157,D_159)))
      | ~ v1_funct_2(F_156,C_157,D_159)
      | ~ m1_subset_1(F_156,k1_zfmisc_1(k2_zfmisc_1(A_158,B_155)))
      | ~ v1_funct_2(F_156,A_158,B_155)
      | ~ v1_funct_1(F_156)
      | v1_xboole_0(D_159)
      | v1_xboole_0(B_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1033,plain,(
    ! [A_190,B_191,D_193,C_194,A_192] :
      ( r1_funct_2(A_190,B_191,C_194,D_193,A_192,A_192)
      | ~ v1_funct_2(A_192,C_194,D_193)
      | ~ m1_subset_1(A_192,k1_zfmisc_1(k2_zfmisc_1(A_190,B_191)))
      | ~ v1_funct_2(A_192,A_190,B_191)
      | ~ v1_funct_1(A_192)
      | v1_xboole_0(D_193)
      | v1_xboole_0(B_191)
      | ~ r1_tarski(A_192,k2_zfmisc_1(C_194,D_193)) ) ),
    inference(resolution,[status(thm)],[c_10,c_549])).

tff(c_1035,plain,(
    ! [C_194,D_193] :
      ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),C_194,D_193,'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',C_194,D_193)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(D_193)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(C_194,D_193)) ) ),
    inference(resolution,[status(thm)],[c_499,c_1033])).

tff(c_1041,plain,(
    ! [C_194,D_193] :
      ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),C_194,D_193,'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',C_194,D_193)
      | v1_xboole_0(D_193)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(C_194,D_193)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_500,c_1035])).

tff(c_1221,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1041])).

tff(c_32,plain,(
    ! [A_25] :
      ( ~ v1_xboole_0(u1_struct_0(A_25))
      | ~ l1_struct_0(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1224,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1221,c_32])).

tff(c_1227,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1224])).

tff(c_1230,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_1227])).

tff(c_1234,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1230])).

tff(c_1236,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1041])).

tff(c_101,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_54,c_8])).

tff(c_498,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_101])).

tff(c_1251,plain,(
    ! [C_240,D_241] :
      ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),C_240,D_241,'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',C_240,D_241)
      | v1_xboole_0(D_241)
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(C_240,D_241)) ) ),
    inference(splitRight,[status(thm)],[c_1041])).

tff(c_72,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_399,plain,(
    ! [A_145,B_146,C_147,D_148] :
      ( k2_partfun1(A_145,B_146,C_147,D_148) = k7_relat_1(C_147,D_148)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146)))
      | ~ v1_funct_1(C_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_401,plain,(
    ! [D_148] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_148) = k7_relat_1('#skF_4',D_148)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_399])).

tff(c_407,plain,(
    ! [D_148] : k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_148) = k7_relat_1('#skF_4',D_148) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_401])).

tff(c_491,plain,(
    ! [D_148] : k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',D_148) = k7_relat_1('#skF_4',D_148) ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_407])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_66,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_676,plain,(
    ! [A_168,B_169,C_170,D_171] :
      ( k2_partfun1(u1_struct_0(A_168),u1_struct_0(B_169),C_170,u1_struct_0(D_171)) = k2_tmap_1(A_168,B_169,C_170,D_171)
      | ~ m1_pre_topc(D_171,A_168)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_168),u1_struct_0(B_169))))
      | ~ v1_funct_2(C_170,u1_struct_0(A_168),u1_struct_0(B_169))
      | ~ v1_funct_1(C_170)
      | ~ l1_pre_topc(B_169)
      | ~ v2_pre_topc(B_169)
      | v2_struct_0(B_169)
      | ~ l1_pre_topc(A_168)
      | ~ v2_pre_topc(A_168)
      | v2_struct_0(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_680,plain,(
    ! [B_169,C_170,D_171] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0(B_169),C_170,u1_struct_0(D_171)) = k2_tmap_1('#skF_2',B_169,C_170,D_171)
      | ~ m1_pre_topc(D_171,'#skF_2')
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_169))))
      | ~ v1_funct_2(C_170,u1_struct_0('#skF_2'),u1_struct_0(B_169))
      | ~ v1_funct_1(C_170)
      | ~ l1_pre_topc(B_169)
      | ~ v2_pre_topc(B_169)
      | v2_struct_0(B_169)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_676])).

tff(c_691,plain,(
    ! [B_169,C_170,D_171] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_169),C_170,u1_struct_0(D_171)) = k2_tmap_1('#skF_2',B_169,C_170,D_171)
      | ~ m1_pre_topc(D_171,'#skF_2')
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_169))))
      | ~ v1_funct_2(C_170,u1_struct_0('#skF_3'),u1_struct_0(B_169))
      | ~ v1_funct_1(C_170)
      | ~ l1_pre_topc(B_169)
      | ~ v2_pre_topc(B_169)
      | v2_struct_0(B_169)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_480,c_480,c_680])).

tff(c_983,plain,(
    ! [B_186,C_187,D_188] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_186),C_187,u1_struct_0(D_188)) = k2_tmap_1('#skF_2',B_186,C_187,D_188)
      | ~ m1_pre_topc(D_188,'#skF_2')
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_186))))
      | ~ v1_funct_2(C_187,u1_struct_0('#skF_3'),u1_struct_0(B_186))
      | ~ v1_funct_1(C_187)
      | ~ l1_pre_topc(B_186)
      | ~ v2_pre_topc(B_186)
      | v2_struct_0(B_186) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_691])).

tff(c_985,plain,(
    ! [D_188] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_188)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_188)
      | ~ m1_pre_topc(D_188,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_499,c_983])).

tff(c_993,plain,(
    ! [D_188] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_188)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_188)
      | ~ m1_pre_topc(D_188,'#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_58,c_500,c_491,c_985])).

tff(c_999,plain,(
    ! [D_189] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_189)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_189)
      | ~ m1_pre_topc(D_189,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_993])).

tff(c_18,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_102,plain,(
    ! [B_80,A_81] :
      ( v1_relat_1(B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_81))
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_105,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_54,c_102])).

tff(c_111,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_105])).

tff(c_184,plain,(
    ! [C_99,A_100,B_101] :
      ( v4_relat_1(C_99,A_100)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_192,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_184])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(B_9),A_8)
      | ~ v4_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_194,plain,(
    ! [B_102,A_103] :
      ( k7_relat_1(B_102,A_103) = B_102
      | ~ r1_tarski(k1_relat_1(B_102),A_103)
      | ~ v1_relat_1(B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_230,plain,(
    ! [B_110,A_111] :
      ( k7_relat_1(B_110,A_111) = B_110
      | ~ v4_relat_1(B_110,A_111)
      | ~ v1_relat_1(B_110) ) ),
    inference(resolution,[status(thm)],[c_16,c_194])).

tff(c_236,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_192,c_230])).

tff(c_245,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_236])).

tff(c_494,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_245])).

tff(c_1005,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_999,c_494])).

tff(c_1017,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1005])).

tff(c_50,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_495,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_50])).

tff(c_1023,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1017,c_495])).

tff(c_1254,plain,
    ( ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_1251,c_1023])).

tff(c_1259,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_500,c_1254])).

tff(c_1261,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1236,c_1259])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:07:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.76/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.76/1.62  
% 3.76/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.76/1.63  %$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.76/1.63  
% 3.76/1.63  %Foreground sorts:
% 3.76/1.63  
% 3.76/1.63  
% 3.76/1.63  %Background operators:
% 3.76/1.63  
% 3.76/1.63  
% 3.76/1.63  %Foreground operators:
% 3.76/1.63  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.76/1.63  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.76/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.76/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.76/1.63  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.76/1.63  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.76/1.63  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.76/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.76/1.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.76/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.76/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.76/1.63  tff('#skF_1', type, '#skF_1': $i).
% 3.76/1.63  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.76/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.76/1.63  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.76/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.76/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.76/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.76/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.76/1.63  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 3.76/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.76/1.63  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.76/1.63  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.76/1.63  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.76/1.63  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.76/1.63  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.76/1.63  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.76/1.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.76/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.76/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.76/1.63  
% 4.08/1.65  tff(f_196, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_tmap_1)).
% 4.08/1.65  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.08/1.65  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.08/1.65  tff(f_163, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 4.08/1.65  tff(f_103, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 4.08/1.65  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 4.08/1.65  tff(f_159, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.08/1.65  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.08/1.65  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.08/1.65  tff(f_125, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 4.08/1.65  tff(f_87, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.08/1.65  tff(f_68, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 4.08/1.65  tff(f_152, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 4.08/1.65  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.08/1.65  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.08/1.65  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.08/1.65  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 4.08/1.65  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 4.08/1.65  tff(c_70, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.08/1.65  tff(c_28, plain, (![A_21]: (l1_struct_0(A_21) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.08/1.65  tff(c_74, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.08/1.65  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.08/1.65  tff(c_64, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.08/1.65  tff(c_60, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.08/1.65  tff(c_82, plain, (![B_76, A_77]: (l1_pre_topc(B_76) | ~m1_pre_topc(B_76, A_77) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.08/1.65  tff(c_88, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_82])).
% 4.08/1.65  tff(c_92, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_88])).
% 4.08/1.65  tff(c_48, plain, (![A_56]: (m1_pre_topc(A_56, A_56) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.08/1.65  tff(c_52, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.08/1.65  tff(c_356, plain, (![A_141, B_142]: (m1_pre_topc(A_141, g1_pre_topc(u1_struct_0(B_142), u1_pre_topc(B_142))) | ~m1_pre_topc(A_141, B_142) | ~l1_pre_topc(B_142) | ~l1_pre_topc(A_141))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.08/1.65  tff(c_369, plain, (![A_141]: (m1_pre_topc(A_141, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_141, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_141))), inference(superposition, [status(thm), theory('equality')], [c_52, c_356])).
% 4.08/1.65  tff(c_384, plain, (![A_144]: (m1_pre_topc(A_144, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_144, '#skF_2') | ~l1_pre_topc(A_144))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_369])).
% 4.08/1.65  tff(c_34, plain, (![B_28, A_26]: (m1_pre_topc(B_28, A_26) | ~m1_pre_topc(B_28, g1_pre_topc(u1_struct_0(A_26), u1_pre_topc(A_26))) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.08/1.65  tff(c_390, plain, (![A_144]: (m1_pre_topc(A_144, '#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc(A_144, '#skF_2') | ~l1_pre_topc(A_144))), inference(resolution, [status(thm)], [c_384, c_34])).
% 4.08/1.65  tff(c_409, plain, (![A_149]: (m1_pre_topc(A_149, '#skF_3') | ~m1_pre_topc(A_149, '#skF_2') | ~l1_pre_topc(A_149))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_390])).
% 4.08/1.65  tff(c_416, plain, (m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_409])).
% 4.08/1.65  tff(c_423, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_416])).
% 4.08/1.65  tff(c_275, plain, (![B_116, A_117]: (m1_subset_1(u1_struct_0(B_116), k1_zfmisc_1(u1_struct_0(A_117))) | ~m1_pre_topc(B_116, A_117) | ~l1_pre_topc(A_117))), inference(cnfTransformation, [status(thm)], [f_159])).
% 4.08/1.65  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.08/1.65  tff(c_283, plain, (![B_116, A_117]: (r1_tarski(u1_struct_0(B_116), u1_struct_0(A_117)) | ~m1_pre_topc(B_116, A_117) | ~l1_pre_topc(A_117))), inference(resolution, [status(thm)], [c_275, c_8])).
% 4.08/1.65  tff(c_285, plain, (![B_120, A_121]: (r1_tarski(u1_struct_0(B_120), u1_struct_0(A_121)) | ~m1_pre_topc(B_120, A_121) | ~l1_pre_topc(A_121))), inference(resolution, [status(thm)], [c_275, c_8])).
% 4.08/1.65  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.08/1.65  tff(c_448, plain, (![B_151, A_152]: (u1_struct_0(B_151)=u1_struct_0(A_152) | ~r1_tarski(u1_struct_0(A_152), u1_struct_0(B_151)) | ~m1_pre_topc(B_151, A_152) | ~l1_pre_topc(A_152))), inference(resolution, [status(thm)], [c_285, c_2])).
% 4.08/1.65  tff(c_459, plain, (![B_153, A_154]: (u1_struct_0(B_153)=u1_struct_0(A_154) | ~m1_pre_topc(A_154, B_153) | ~l1_pre_topc(B_153) | ~m1_pre_topc(B_153, A_154) | ~l1_pre_topc(A_154))), inference(resolution, [status(thm)], [c_283, c_448])).
% 4.08/1.65  tff(c_463, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_423, c_459])).
% 4.08/1.65  tff(c_480, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_92, c_463])).
% 4.08/1.65  tff(c_56, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.08/1.65  tff(c_500, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_480, c_56])).
% 4.08/1.65  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.08/1.65  tff(c_499, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_480, c_54])).
% 4.08/1.65  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.08/1.65  tff(c_549, plain, (![B_155, A_158, D_159, F_156, C_157]: (r1_funct_2(A_158, B_155, C_157, D_159, F_156, F_156) | ~m1_subset_1(F_156, k1_zfmisc_1(k2_zfmisc_1(C_157, D_159))) | ~v1_funct_2(F_156, C_157, D_159) | ~m1_subset_1(F_156, k1_zfmisc_1(k2_zfmisc_1(A_158, B_155))) | ~v1_funct_2(F_156, A_158, B_155) | ~v1_funct_1(F_156) | v1_xboole_0(D_159) | v1_xboole_0(B_155))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.08/1.65  tff(c_1033, plain, (![A_190, B_191, D_193, C_194, A_192]: (r1_funct_2(A_190, B_191, C_194, D_193, A_192, A_192) | ~v1_funct_2(A_192, C_194, D_193) | ~m1_subset_1(A_192, k1_zfmisc_1(k2_zfmisc_1(A_190, B_191))) | ~v1_funct_2(A_192, A_190, B_191) | ~v1_funct_1(A_192) | v1_xboole_0(D_193) | v1_xboole_0(B_191) | ~r1_tarski(A_192, k2_zfmisc_1(C_194, D_193)))), inference(resolution, [status(thm)], [c_10, c_549])).
% 4.08/1.65  tff(c_1035, plain, (![C_194, D_193]: (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), C_194, D_193, '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', C_194, D_193) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(D_193) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski('#skF_4', k2_zfmisc_1(C_194, D_193)))), inference(resolution, [status(thm)], [c_499, c_1033])).
% 4.08/1.65  tff(c_1041, plain, (![C_194, D_193]: (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), C_194, D_193, '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', C_194, D_193) | v1_xboole_0(D_193) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski('#skF_4', k2_zfmisc_1(C_194, D_193)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_500, c_1035])).
% 4.08/1.65  tff(c_1221, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_1041])).
% 4.08/1.65  tff(c_32, plain, (![A_25]: (~v1_xboole_0(u1_struct_0(A_25)) | ~l1_struct_0(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.08/1.65  tff(c_1224, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1221, c_32])).
% 4.08/1.65  tff(c_1227, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_74, c_1224])).
% 4.08/1.65  tff(c_1230, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_1227])).
% 4.08/1.65  tff(c_1234, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_1230])).
% 4.08/1.65  tff(c_1236, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_1041])).
% 4.08/1.65  tff(c_101, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_54, c_8])).
% 4.08/1.65  tff(c_498, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_480, c_101])).
% 4.08/1.65  tff(c_1251, plain, (![C_240, D_241]: (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), C_240, D_241, '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', C_240, D_241) | v1_xboole_0(D_241) | ~r1_tarski('#skF_4', k2_zfmisc_1(C_240, D_241)))), inference(splitRight, [status(thm)], [c_1041])).
% 4.08/1.65  tff(c_72, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.08/1.65  tff(c_399, plain, (![A_145, B_146, C_147, D_148]: (k2_partfun1(A_145, B_146, C_147, D_148)=k7_relat_1(C_147, D_148) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))) | ~v1_funct_1(C_147))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.08/1.65  tff(c_401, plain, (![D_148]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_148)=k7_relat_1('#skF_4', D_148) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_399])).
% 4.08/1.65  tff(c_407, plain, (![D_148]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_148)=k7_relat_1('#skF_4', D_148))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_401])).
% 4.08/1.65  tff(c_491, plain, (![D_148]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', D_148)=k7_relat_1('#skF_4', D_148))), inference(demodulation, [status(thm), theory('equality')], [c_480, c_407])).
% 4.08/1.65  tff(c_68, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.08/1.65  tff(c_66, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.08/1.65  tff(c_676, plain, (![A_168, B_169, C_170, D_171]: (k2_partfun1(u1_struct_0(A_168), u1_struct_0(B_169), C_170, u1_struct_0(D_171))=k2_tmap_1(A_168, B_169, C_170, D_171) | ~m1_pre_topc(D_171, A_168) | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_168), u1_struct_0(B_169)))) | ~v1_funct_2(C_170, u1_struct_0(A_168), u1_struct_0(B_169)) | ~v1_funct_1(C_170) | ~l1_pre_topc(B_169) | ~v2_pre_topc(B_169) | v2_struct_0(B_169) | ~l1_pre_topc(A_168) | ~v2_pre_topc(A_168) | v2_struct_0(A_168))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.08/1.65  tff(c_680, plain, (![B_169, C_170, D_171]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0(B_169), C_170, u1_struct_0(D_171))=k2_tmap_1('#skF_2', B_169, C_170, D_171) | ~m1_pre_topc(D_171, '#skF_2') | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_169)))) | ~v1_funct_2(C_170, u1_struct_0('#skF_2'), u1_struct_0(B_169)) | ~v1_funct_1(C_170) | ~l1_pre_topc(B_169) | ~v2_pre_topc(B_169) | v2_struct_0(B_169) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_480, c_676])).
% 4.08/1.65  tff(c_691, plain, (![B_169, C_170, D_171]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_169), C_170, u1_struct_0(D_171))=k2_tmap_1('#skF_2', B_169, C_170, D_171) | ~m1_pre_topc(D_171, '#skF_2') | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_169)))) | ~v1_funct_2(C_170, u1_struct_0('#skF_3'), u1_struct_0(B_169)) | ~v1_funct_1(C_170) | ~l1_pre_topc(B_169) | ~v2_pre_topc(B_169) | v2_struct_0(B_169) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_480, c_480, c_680])).
% 4.08/1.65  tff(c_983, plain, (![B_186, C_187, D_188]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_186), C_187, u1_struct_0(D_188))=k2_tmap_1('#skF_2', B_186, C_187, D_188) | ~m1_pre_topc(D_188, '#skF_2') | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_186)))) | ~v1_funct_2(C_187, u1_struct_0('#skF_3'), u1_struct_0(B_186)) | ~v1_funct_1(C_187) | ~l1_pre_topc(B_186) | ~v2_pre_topc(B_186) | v2_struct_0(B_186))), inference(negUnitSimplification, [status(thm)], [c_68, c_691])).
% 4.08/1.65  tff(c_985, plain, (![D_188]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_188))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_188) | ~m1_pre_topc(D_188, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_499, c_983])).
% 4.08/1.65  tff(c_993, plain, (![D_188]: (k7_relat_1('#skF_4', u1_struct_0(D_188))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_188) | ~m1_pre_topc(D_188, '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_58, c_500, c_491, c_985])).
% 4.08/1.65  tff(c_999, plain, (![D_189]: (k7_relat_1('#skF_4', u1_struct_0(D_189))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_189) | ~m1_pre_topc(D_189, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_74, c_993])).
% 4.08/1.65  tff(c_18, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.08/1.65  tff(c_102, plain, (![B_80, A_81]: (v1_relat_1(B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(A_81)) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.08/1.65  tff(c_105, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_54, c_102])).
% 4.08/1.65  tff(c_111, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_105])).
% 4.08/1.65  tff(c_184, plain, (![C_99, A_100, B_101]: (v4_relat_1(C_99, A_100) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.08/1.65  tff(c_192, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_54, c_184])).
% 4.08/1.65  tff(c_16, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(B_9), A_8) | ~v4_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.08/1.65  tff(c_194, plain, (![B_102, A_103]: (k7_relat_1(B_102, A_103)=B_102 | ~r1_tarski(k1_relat_1(B_102), A_103) | ~v1_relat_1(B_102))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.08/1.65  tff(c_230, plain, (![B_110, A_111]: (k7_relat_1(B_110, A_111)=B_110 | ~v4_relat_1(B_110, A_111) | ~v1_relat_1(B_110))), inference(resolution, [status(thm)], [c_16, c_194])).
% 4.08/1.65  tff(c_236, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_192, c_230])).
% 4.08/1.65  tff(c_245, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_111, c_236])).
% 4.08/1.65  tff(c_494, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_480, c_245])).
% 4.08/1.65  tff(c_1005, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_999, c_494])).
% 4.08/1.65  tff(c_1017, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1005])).
% 4.08/1.65  tff(c_50, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.08/1.65  tff(c_495, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_480, c_50])).
% 4.08/1.65  tff(c_1023, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1017, c_495])).
% 4.08/1.65  tff(c_1254, plain, (~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_1251, c_1023])).
% 4.08/1.65  tff(c_1259, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_498, c_500, c_1254])).
% 4.08/1.65  tff(c_1261, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1236, c_1259])).
% 4.08/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.08/1.65  
% 4.08/1.65  Inference rules
% 4.08/1.65  ----------------------
% 4.08/1.65  #Ref     : 0
% 4.08/1.65  #Sup     : 229
% 4.08/1.65  #Fact    : 0
% 4.08/1.65  #Define  : 0
% 4.08/1.65  #Split   : 7
% 4.08/1.65  #Chain   : 0
% 4.08/1.65  #Close   : 0
% 4.08/1.65  
% 4.08/1.65  Ordering : KBO
% 4.08/1.65  
% 4.08/1.65  Simplification rules
% 4.08/1.65  ----------------------
% 4.08/1.65  #Subsume      : 37
% 4.08/1.65  #Demod        : 257
% 4.08/1.65  #Tautology    : 88
% 4.08/1.65  #SimpNegUnit  : 16
% 4.08/1.65  #BackRed      : 11
% 4.08/1.65  
% 4.08/1.65  #Partial instantiations: 0
% 4.08/1.65  #Strategies tried      : 1
% 4.08/1.65  
% 4.08/1.65  Timing (in seconds)
% 4.08/1.65  ----------------------
% 4.08/1.65  Preprocessing        : 0.37
% 4.08/1.65  Parsing              : 0.20
% 4.08/1.65  CNF conversion       : 0.03
% 4.08/1.65  Main loop            : 0.49
% 4.08/1.65  Inferencing          : 0.18
% 4.08/1.65  Reduction            : 0.16
% 4.08/1.65  Demodulation         : 0.11
% 4.08/1.65  BG Simplification    : 0.03
% 4.08/1.65  Subsumption          : 0.10
% 4.08/1.65  Abstraction          : 0.02
% 4.08/1.65  MUC search           : 0.00
% 4.08/1.65  Cooper               : 0.00
% 4.08/1.65  Total                : 0.91
% 4.08/1.65  Index Insertion      : 0.00
% 4.08/1.65  Index Deletion       : 0.00
% 4.08/1.65  Index Matching       : 0.00
% 4.08/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
