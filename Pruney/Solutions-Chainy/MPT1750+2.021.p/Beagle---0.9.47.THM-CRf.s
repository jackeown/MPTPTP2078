%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:54 EST 2020

% Result     : Theorem 5.10s
% Output     : CNFRefutation 5.29s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 912 expanded)
%              Number of leaves         :   49 ( 336 expanded)
%              Depth                    :   19
%              Number of atoms          :  406 (3936 expanded)
%              Number of equality atoms :   44 ( 367 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

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

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

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

tff(f_238,negated_conjecture,(
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

tff(f_205,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => k1_tsep_1(A,B,B) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).

tff(f_142,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

tff(f_160,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( ( v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v2_pre_topc(C)
                & l1_pre_topc(C) )
             => ( B = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C))
               => ( m1_pre_topc(B,A)
                <=> m1_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tmap_1)).

tff(f_167,axiom,(
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

tff(f_190,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( m1_pre_topc(B,C)
              <=> k1_tsep_1(A,B,C) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tsep_1)).

tff(f_106,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

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

tff(f_133,axiom,(
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

tff(c_74,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_22,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_68,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_64,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_82,plain,(
    ! [B_80,A_81] :
      ( l1_pre_topc(B_80)
      | ~ m1_pre_topc(B_80,A_81)
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_85,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_82])).

tff(c_88,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_85])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_70,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_302,plain,(
    ! [A_138,B_139] :
      ( k1_tsep_1(A_138,B_139,B_139) = g1_pre_topc(u1_struct_0(B_139),u1_pre_topc(B_139))
      | ~ m1_pre_topc(B_139,A_138)
      | v2_struct_0(B_139)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_308,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k1_tsep_1('#skF_2','#skF_3','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_302])).

tff(c_313,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k1_tsep_1('#skF_2','#skF_3','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_308])).

tff(c_314,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k1_tsep_1('#skF_2','#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_313])).

tff(c_38,plain,(
    ! [B_46,A_44] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_46),u1_pre_topc(B_46)),A_44)
      | ~ m1_pre_topc(B_46,A_44)
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_323,plain,(
    ! [A_44] :
      ( m1_pre_topc(k1_tsep_1('#skF_2','#skF_3','#skF_3'),A_44)
      | ~ m1_pre_topc('#skF_3',A_44)
      | ~ l1_pre_topc(A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_38])).

tff(c_56,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_193,plain,(
    ! [A_115] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(A_115),u1_pre_topc(A_115)))
      | ~ l1_pre_topc(A_115)
      | ~ v2_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_196,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_193])).

tff(c_198,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_196])).

tff(c_318,plain,(
    v2_pre_topc(k1_tsep_1('#skF_2','#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_198])).

tff(c_319,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k1_tsep_1('#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_56])).

tff(c_230,plain,(
    ! [B_123,A_124] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_123),u1_pre_topc(B_123)),A_124)
      | ~ m1_pre_topc(B_123,A_124)
      | ~ l1_pre_topc(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_24,plain,(
    ! [B_20,A_18] :
      ( l1_pre_topc(B_20)
      | ~ m1_pre_topc(B_20,A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_245,plain,(
    ! [B_127,A_128] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(B_127),u1_pre_topc(B_127)))
      | ~ m1_pre_topc(B_127,A_128)
      | ~ l1_pre_topc(A_128) ) ),
    inference(resolution,[status(thm)],[c_230,c_24])).

tff(c_249,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_245])).

tff(c_253,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_249])).

tff(c_316,plain,(
    l1_pre_topc(k1_tsep_1('#skF_2','#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_253])).

tff(c_770,plain,(
    ! [C_184,A_185] :
      ( m1_pre_topc(C_184,A_185)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(C_184),u1_pre_topc(C_184)),A_185)
      | ~ l1_pre_topc(C_184)
      | ~ v2_pre_topc(C_184)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_184),u1_pre_topc(C_184)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_184),u1_pre_topc(C_184)))
      | ~ l1_pre_topc(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_773,plain,(
    ! [A_185] :
      ( m1_pre_topc('#skF_2',A_185)
      | ~ m1_pre_topc(k1_tsep_1('#skF_2','#skF_3','#skF_3'),A_185)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_185) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_770])).

tff(c_785,plain,(
    ! [A_186] :
      ( m1_pre_topc('#skF_2',A_186)
      | ~ m1_pre_topc(k1_tsep_1('#skF_2','#skF_3','#skF_3'),A_186)
      | ~ l1_pre_topc(A_186) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_319,c_316,c_319,c_70,c_68,c_773])).

tff(c_794,plain,(
    ! [A_187] :
      ( m1_pre_topc('#skF_2',A_187)
      | ~ m1_pre_topc('#skF_3',A_187)
      | ~ l1_pre_topc(A_187) ) ),
    inference(resolution,[status(thm)],[c_323,c_785])).

tff(c_225,plain,(
    ! [B_121,A_122] :
      ( m1_subset_1(u1_struct_0(B_121),k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ m1_pre_topc(B_121,A_122)
      | ~ l1_pre_topc(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_229,plain,(
    ! [B_121,A_122] :
      ( r1_tarski(u1_struct_0(B_121),u1_struct_0(A_122))
      | ~ m1_pre_topc(B_121,A_122)
      | ~ l1_pre_topc(A_122) ) ),
    inference(resolution,[status(thm)],[c_225,c_8])).

tff(c_241,plain,(
    ! [B_125,A_126] :
      ( r1_tarski(u1_struct_0(B_125),u1_struct_0(A_126))
      | ~ m1_pre_topc(B_125,A_126)
      | ~ l1_pre_topc(A_126) ) ),
    inference(resolution,[status(thm)],[c_225,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_266,plain,(
    ! [B_130,A_131] :
      ( u1_struct_0(B_130) = u1_struct_0(A_131)
      | ~ r1_tarski(u1_struct_0(A_131),u1_struct_0(B_130))
      | ~ m1_pre_topc(B_130,A_131)
      | ~ l1_pre_topc(A_131) ) ),
    inference(resolution,[status(thm)],[c_241,c_2])).

tff(c_277,plain,(
    ! [B_132,A_133] :
      ( u1_struct_0(B_132) = u1_struct_0(A_133)
      | ~ m1_pre_topc(A_133,B_132)
      | ~ l1_pre_topc(B_132)
      | ~ m1_pre_topc(B_132,A_133)
      | ~ l1_pre_topc(A_133) ) ),
    inference(resolution,[status(thm)],[c_229,c_266])).

tff(c_283,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_277])).

tff(c_290,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_68,c_283])).

tff(c_291,plain,(
    ~ m1_pre_topc('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_290])).

tff(c_808,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_794,c_291])).

tff(c_830,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_808])).

tff(c_885,plain,(
    ! [B_190,C_191,A_192] :
      ( m1_pre_topc(B_190,C_191)
      | k1_tsep_1(A_192,B_190,C_191) != g1_pre_topc(u1_struct_0(C_191),u1_pre_topc(C_191))
      | ~ m1_pre_topc(C_191,A_192)
      | v2_struct_0(C_191)
      | ~ m1_pre_topc(B_190,A_192)
      | v2_struct_0(B_190)
      | ~ l1_pre_topc(A_192)
      | ~ v2_pre_topc(A_192)
      | v2_struct_0(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_889,plain,(
    ! [B_190,A_192] :
      ( m1_pre_topc(B_190,'#skF_3')
      | k1_tsep_1(A_192,B_190,'#skF_3') != k1_tsep_1('#skF_2','#skF_3','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_192)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_190,A_192)
      | v2_struct_0(B_190)
      | ~ l1_pre_topc(A_192)
      | ~ v2_pre_topc(A_192)
      | v2_struct_0(A_192) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_885])).

tff(c_988,plain,(
    ! [B_206,A_207] :
      ( m1_pre_topc(B_206,'#skF_3')
      | k1_tsep_1(A_207,B_206,'#skF_3') != k1_tsep_1('#skF_2','#skF_3','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_207)
      | ~ m1_pre_topc(B_206,A_207)
      | v2_struct_0(B_206)
      | ~ l1_pre_topc(A_207)
      | ~ v2_pre_topc(A_207)
      | v2_struct_0(A_207) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_889])).

tff(c_990,plain,(
    ! [B_206] :
      ( m1_pre_topc(B_206,'#skF_3')
      | k1_tsep_1('#skF_2',B_206,'#skF_3') != k1_tsep_1('#skF_2','#skF_3','#skF_3')
      | ~ m1_pre_topc(B_206,'#skF_2')
      | v2_struct_0(B_206)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_64,c_988])).

tff(c_993,plain,(
    ! [B_206] :
      ( m1_pre_topc(B_206,'#skF_3')
      | k1_tsep_1('#skF_2',B_206,'#skF_3') != k1_tsep_1('#skF_2','#skF_3','#skF_3')
      | ~ m1_pre_topc(B_206,'#skF_2')
      | v2_struct_0(B_206)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_990])).

tff(c_995,plain,(
    ! [B_208] :
      ( m1_pre_topc(B_208,'#skF_3')
      | k1_tsep_1('#skF_2',B_208,'#skF_3') != k1_tsep_1('#skF_2','#skF_3','#skF_3')
      | ~ m1_pre_topc(B_208,'#skF_2')
      | v2_struct_0(B_208) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_993])).

tff(c_1014,plain,
    ( m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_995])).

tff(c_1031,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_830,c_1014])).

tff(c_1032,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_290])).

tff(c_60,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_1062,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1032,c_60])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_1061,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1032,c_58])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1670,plain,(
    ! [F_246,C_245,D_248,B_247,A_249] :
      ( r1_funct_2(A_249,B_247,C_245,D_248,F_246,F_246)
      | ~ m1_subset_1(F_246,k1_zfmisc_1(k2_zfmisc_1(C_245,D_248)))
      | ~ v1_funct_2(F_246,C_245,D_248)
      | ~ m1_subset_1(F_246,k1_zfmisc_1(k2_zfmisc_1(A_249,B_247)))
      | ~ v1_funct_2(F_246,A_249,B_247)
      | ~ v1_funct_1(F_246)
      | v1_xboole_0(D_248)
      | v1_xboole_0(B_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1956,plain,(
    ! [B_281,A_282,D_283,A_280,C_279] :
      ( r1_funct_2(A_282,B_281,C_279,D_283,A_280,A_280)
      | ~ v1_funct_2(A_280,C_279,D_283)
      | ~ m1_subset_1(A_280,k1_zfmisc_1(k2_zfmisc_1(A_282,B_281)))
      | ~ v1_funct_2(A_280,A_282,B_281)
      | ~ v1_funct_1(A_280)
      | v1_xboole_0(D_283)
      | v1_xboole_0(B_281)
      | ~ r1_tarski(A_280,k2_zfmisc_1(C_279,D_283)) ) ),
    inference(resolution,[status(thm)],[c_10,c_1670])).

tff(c_1958,plain,(
    ! [C_279,D_283] :
      ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),C_279,D_283,'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',C_279,D_283)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(D_283)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(C_279,D_283)) ) ),
    inference(resolution,[status(thm)],[c_1061,c_1956])).

tff(c_1964,plain,(
    ! [C_279,D_283] :
      ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),C_279,D_283,'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',C_279,D_283)
      | v1_xboole_0(D_283)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(C_279,D_283)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1062,c_1958])).

tff(c_2235,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1964])).

tff(c_26,plain,(
    ! [A_21] :
      ( ~ v1_xboole_0(u1_struct_0(A_21))
      | ~ l1_struct_0(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2255,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2235,c_26])).

tff(c_2258,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2255])).

tff(c_2261,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_2258])).

tff(c_2265,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2261])).

tff(c_2267,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1964])).

tff(c_1672,plain,(
    ! [A_249,B_247] :
      ( r1_funct_2(A_249,B_247,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_249,B_247)))
      | ~ v1_funct_2('#skF_4',A_249,B_247)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_247) ) ),
    inference(resolution,[status(thm)],[c_1061,c_1670])).

tff(c_1678,plain,(
    ! [A_249,B_247] :
      ( r1_funct_2(A_249,B_247,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_249,B_247)))
      | ~ v1_funct_2('#skF_4',A_249,B_247)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_247) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1062,c_1672])).

tff(c_2276,plain,(
    ! [A_249,B_247] :
      ( r1_funct_2(A_249,B_247,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_249,B_247)))
      | ~ v1_funct_2('#skF_4',A_249,B_247)
      | v1_xboole_0(B_247) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2267,c_1678])).

tff(c_76,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_20,plain,(
    ! [A_13,B_14,C_15,D_16] :
      ( k2_partfun1(A_13,B_14,C_15,D_16) = k7_relat_1(C_15,D_16)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1174,plain,(
    ! [D_16] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',D_16) = k7_relat_1('#skF_4',D_16)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1061,c_20])).

tff(c_1189,plain,(
    ! [D_16] : k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',D_16) = k7_relat_1('#skF_4',D_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1174])).

tff(c_99,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_8])).

tff(c_1060,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1032,c_99])).

tff(c_1807,plain,(
    ! [A_268,B_269,C_270,D_271] :
      ( k2_partfun1(u1_struct_0(A_268),u1_struct_0(B_269),C_270,u1_struct_0(D_271)) = k2_tmap_1(A_268,B_269,C_270,D_271)
      | ~ m1_pre_topc(D_271,A_268)
      | ~ m1_subset_1(C_270,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_268),u1_struct_0(B_269))))
      | ~ v1_funct_2(C_270,u1_struct_0(A_268),u1_struct_0(B_269))
      | ~ v1_funct_1(C_270)
      | ~ l1_pre_topc(B_269)
      | ~ v2_pre_topc(B_269)
      | v2_struct_0(B_269)
      | ~ l1_pre_topc(A_268)
      | ~ v2_pre_topc(A_268)
      | v2_struct_0(A_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2548,plain,(
    ! [A_313,B_314,A_315,D_316] :
      ( k2_partfun1(u1_struct_0(A_313),u1_struct_0(B_314),A_315,u1_struct_0(D_316)) = k2_tmap_1(A_313,B_314,A_315,D_316)
      | ~ m1_pre_topc(D_316,A_313)
      | ~ v1_funct_2(A_315,u1_struct_0(A_313),u1_struct_0(B_314))
      | ~ v1_funct_1(A_315)
      | ~ l1_pre_topc(B_314)
      | ~ v2_pre_topc(B_314)
      | v2_struct_0(B_314)
      | ~ l1_pre_topc(A_313)
      | ~ v2_pre_topc(A_313)
      | v2_struct_0(A_313)
      | ~ r1_tarski(A_315,k2_zfmisc_1(u1_struct_0(A_313),u1_struct_0(B_314))) ) ),
    inference(resolution,[status(thm)],[c_10,c_1807])).

tff(c_2552,plain,(
    ! [B_314,A_315,D_316] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0(B_314),A_315,u1_struct_0(D_316)) = k2_tmap_1('#skF_2',B_314,A_315,D_316)
      | ~ m1_pre_topc(D_316,'#skF_2')
      | ~ v1_funct_2(A_315,u1_struct_0('#skF_2'),u1_struct_0(B_314))
      | ~ v1_funct_1(A_315)
      | ~ l1_pre_topc(B_314)
      | ~ v2_pre_topc(B_314)
      | v2_struct_0(B_314)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_315,k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_314))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1032,c_2548])).

tff(c_2563,plain,(
    ! [B_314,A_315,D_316] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_314),A_315,u1_struct_0(D_316)) = k2_tmap_1('#skF_2',B_314,A_315,D_316)
      | ~ m1_pre_topc(D_316,'#skF_2')
      | ~ v1_funct_2(A_315,u1_struct_0('#skF_3'),u1_struct_0(B_314))
      | ~ v1_funct_1(A_315)
      | ~ l1_pre_topc(B_314)
      | ~ v2_pre_topc(B_314)
      | v2_struct_0(B_314)
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_315,k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_314))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1032,c_1032,c_2552])).

tff(c_2637,plain,(
    ! [B_320,A_321,D_322] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_320),A_321,u1_struct_0(D_322)) = k2_tmap_1('#skF_2',B_320,A_321,D_322)
      | ~ m1_pre_topc(D_322,'#skF_2')
      | ~ v1_funct_2(A_321,u1_struct_0('#skF_3'),u1_struct_0(B_320))
      | ~ v1_funct_1(A_321)
      | ~ l1_pre_topc(B_320)
      | ~ v2_pre_topc(B_320)
      | v2_struct_0(B_320)
      | ~ r1_tarski(A_321,k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_320))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2563])).

tff(c_2639,plain,(
    ! [D_322] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_322)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_322)
      | ~ m1_pre_topc(D_322,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1060,c_2637])).

tff(c_2647,plain,(
    ! [D_322] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_322)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_322)
      | ~ m1_pre_topc(D_322,'#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_62,c_1062,c_1189,c_2639])).

tff(c_2653,plain,(
    ! [D_323] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_323)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_323)
      | ~ m1_pre_topc(D_323,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2647])).

tff(c_114,plain,(
    ! [C_89,A_90,B_91] :
      ( v1_relat_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_122,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_114])).

tff(c_136,plain,(
    ! [C_97,A_98,B_99] :
      ( v4_relat_1(C_97,A_98)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_144,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_136])).

tff(c_180,plain,(
    ! [B_113,A_114] :
      ( k7_relat_1(B_113,A_114) = B_113
      | ~ v4_relat_1(B_113,A_114)
      | ~ v1_relat_1(B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_186,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_144,c_180])).

tff(c_192,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_186])).

tff(c_1056,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1032,c_192])).

tff(c_2659,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2653,c_1056])).

tff(c_2671,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2659])).

tff(c_54,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_1057,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1032,c_54])).

tff(c_2677,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2671,c_1057])).

tff(c_2689,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_2276,c_2677])).

tff(c_2695,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1062,c_1061,c_2689])).

tff(c_2697,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2267,c_2695])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:26:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.10/1.91  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.23/1.92  
% 5.23/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.23/1.92  %$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.23/1.92  
% 5.23/1.92  %Foreground sorts:
% 5.23/1.92  
% 5.23/1.92  
% 5.23/1.92  %Background operators:
% 5.23/1.92  
% 5.23/1.92  
% 5.23/1.92  %Foreground operators:
% 5.23/1.92  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.23/1.92  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 5.23/1.92  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 5.23/1.92  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.23/1.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.23/1.92  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 5.23/1.92  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.23/1.92  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.23/1.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.23/1.92  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.23/1.92  tff('#skF_2', type, '#skF_2': $i).
% 5.23/1.92  tff('#skF_3', type, '#skF_3': $i).
% 5.23/1.92  tff('#skF_1', type, '#skF_1': $i).
% 5.23/1.92  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 5.23/1.92  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.23/1.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.23/1.92  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.23/1.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.23/1.92  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.23/1.92  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.23/1.92  tff('#skF_4', type, '#skF_4': $i).
% 5.23/1.92  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 5.23/1.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.23/1.92  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.23/1.92  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 5.23/1.92  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.23/1.92  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.23/1.92  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 5.23/1.92  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.23/1.92  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.23/1.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.23/1.92  
% 5.29/1.95  tff(f_238, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_tmap_1)).
% 5.29/1.95  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.29/1.95  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.29/1.95  tff(f_205, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (k1_tsep_1(A, B, B) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_tmap_1)).
% 5.29/1.95  tff(f_142, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tmap_1)).
% 5.29/1.95  tff(f_84, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_pre_topc)).
% 5.29/1.95  tff(f_160, axiom, (![A]: (l1_pre_topc(A) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((B = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) => (m1_pre_topc(B, A) <=> m1_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_tmap_1)).
% 5.29/1.95  tff(f_167, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 5.29/1.95  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.29/1.95  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.29/1.95  tff(f_190, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) <=> (k1_tsep_1(A, B, C) = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tsep_1)).
% 5.29/1.95  tff(f_106, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 5.29/1.95  tff(f_76, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 5.29/1.95  tff(f_57, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 5.29/1.95  tff(f_133, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 5.29/1.95  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.29/1.95  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.29/1.95  tff(f_41, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 5.29/1.95  tff(c_74, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_238])).
% 5.29/1.95  tff(c_22, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.29/1.95  tff(c_78, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_238])).
% 5.29/1.95  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_238])).
% 5.29/1.95  tff(c_66, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_238])).
% 5.29/1.95  tff(c_68, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_238])).
% 5.29/1.95  tff(c_64, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_238])).
% 5.29/1.95  tff(c_82, plain, (![B_80, A_81]: (l1_pre_topc(B_80) | ~m1_pre_topc(B_80, A_81) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.29/1.95  tff(c_85, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_64, c_82])).
% 5.29/1.95  tff(c_88, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_85])).
% 5.29/1.95  tff(c_72, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_238])).
% 5.29/1.95  tff(c_70, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_238])).
% 5.29/1.95  tff(c_302, plain, (![A_138, B_139]: (k1_tsep_1(A_138, B_139, B_139)=g1_pre_topc(u1_struct_0(B_139), u1_pre_topc(B_139)) | ~m1_pre_topc(B_139, A_138) | v2_struct_0(B_139) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_205])).
% 5.29/1.95  tff(c_308, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k1_tsep_1('#skF_2', '#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_64, c_302])).
% 5.29/1.95  tff(c_313, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k1_tsep_1('#skF_2', '#skF_3', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_308])).
% 5.29/1.95  tff(c_314, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k1_tsep_1('#skF_2', '#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_313])).
% 5.29/1.95  tff(c_38, plain, (![B_46, A_44]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_46), u1_pre_topc(B_46)), A_44) | ~m1_pre_topc(B_46, A_44) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_142])).
% 5.29/1.95  tff(c_323, plain, (![A_44]: (m1_pre_topc(k1_tsep_1('#skF_2', '#skF_3', '#skF_3'), A_44) | ~m1_pre_topc('#skF_3', A_44) | ~l1_pre_topc(A_44))), inference(superposition, [status(thm), theory('equality')], [c_314, c_38])).
% 5.29/1.95  tff(c_56, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_238])).
% 5.29/1.95  tff(c_193, plain, (![A_115]: (v2_pre_topc(g1_pre_topc(u1_struct_0(A_115), u1_pre_topc(A_115))) | ~l1_pre_topc(A_115) | ~v2_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.29/1.95  tff(c_196, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_56, c_193])).
% 5.29/1.95  tff(c_198, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_196])).
% 5.29/1.95  tff(c_318, plain, (v2_pre_topc(k1_tsep_1('#skF_2', '#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_314, c_198])).
% 5.29/1.95  tff(c_319, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k1_tsep_1('#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_314, c_56])).
% 5.29/1.95  tff(c_230, plain, (![B_123, A_124]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_123), u1_pre_topc(B_123)), A_124) | ~m1_pre_topc(B_123, A_124) | ~l1_pre_topc(A_124))), inference(cnfTransformation, [status(thm)], [f_142])).
% 5.29/1.95  tff(c_24, plain, (![B_20, A_18]: (l1_pre_topc(B_20) | ~m1_pre_topc(B_20, A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.29/1.95  tff(c_245, plain, (![B_127, A_128]: (l1_pre_topc(g1_pre_topc(u1_struct_0(B_127), u1_pre_topc(B_127))) | ~m1_pre_topc(B_127, A_128) | ~l1_pre_topc(A_128))), inference(resolution, [status(thm)], [c_230, c_24])).
% 5.29/1.95  tff(c_249, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_64, c_245])).
% 5.29/1.95  tff(c_253, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_249])).
% 5.29/1.95  tff(c_316, plain, (l1_pre_topc(k1_tsep_1('#skF_2', '#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_314, c_253])).
% 5.29/1.95  tff(c_770, plain, (![C_184, A_185]: (m1_pre_topc(C_184, A_185) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_184), u1_pre_topc(C_184)), A_185) | ~l1_pre_topc(C_184) | ~v2_pre_topc(C_184) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_184), u1_pre_topc(C_184))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_184), u1_pre_topc(C_184))) | ~l1_pre_topc(A_185))), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.29/1.95  tff(c_773, plain, (![A_185]: (m1_pre_topc('#skF_2', A_185) | ~m1_pre_topc(k1_tsep_1('#skF_2', '#skF_3', '#skF_3'), A_185) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_185))), inference(superposition, [status(thm), theory('equality')], [c_319, c_770])).
% 5.29/1.95  tff(c_785, plain, (![A_186]: (m1_pre_topc('#skF_2', A_186) | ~m1_pre_topc(k1_tsep_1('#skF_2', '#skF_3', '#skF_3'), A_186) | ~l1_pre_topc(A_186))), inference(demodulation, [status(thm), theory('equality')], [c_318, c_319, c_316, c_319, c_70, c_68, c_773])).
% 5.29/1.95  tff(c_794, plain, (![A_187]: (m1_pre_topc('#skF_2', A_187) | ~m1_pre_topc('#skF_3', A_187) | ~l1_pre_topc(A_187))), inference(resolution, [status(thm)], [c_323, c_785])).
% 5.29/1.95  tff(c_225, plain, (![B_121, A_122]: (m1_subset_1(u1_struct_0(B_121), k1_zfmisc_1(u1_struct_0(A_122))) | ~m1_pre_topc(B_121, A_122) | ~l1_pre_topc(A_122))), inference(cnfTransformation, [status(thm)], [f_167])).
% 5.29/1.95  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.29/1.95  tff(c_229, plain, (![B_121, A_122]: (r1_tarski(u1_struct_0(B_121), u1_struct_0(A_122)) | ~m1_pre_topc(B_121, A_122) | ~l1_pre_topc(A_122))), inference(resolution, [status(thm)], [c_225, c_8])).
% 5.29/1.95  tff(c_241, plain, (![B_125, A_126]: (r1_tarski(u1_struct_0(B_125), u1_struct_0(A_126)) | ~m1_pre_topc(B_125, A_126) | ~l1_pre_topc(A_126))), inference(resolution, [status(thm)], [c_225, c_8])).
% 5.29/1.95  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.29/1.95  tff(c_266, plain, (![B_130, A_131]: (u1_struct_0(B_130)=u1_struct_0(A_131) | ~r1_tarski(u1_struct_0(A_131), u1_struct_0(B_130)) | ~m1_pre_topc(B_130, A_131) | ~l1_pre_topc(A_131))), inference(resolution, [status(thm)], [c_241, c_2])).
% 5.29/1.95  tff(c_277, plain, (![B_132, A_133]: (u1_struct_0(B_132)=u1_struct_0(A_133) | ~m1_pre_topc(A_133, B_132) | ~l1_pre_topc(B_132) | ~m1_pre_topc(B_132, A_133) | ~l1_pre_topc(A_133))), inference(resolution, [status(thm)], [c_229, c_266])).
% 5.29/1.95  tff(c_283, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_64, c_277])).
% 5.29/1.95  tff(c_290, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_68, c_283])).
% 5.29/1.95  tff(c_291, plain, (~m1_pre_topc('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_290])).
% 5.29/1.95  tff(c_808, plain, (~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_794, c_291])).
% 5.29/1.95  tff(c_830, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_808])).
% 5.29/1.95  tff(c_885, plain, (![B_190, C_191, A_192]: (m1_pre_topc(B_190, C_191) | k1_tsep_1(A_192, B_190, C_191)!=g1_pre_topc(u1_struct_0(C_191), u1_pre_topc(C_191)) | ~m1_pre_topc(C_191, A_192) | v2_struct_0(C_191) | ~m1_pre_topc(B_190, A_192) | v2_struct_0(B_190) | ~l1_pre_topc(A_192) | ~v2_pre_topc(A_192) | v2_struct_0(A_192))), inference(cnfTransformation, [status(thm)], [f_190])).
% 5.29/1.95  tff(c_889, plain, (![B_190, A_192]: (m1_pre_topc(B_190, '#skF_3') | k1_tsep_1(A_192, B_190, '#skF_3')!=k1_tsep_1('#skF_2', '#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', A_192) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_190, A_192) | v2_struct_0(B_190) | ~l1_pre_topc(A_192) | ~v2_pre_topc(A_192) | v2_struct_0(A_192))), inference(superposition, [status(thm), theory('equality')], [c_314, c_885])).
% 5.29/1.95  tff(c_988, plain, (![B_206, A_207]: (m1_pre_topc(B_206, '#skF_3') | k1_tsep_1(A_207, B_206, '#skF_3')!=k1_tsep_1('#skF_2', '#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', A_207) | ~m1_pre_topc(B_206, A_207) | v2_struct_0(B_206) | ~l1_pre_topc(A_207) | ~v2_pre_topc(A_207) | v2_struct_0(A_207))), inference(negUnitSimplification, [status(thm)], [c_66, c_889])).
% 5.29/1.95  tff(c_990, plain, (![B_206]: (m1_pre_topc(B_206, '#skF_3') | k1_tsep_1('#skF_2', B_206, '#skF_3')!=k1_tsep_1('#skF_2', '#skF_3', '#skF_3') | ~m1_pre_topc(B_206, '#skF_2') | v2_struct_0(B_206) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_64, c_988])).
% 5.29/1.95  tff(c_993, plain, (![B_206]: (m1_pre_topc(B_206, '#skF_3') | k1_tsep_1('#skF_2', B_206, '#skF_3')!=k1_tsep_1('#skF_2', '#skF_3', '#skF_3') | ~m1_pre_topc(B_206, '#skF_2') | v2_struct_0(B_206) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_990])).
% 5.29/1.95  tff(c_995, plain, (![B_208]: (m1_pre_topc(B_208, '#skF_3') | k1_tsep_1('#skF_2', B_208, '#skF_3')!=k1_tsep_1('#skF_2', '#skF_3', '#skF_3') | ~m1_pre_topc(B_208, '#skF_2') | v2_struct_0(B_208))), inference(negUnitSimplification, [status(thm)], [c_72, c_993])).
% 5.29/1.95  tff(c_1014, plain, (m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_995])).
% 5.29/1.95  tff(c_1031, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_830, c_1014])).
% 5.29/1.95  tff(c_1032, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_290])).
% 5.29/1.95  tff(c_60, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_238])).
% 5.29/1.95  tff(c_1062, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1032, c_60])).
% 5.29/1.95  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_238])).
% 5.29/1.95  tff(c_1061, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_1032, c_58])).
% 5.29/1.95  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.29/1.95  tff(c_1670, plain, (![F_246, C_245, D_248, B_247, A_249]: (r1_funct_2(A_249, B_247, C_245, D_248, F_246, F_246) | ~m1_subset_1(F_246, k1_zfmisc_1(k2_zfmisc_1(C_245, D_248))) | ~v1_funct_2(F_246, C_245, D_248) | ~m1_subset_1(F_246, k1_zfmisc_1(k2_zfmisc_1(A_249, B_247))) | ~v1_funct_2(F_246, A_249, B_247) | ~v1_funct_1(F_246) | v1_xboole_0(D_248) | v1_xboole_0(B_247))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.29/1.95  tff(c_1956, plain, (![B_281, A_282, D_283, A_280, C_279]: (r1_funct_2(A_282, B_281, C_279, D_283, A_280, A_280) | ~v1_funct_2(A_280, C_279, D_283) | ~m1_subset_1(A_280, k1_zfmisc_1(k2_zfmisc_1(A_282, B_281))) | ~v1_funct_2(A_280, A_282, B_281) | ~v1_funct_1(A_280) | v1_xboole_0(D_283) | v1_xboole_0(B_281) | ~r1_tarski(A_280, k2_zfmisc_1(C_279, D_283)))), inference(resolution, [status(thm)], [c_10, c_1670])).
% 5.29/1.95  tff(c_1958, plain, (![C_279, D_283]: (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), C_279, D_283, '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', C_279, D_283) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(D_283) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski('#skF_4', k2_zfmisc_1(C_279, D_283)))), inference(resolution, [status(thm)], [c_1061, c_1956])).
% 5.29/1.95  tff(c_1964, plain, (![C_279, D_283]: (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), C_279, D_283, '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', C_279, D_283) | v1_xboole_0(D_283) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski('#skF_4', k2_zfmisc_1(C_279, D_283)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1062, c_1958])).
% 5.29/1.95  tff(c_2235, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_1964])).
% 5.29/1.95  tff(c_26, plain, (![A_21]: (~v1_xboole_0(u1_struct_0(A_21)) | ~l1_struct_0(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.29/1.95  tff(c_2255, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2235, c_26])).
% 5.29/1.95  tff(c_2258, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_78, c_2255])).
% 5.29/1.95  tff(c_2261, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_2258])).
% 5.29/1.95  tff(c_2265, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_2261])).
% 5.29/1.95  tff(c_2267, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_1964])).
% 5.29/1.95  tff(c_1672, plain, (![A_249, B_247]: (r1_funct_2(A_249, B_247, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_249, B_247))) | ~v1_funct_2('#skF_4', A_249, B_247) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_247))), inference(resolution, [status(thm)], [c_1061, c_1670])).
% 5.29/1.95  tff(c_1678, plain, (![A_249, B_247]: (r1_funct_2(A_249, B_247, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_249, B_247))) | ~v1_funct_2('#skF_4', A_249, B_247) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_247))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1062, c_1672])).
% 5.29/1.95  tff(c_2276, plain, (![A_249, B_247]: (r1_funct_2(A_249, B_247, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_249, B_247))) | ~v1_funct_2('#skF_4', A_249, B_247) | v1_xboole_0(B_247))), inference(negUnitSimplification, [status(thm)], [c_2267, c_1678])).
% 5.29/1.95  tff(c_76, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_238])).
% 5.29/1.95  tff(c_20, plain, (![A_13, B_14, C_15, D_16]: (k2_partfun1(A_13, B_14, C_15, D_16)=k7_relat_1(C_15, D_16) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_1(C_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.29/1.95  tff(c_1174, plain, (![D_16]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', D_16)=k7_relat_1('#skF_4', D_16) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_1061, c_20])).
% 5.29/1.95  tff(c_1189, plain, (![D_16]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', D_16)=k7_relat_1('#skF_4', D_16))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1174])).
% 5.29/1.95  tff(c_99, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_58, c_8])).
% 5.29/1.95  tff(c_1060, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1032, c_99])).
% 5.29/1.95  tff(c_1807, plain, (![A_268, B_269, C_270, D_271]: (k2_partfun1(u1_struct_0(A_268), u1_struct_0(B_269), C_270, u1_struct_0(D_271))=k2_tmap_1(A_268, B_269, C_270, D_271) | ~m1_pre_topc(D_271, A_268) | ~m1_subset_1(C_270, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_268), u1_struct_0(B_269)))) | ~v1_funct_2(C_270, u1_struct_0(A_268), u1_struct_0(B_269)) | ~v1_funct_1(C_270) | ~l1_pre_topc(B_269) | ~v2_pre_topc(B_269) | v2_struct_0(B_269) | ~l1_pre_topc(A_268) | ~v2_pre_topc(A_268) | v2_struct_0(A_268))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.29/1.95  tff(c_2548, plain, (![A_313, B_314, A_315, D_316]: (k2_partfun1(u1_struct_0(A_313), u1_struct_0(B_314), A_315, u1_struct_0(D_316))=k2_tmap_1(A_313, B_314, A_315, D_316) | ~m1_pre_topc(D_316, A_313) | ~v1_funct_2(A_315, u1_struct_0(A_313), u1_struct_0(B_314)) | ~v1_funct_1(A_315) | ~l1_pre_topc(B_314) | ~v2_pre_topc(B_314) | v2_struct_0(B_314) | ~l1_pre_topc(A_313) | ~v2_pre_topc(A_313) | v2_struct_0(A_313) | ~r1_tarski(A_315, k2_zfmisc_1(u1_struct_0(A_313), u1_struct_0(B_314))))), inference(resolution, [status(thm)], [c_10, c_1807])).
% 5.29/1.95  tff(c_2552, plain, (![B_314, A_315, D_316]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0(B_314), A_315, u1_struct_0(D_316))=k2_tmap_1('#skF_2', B_314, A_315, D_316) | ~m1_pre_topc(D_316, '#skF_2') | ~v1_funct_2(A_315, u1_struct_0('#skF_2'), u1_struct_0(B_314)) | ~v1_funct_1(A_315) | ~l1_pre_topc(B_314) | ~v2_pre_topc(B_314) | v2_struct_0(B_314) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(A_315, k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_314))))), inference(superposition, [status(thm), theory('equality')], [c_1032, c_2548])).
% 5.29/1.95  tff(c_2563, plain, (![B_314, A_315, D_316]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_314), A_315, u1_struct_0(D_316))=k2_tmap_1('#skF_2', B_314, A_315, D_316) | ~m1_pre_topc(D_316, '#skF_2') | ~v1_funct_2(A_315, u1_struct_0('#skF_3'), u1_struct_0(B_314)) | ~v1_funct_1(A_315) | ~l1_pre_topc(B_314) | ~v2_pre_topc(B_314) | v2_struct_0(B_314) | v2_struct_0('#skF_2') | ~r1_tarski(A_315, k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_314))))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1032, c_1032, c_2552])).
% 5.29/1.95  tff(c_2637, plain, (![B_320, A_321, D_322]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_320), A_321, u1_struct_0(D_322))=k2_tmap_1('#skF_2', B_320, A_321, D_322) | ~m1_pre_topc(D_322, '#skF_2') | ~v1_funct_2(A_321, u1_struct_0('#skF_3'), u1_struct_0(B_320)) | ~v1_funct_1(A_321) | ~l1_pre_topc(B_320) | ~v2_pre_topc(B_320) | v2_struct_0(B_320) | ~r1_tarski(A_321, k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_320))))), inference(negUnitSimplification, [status(thm)], [c_72, c_2563])).
% 5.29/1.95  tff(c_2639, plain, (![D_322]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_322))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_322) | ~m1_pre_topc(D_322, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_1060, c_2637])).
% 5.29/1.95  tff(c_2647, plain, (![D_322]: (k7_relat_1('#skF_4', u1_struct_0(D_322))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_322) | ~m1_pre_topc(D_322, '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_62, c_1062, c_1189, c_2639])).
% 5.29/1.95  tff(c_2653, plain, (![D_323]: (k7_relat_1('#skF_4', u1_struct_0(D_323))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_323) | ~m1_pre_topc(D_323, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_78, c_2647])).
% 5.29/1.95  tff(c_114, plain, (![C_89, A_90, B_91]: (v1_relat_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.29/1.95  tff(c_122, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_114])).
% 5.29/1.95  tff(c_136, plain, (![C_97, A_98, B_99]: (v4_relat_1(C_97, A_98) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.29/1.95  tff(c_144, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_58, c_136])).
% 5.29/1.95  tff(c_180, plain, (![B_113, A_114]: (k7_relat_1(B_113, A_114)=B_113 | ~v4_relat_1(B_113, A_114) | ~v1_relat_1(B_113))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.29/1.95  tff(c_186, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_144, c_180])).
% 5.29/1.95  tff(c_192, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_122, c_186])).
% 5.29/1.95  tff(c_1056, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1032, c_192])).
% 5.29/1.95  tff(c_2659, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2653, c_1056])).
% 5.29/1.95  tff(c_2671, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2659])).
% 5.29/1.95  tff(c_54, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_238])).
% 5.29/1.95  tff(c_1057, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1032, c_54])).
% 5.29/1.95  tff(c_2677, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2671, c_1057])).
% 5.29/1.95  tff(c_2689, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_2276, c_2677])).
% 5.29/1.95  tff(c_2695, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1062, c_1061, c_2689])).
% 5.29/1.95  tff(c_2697, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2267, c_2695])).
% 5.29/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.29/1.95  
% 5.29/1.95  Inference rules
% 5.29/1.95  ----------------------
% 5.29/1.95  #Ref     : 0
% 5.29/1.95  #Sup     : 518
% 5.29/1.95  #Fact    : 0
% 5.29/1.95  #Define  : 0
% 5.29/1.95  #Split   : 17
% 5.29/1.95  #Chain   : 0
% 5.29/1.95  #Close   : 0
% 5.29/1.95  
% 5.29/1.95  Ordering : KBO
% 5.29/1.95  
% 5.29/1.95  Simplification rules
% 5.29/1.95  ----------------------
% 5.29/1.95  #Subsume      : 119
% 5.29/1.95  #Demod        : 827
% 5.29/1.95  #Tautology    : 178
% 5.29/1.95  #SimpNegUnit  : 81
% 5.29/1.95  #BackRed      : 20
% 5.29/1.95  
% 5.29/1.95  #Partial instantiations: 0
% 5.29/1.95  #Strategies tried      : 1
% 5.29/1.95  
% 5.29/1.95  Timing (in seconds)
% 5.29/1.95  ----------------------
% 5.29/1.95  Preprocessing        : 0.38
% 5.29/1.95  Parsing              : 0.20
% 5.29/1.95  CNF conversion       : 0.03
% 5.29/1.95  Main loop            : 0.79
% 5.29/1.95  Inferencing          : 0.25
% 5.29/1.95  Reduction            : 0.27
% 5.29/1.95  Demodulation         : 0.20
% 5.29/1.95  BG Simplification    : 0.04
% 5.29/1.95  Subsumption          : 0.18
% 5.29/1.95  Abstraction          : 0.04
% 5.29/1.95  MUC search           : 0.00
% 5.29/1.95  Cooper               : 0.00
% 5.29/1.95  Total                : 1.21
% 5.29/1.95  Index Insertion      : 0.00
% 5.29/1.95  Index Deletion       : 0.00
% 5.29/1.95  Index Matching       : 0.00
% 5.29/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
