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
% DateTime   : Thu Dec  3 10:26:57 EST 2020

% Result     : Theorem 10.37s
% Output     : CNFRefutation 10.43s
% Verified   : 
% Statistics : Number of formulae       :  154 (5012 expanded)
%              Number of leaves         :   44 (1738 expanded)
%              Depth                    :   28
%              Number of atoms          :  396 (22257 expanded)
%              Number of equality atoms :   27 (1447 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_218,negated_conjecture,(
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

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_160,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

tff(f_178,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tmap_1)).

tff(f_185,axiom,(
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

tff(f_124,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r1_funct_2)).

tff(f_80,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_151,axiom,(
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

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(A,C)
       => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_43,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(c_72,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_22,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_66,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_62,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_87,plain,(
    ! [B_81,A_82] :
      ( l1_pre_topc(B_81)
      | ~ m1_pre_topc(B_81,A_82)
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_90,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_87])).

tff(c_93,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_90])).

tff(c_219,plain,(
    ! [A_109,B_110] :
      ( m1_pre_topc(A_109,g1_pre_topc(u1_struct_0(B_110),u1_pre_topc(B_110)))
      | ~ m1_pre_topc(A_109,B_110)
      | ~ l1_pre_topc(B_110)
      | ~ l1_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_54,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_157,plain,(
    ! [B_101,A_102] :
      ( m1_pre_topc(B_101,A_102)
      | ~ m1_pre_topc(B_101,g1_pre_topc(u1_struct_0(A_102),u1_pre_topc(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_160,plain,(
    ! [B_101] :
      ( m1_pre_topc(B_101,'#skF_2')
      | ~ m1_pre_topc(B_101,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_157])).

tff(c_162,plain,(
    ! [B_101] :
      ( m1_pre_topc(B_101,'#skF_2')
      | ~ m1_pre_topc(B_101,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_160])).

tff(c_225,plain,(
    ! [A_109] :
      ( m1_pre_topc(A_109,'#skF_2')
      | ~ m1_pre_topc(A_109,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_109) ) ),
    inference(resolution,[status(thm)],[c_219,c_162])).

tff(c_240,plain,(
    ! [A_109] :
      ( m1_pre_topc(A_109,'#skF_2')
      | ~ m1_pre_topc(A_109,'#skF_3')
      | ~ l1_pre_topc(A_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_225])).

tff(c_164,plain,(
    ! [B_104,A_105] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_104),u1_pre_topc(B_104)),A_105)
      | ~ m1_pre_topc(B_104,A_105)
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_24,plain,(
    ! [B_20,A_18] :
      ( l1_pre_topc(B_20)
      | ~ m1_pre_topc(B_20,A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_185,plain,(
    ! [B_106,A_107] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(B_106),u1_pre_topc(B_106)))
      | ~ m1_pre_topc(B_106,A_107)
      | ~ l1_pre_topc(A_107) ) ),
    inference(resolution,[status(thm)],[c_164,c_24])).

tff(c_189,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_185])).

tff(c_193,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_189])).

tff(c_180,plain,(
    ! [A_105] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),A_105)
      | ~ m1_pre_topc('#skF_2',A_105)
      | ~ l1_pre_topc(A_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_164])).

tff(c_236,plain,(
    ! [A_109] :
      ( m1_pre_topc(A_109,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_109,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_219])).

tff(c_286,plain,(
    ! [A_119] :
      ( m1_pre_topc(A_119,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_119,'#skF_2')
      | ~ l1_pre_topc(A_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_236])).

tff(c_32,plain,(
    ! [B_25,A_23] :
      ( m1_pre_topc(B_25,A_23)
      | ~ m1_pre_topc(B_25,g1_pre_topc(u1_struct_0(A_23),u1_pre_topc(A_23)))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_294,plain,(
    ! [A_119] :
      ( m1_pre_topc(A_119,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_pre_topc(A_119,'#skF_2')
      | ~ l1_pre_topc(A_119) ) ),
    inference(resolution,[status(thm)],[c_286,c_32])).

tff(c_313,plain,(
    ! [A_120] :
      ( m1_pre_topc(A_120,'#skF_3')
      | ~ m1_pre_topc(A_120,'#skF_2')
      | ~ l1_pre_topc(A_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_294])).

tff(c_320,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_3')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_180,c_313])).

tff(c_331,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_193,c_320])).

tff(c_354,plain,(
    ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_331])).

tff(c_357,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_240,c_354])).

tff(c_360,plain,(
    ~ m1_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_357])).

tff(c_42,plain,(
    ! [B_52,A_50] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_52),u1_pre_topc(B_52)),A_50)
      | ~ m1_pre_topc(B_52,A_50)
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_324,plain,(
    ! [B_52] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_52),u1_pre_topc(B_52)),'#skF_3')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(B_52),u1_pre_topc(B_52)))
      | ~ m1_pre_topc(B_52,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_42,c_313])).

tff(c_334,plain,(
    ! [B_52] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_52),u1_pre_topc(B_52)),'#skF_3')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(B_52),u1_pre_topc(B_52)))
      | ~ m1_pre_topc(B_52,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_324])).

tff(c_68,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_112,plain,(
    ! [A_85] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(A_85),u1_pre_topc(A_85)))
      | ~ l1_pre_topc(A_85)
      | ~ v2_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_115,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_112])).

tff(c_117,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_115])).

tff(c_791,plain,(
    ! [C_165,A_166] :
      ( m1_pre_topc(C_165,A_166)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(C_165),u1_pre_topc(C_165)),A_166)
      | ~ l1_pre_topc(C_165)
      | ~ v2_pre_topc(C_165)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_165),u1_pre_topc(C_165)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_165),u1_pre_topc(C_165)))
      | ~ l1_pre_topc(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_818,plain,(
    ! [A_166] :
      ( m1_pre_topc('#skF_2',A_166)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),A_166)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_166) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_791])).

tff(c_992,plain,(
    ! [A_167] :
      ( m1_pre_topc('#skF_2',A_167)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),A_167)
      | ~ l1_pre_topc(A_167) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_54,c_193,c_54,c_68,c_66,c_818])).

tff(c_1004,plain,
    ( m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_334,c_992])).

tff(c_1031,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_193,c_93,c_1004])).

tff(c_1033,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_360,c_1031])).

tff(c_1035,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitRight,[status(thm)],[c_331])).

tff(c_306,plain,(
    ! [A_119] :
      ( m1_pre_topc(A_119,'#skF_3')
      | ~ m1_pre_topc(A_119,'#skF_2')
      | ~ l1_pre_topc(A_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_294])).

tff(c_1038,plain,
    ( m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1035,c_306])).

tff(c_1048,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1038])).

tff(c_124,plain,(
    ! [B_87,A_88] :
      ( m1_subset_1(u1_struct_0(B_87),k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ m1_pre_topc(B_87,A_88)
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_128,plain,(
    ! [B_87,A_88] :
      ( r1_tarski(u1_struct_0(B_87),u1_struct_0(A_88))
      | ~ m1_pre_topc(B_87,A_88)
      | ~ l1_pre_topc(A_88) ) ),
    inference(resolution,[status(thm)],[c_124,c_8])).

tff(c_129,plain,(
    ! [B_89,A_90] :
      ( r1_tarski(u1_struct_0(B_89),u1_struct_0(A_90))
      | ~ m1_pre_topc(B_89,A_90)
      | ~ l1_pre_topc(A_90) ) ),
    inference(resolution,[status(thm)],[c_124,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1124,plain,(
    ! [B_181,A_182] :
      ( u1_struct_0(B_181) = u1_struct_0(A_182)
      | ~ r1_tarski(u1_struct_0(A_182),u1_struct_0(B_181))
      | ~ m1_pre_topc(B_181,A_182)
      | ~ l1_pre_topc(A_182) ) ),
    inference(resolution,[status(thm)],[c_129,c_2])).

tff(c_1235,plain,(
    ! [B_188,A_189] :
      ( u1_struct_0(B_188) = u1_struct_0(A_189)
      | ~ m1_pre_topc(A_189,B_188)
      | ~ l1_pre_topc(B_188)
      | ~ m1_pre_topc(B_188,A_189)
      | ~ l1_pre_topc(A_189) ) ),
    inference(resolution,[status(thm)],[c_128,c_1124])).

tff(c_1259,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_1235])).

tff(c_1293,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_1048,c_66,c_1259])).

tff(c_58,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_1301,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1293,c_58])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_1300,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1293,c_56])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1578,plain,(
    ! [E_201,C_202,B_198,D_197,A_199,F_200] :
      ( r1_funct_2(A_199,B_198,C_202,D_197,E_201,E_201)
      | ~ m1_subset_1(F_200,k1_zfmisc_1(k2_zfmisc_1(C_202,D_197)))
      | ~ v1_funct_2(F_200,C_202,D_197)
      | ~ v1_funct_1(F_200)
      | ~ m1_subset_1(E_201,k1_zfmisc_1(k2_zfmisc_1(A_199,B_198)))
      | ~ v1_funct_2(E_201,A_199,B_198)
      | ~ v1_funct_1(E_201)
      | v1_xboole_0(D_197)
      | v1_xboole_0(B_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2751,plain,(
    ! [B_262,A_265,E_260,C_261,A_264,D_263] :
      ( r1_funct_2(A_264,B_262,C_261,D_263,E_260,E_260)
      | ~ v1_funct_2(A_265,C_261,D_263)
      | ~ v1_funct_1(A_265)
      | ~ m1_subset_1(E_260,k1_zfmisc_1(k2_zfmisc_1(A_264,B_262)))
      | ~ v1_funct_2(E_260,A_264,B_262)
      | ~ v1_funct_1(E_260)
      | v1_xboole_0(D_263)
      | v1_xboole_0(B_262)
      | ~ r1_tarski(A_265,k2_zfmisc_1(C_261,D_263)) ) ),
    inference(resolution,[status(thm)],[c_10,c_1578])).

tff(c_2753,plain,(
    ! [C_261,D_263,A_265] :
      ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),C_261,D_263,'#skF_4','#skF_4')
      | ~ v1_funct_2(A_265,C_261,D_263)
      | ~ v1_funct_1(A_265)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(D_263)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_265,k2_zfmisc_1(C_261,D_263)) ) ),
    inference(resolution,[status(thm)],[c_1300,c_2751])).

tff(c_2761,plain,(
    ! [C_261,D_263,A_265] :
      ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),C_261,D_263,'#skF_4','#skF_4')
      | ~ v1_funct_2(A_265,C_261,D_263)
      | ~ v1_funct_1(A_265)
      | v1_xboole_0(D_263)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_265,k2_zfmisc_1(C_261,D_263)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1301,c_2753])).

tff(c_13213,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_2761])).

tff(c_26,plain,(
    ! [A_21] :
      ( ~ v1_xboole_0(u1_struct_0(A_21))
      | ~ l1_struct_0(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_13626,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_13213,c_26])).

tff(c_13629,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_13626])).

tff(c_13632,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_13629])).

tff(c_13636,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_13632])).

tff(c_13638,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_2761])).

tff(c_74,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_1634,plain,(
    ! [A_205,B_206,C_207,D_208] :
      ( k2_partfun1(u1_struct_0(A_205),u1_struct_0(B_206),C_207,u1_struct_0(D_208)) = k2_tmap_1(A_205,B_206,C_207,D_208)
      | ~ m1_pre_topc(D_208,A_205)
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_205),u1_struct_0(B_206))))
      | ~ v1_funct_2(C_207,u1_struct_0(A_205),u1_struct_0(B_206))
      | ~ v1_funct_1(C_207)
      | ~ l1_pre_topc(B_206)
      | ~ v2_pre_topc(B_206)
      | v2_struct_0(B_206)
      | ~ l1_pre_topc(A_205)
      | ~ v2_pre_topc(A_205)
      | v2_struct_0(A_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_1642,plain,(
    ! [B_206,C_207,D_208] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0(B_206),C_207,u1_struct_0(D_208)) = k2_tmap_1('#skF_2',B_206,C_207,D_208)
      | ~ m1_pre_topc(D_208,'#skF_2')
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_206))))
      | ~ v1_funct_2(C_207,u1_struct_0('#skF_2'),u1_struct_0(B_206))
      | ~ v1_funct_1(C_207)
      | ~ l1_pre_topc(B_206)
      | ~ v2_pre_topc(B_206)
      | v2_struct_0(B_206)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1293,c_1634])).

tff(c_1660,plain,(
    ! [B_206,C_207,D_208] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_206),C_207,u1_struct_0(D_208)) = k2_tmap_1('#skF_2',B_206,C_207,D_208)
      | ~ m1_pre_topc(D_208,'#skF_2')
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_206))))
      | ~ v1_funct_2(C_207,u1_struct_0('#skF_3'),u1_struct_0(B_206))
      | ~ v1_funct_1(C_207)
      | ~ l1_pre_topc(B_206)
      | ~ v2_pre_topc(B_206)
      | v2_struct_0(B_206)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_1293,c_1293,c_1642])).

tff(c_2139,plain,(
    ! [B_235,C_236,D_237] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_235),C_236,u1_struct_0(D_237)) = k2_tmap_1('#skF_2',B_235,C_236,D_237)
      | ~ m1_pre_topc(D_237,'#skF_2')
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_235))))
      | ~ v1_funct_2(C_236,u1_struct_0('#skF_3'),u1_struct_0(B_235))
      | ~ v1_funct_1(C_236)
      | ~ l1_pre_topc(B_235)
      | ~ v2_pre_topc(B_235)
      | v2_struct_0(B_235) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1660])).

tff(c_2143,plain,(
    ! [D_237] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_237)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_237)
      | ~ m1_pre_topc(D_237,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1300,c_2139])).

tff(c_2156,plain,(
    ! [D_237] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_237)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_237)
      | ~ m1_pre_topc(D_237,'#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_60,c_1301,c_2143])).

tff(c_2291,plain,(
    ! [D_242] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_242)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_242)
      | ~ m1_pre_topc(D_242,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2156])).

tff(c_2317,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0('#skF_3')) = k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1293,c_2291])).

tff(c_2331,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0('#skF_3')) = k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1035,c_2317])).

tff(c_2157,plain,(
    ! [D_237] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_237)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_237)
      | ~ m1_pre_topc(D_237,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2156])).

tff(c_2336,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_2') = k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2331,c_2157])).

tff(c_2357,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_2') = k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2336])).

tff(c_16,plain,(
    ! [A_9,B_10,C_11,D_12] :
      ( m1_subset_1(k2_partfun1(A_9,B_10,C_11,D_12),k1_zfmisc_1(k2_zfmisc_1(A_9,B_10)))
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10)))
      | ~ v1_funct_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2350,plain,
    ( m1_subset_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2331,c_16])).

tff(c_2365,plain,(
    m1_subset_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1300,c_2350])).

tff(c_2433,plain,(
    m1_subset_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2357,c_2365])).

tff(c_97,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_56,c_8])).

tff(c_1299,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1293,c_97])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2370,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0('#skF_3')) = k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2357,c_2331])).

tff(c_1389,plain,(
    ! [A_190,B_191,D_192,C_193] :
      ( r2_relset_1(A_190,B_191,k2_partfun1(A_190,B_191,D_192,C_193),D_192)
      | ~ r1_tarski(A_190,C_193)
      | ~ m1_subset_1(D_192,k1_zfmisc_1(k2_zfmisc_1(A_190,B_191)))
      | ~ v1_funct_2(D_192,A_190,B_191)
      | ~ v1_funct_1(D_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1396,plain,(
    ! [A_190,B_191,A_3,C_193] :
      ( r2_relset_1(A_190,B_191,k2_partfun1(A_190,B_191,A_3,C_193),A_3)
      | ~ r1_tarski(A_190,C_193)
      | ~ v1_funct_2(A_3,A_190,B_191)
      | ~ v1_funct_1(A_3)
      | ~ r1_tarski(A_3,k2_zfmisc_1(A_190,B_191)) ) ),
    inference(resolution,[status(thm)],[c_10,c_1389])).

tff(c_2474,plain,
    ( r2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4')
    | ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1('#skF_4')
    | ~ r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2370,c_1396])).

tff(c_2498,plain,(
    r2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1299,c_60,c_1301,c_6,c_2474])).

tff(c_14,plain,(
    ! [D_8,C_7,A_5,B_6] :
      ( D_8 = C_7
      | ~ r2_relset_1(A_5,B_6,C_7,D_8)
      | ~ m1_subset_1(D_8,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6)))
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2516,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
    | ~ m1_subset_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(resolution,[status(thm)],[c_2498,c_14])).

tff(c_2519,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2433,c_1300,c_2516])).

tff(c_52,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_1297,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1293,c_52])).

tff(c_2545,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2519,c_1297])).

tff(c_13800,plain,(
    ! [C_500,D_501,A_502] :
      ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),C_500,D_501,'#skF_4','#skF_4')
      | ~ v1_funct_2(A_502,C_500,D_501)
      | ~ v1_funct_1(A_502)
      | v1_xboole_0(D_501)
      | ~ r1_tarski(A_502,k2_zfmisc_1(C_500,D_501)) ) ),
    inference(splitRight,[status(thm)],[c_2761])).

tff(c_13810,plain,
    ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1299,c_13800])).

tff(c_13822,plain,
    ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1301,c_13810])).

tff(c_13824,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13638,c_2545,c_13822])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:55:02 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.37/4.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.43/4.16  
% 10.43/4.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.43/4.16  %$ r1_funct_2 > r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.43/4.16  
% 10.43/4.16  %Foreground sorts:
% 10.43/4.16  
% 10.43/4.16  
% 10.43/4.16  %Background operators:
% 10.43/4.16  
% 10.43/4.16  
% 10.43/4.16  %Foreground operators:
% 10.43/4.16  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 10.43/4.16  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 10.43/4.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.43/4.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.43/4.16  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 10.43/4.16  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 10.43/4.16  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.43/4.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.43/4.16  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.43/4.16  tff('#skF_2', type, '#skF_2': $i).
% 10.43/4.16  tff('#skF_3', type, '#skF_3': $i).
% 10.43/4.16  tff('#skF_1', type, '#skF_1': $i).
% 10.43/4.16  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 10.43/4.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.43/4.16  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 10.43/4.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.43/4.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.43/4.16  tff('#skF_4', type, '#skF_4': $i).
% 10.43/4.16  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 10.43/4.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.43/4.16  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 10.43/4.16  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 10.43/4.16  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.43/4.16  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 10.43/4.16  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.43/4.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.43/4.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.43/4.16  
% 10.43/4.19  tff(f_218, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_tmap_1)).
% 10.43/4.19  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 10.43/4.19  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 10.43/4.19  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 10.43/4.19  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 10.43/4.19  tff(f_160, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tmap_1)).
% 10.43/4.19  tff(f_88, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_pre_topc)).
% 10.43/4.19  tff(f_178, axiom, (![A]: (l1_pre_topc(A) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((B = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) => (m1_pre_topc(B, A) <=> m1_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_tmap_1)).
% 10.43/4.19  tff(f_185, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 10.43/4.19  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.43/4.19  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.43/4.19  tff(f_124, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => r1_funct_2(A, B, C, D, E, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r1_funct_2)).
% 10.43/4.19  tff(f_80, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 10.43/4.19  tff(f_151, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 10.43/4.19  tff(f_51, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 10.43/4.19  tff(f_61, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_funct_2)).
% 10.43/4.19  tff(f_43, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 10.43/4.19  tff(c_72, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_218])).
% 10.43/4.19  tff(c_22, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.43/4.19  tff(c_76, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_218])).
% 10.43/4.19  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_218])).
% 10.43/4.19  tff(c_66, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_218])).
% 10.43/4.19  tff(c_62, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_218])).
% 10.43/4.19  tff(c_87, plain, (![B_81, A_82]: (l1_pre_topc(B_81) | ~m1_pre_topc(B_81, A_82) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.43/4.19  tff(c_90, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_62, c_87])).
% 10.43/4.19  tff(c_93, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_90])).
% 10.43/4.19  tff(c_219, plain, (![A_109, B_110]: (m1_pre_topc(A_109, g1_pre_topc(u1_struct_0(B_110), u1_pre_topc(B_110))) | ~m1_pre_topc(A_109, B_110) | ~l1_pre_topc(B_110) | ~l1_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.43/4.19  tff(c_54, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_218])).
% 10.43/4.19  tff(c_157, plain, (![B_101, A_102]: (m1_pre_topc(B_101, A_102) | ~m1_pre_topc(B_101, g1_pre_topc(u1_struct_0(A_102), u1_pre_topc(A_102))) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.43/4.19  tff(c_160, plain, (![B_101]: (m1_pre_topc(B_101, '#skF_2') | ~m1_pre_topc(B_101, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_54, c_157])).
% 10.43/4.19  tff(c_162, plain, (![B_101]: (m1_pre_topc(B_101, '#skF_2') | ~m1_pre_topc(B_101, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_160])).
% 10.43/4.19  tff(c_225, plain, (![A_109]: (m1_pre_topc(A_109, '#skF_2') | ~m1_pre_topc(A_109, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_109))), inference(resolution, [status(thm)], [c_219, c_162])).
% 10.43/4.19  tff(c_240, plain, (![A_109]: (m1_pre_topc(A_109, '#skF_2') | ~m1_pre_topc(A_109, '#skF_3') | ~l1_pre_topc(A_109))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_225])).
% 10.43/4.19  tff(c_164, plain, (![B_104, A_105]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_104), u1_pre_topc(B_104)), A_105) | ~m1_pre_topc(B_104, A_105) | ~l1_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_160])).
% 10.43/4.19  tff(c_24, plain, (![B_20, A_18]: (l1_pre_topc(B_20) | ~m1_pre_topc(B_20, A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.43/4.19  tff(c_185, plain, (![B_106, A_107]: (l1_pre_topc(g1_pre_topc(u1_struct_0(B_106), u1_pre_topc(B_106))) | ~m1_pre_topc(B_106, A_107) | ~l1_pre_topc(A_107))), inference(resolution, [status(thm)], [c_164, c_24])).
% 10.43/4.19  tff(c_189, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_62, c_185])).
% 10.43/4.19  tff(c_193, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_189])).
% 10.43/4.19  tff(c_180, plain, (![A_105]: (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), A_105) | ~m1_pre_topc('#skF_2', A_105) | ~l1_pre_topc(A_105))), inference(superposition, [status(thm), theory('equality')], [c_54, c_164])).
% 10.43/4.19  tff(c_236, plain, (![A_109]: (m1_pre_topc(A_109, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_109, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_109))), inference(superposition, [status(thm), theory('equality')], [c_54, c_219])).
% 10.43/4.19  tff(c_286, plain, (![A_119]: (m1_pre_topc(A_119, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_119, '#skF_2') | ~l1_pre_topc(A_119))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_236])).
% 10.43/4.19  tff(c_32, plain, (![B_25, A_23]: (m1_pre_topc(B_25, A_23) | ~m1_pre_topc(B_25, g1_pre_topc(u1_struct_0(A_23), u1_pre_topc(A_23))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.43/4.19  tff(c_294, plain, (![A_119]: (m1_pre_topc(A_119, '#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc(A_119, '#skF_2') | ~l1_pre_topc(A_119))), inference(resolution, [status(thm)], [c_286, c_32])).
% 10.43/4.19  tff(c_313, plain, (![A_120]: (m1_pre_topc(A_120, '#skF_3') | ~m1_pre_topc(A_120, '#skF_2') | ~l1_pre_topc(A_120))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_294])).
% 10.43/4.19  tff(c_320, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_3') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_180, c_313])).
% 10.43/4.19  tff(c_331, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_193, c_320])).
% 10.43/4.19  tff(c_354, plain, (~m1_pre_topc('#skF_2', '#skF_2')), inference(splitLeft, [status(thm)], [c_331])).
% 10.43/4.19  tff(c_357, plain, (~m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_240, c_354])).
% 10.43/4.19  tff(c_360, plain, (~m1_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_357])).
% 10.43/4.19  tff(c_42, plain, (![B_52, A_50]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_52), u1_pre_topc(B_52)), A_50) | ~m1_pre_topc(B_52, A_50) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_160])).
% 10.43/4.19  tff(c_324, plain, (![B_52]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_52), u1_pre_topc(B_52)), '#skF_3') | ~l1_pre_topc(g1_pre_topc(u1_struct_0(B_52), u1_pre_topc(B_52))) | ~m1_pre_topc(B_52, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_313])).
% 10.43/4.19  tff(c_334, plain, (![B_52]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_52), u1_pre_topc(B_52)), '#skF_3') | ~l1_pre_topc(g1_pre_topc(u1_struct_0(B_52), u1_pre_topc(B_52))) | ~m1_pre_topc(B_52, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_324])).
% 10.43/4.19  tff(c_68, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_218])).
% 10.43/4.19  tff(c_112, plain, (![A_85]: (v2_pre_topc(g1_pre_topc(u1_struct_0(A_85), u1_pre_topc(A_85))) | ~l1_pre_topc(A_85) | ~v2_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_88])).
% 10.43/4.19  tff(c_115, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_54, c_112])).
% 10.43/4.19  tff(c_117, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_115])).
% 10.43/4.19  tff(c_791, plain, (![C_165, A_166]: (m1_pre_topc(C_165, A_166) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_165), u1_pre_topc(C_165)), A_166) | ~l1_pre_topc(C_165) | ~v2_pre_topc(C_165) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_165), u1_pre_topc(C_165))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_165), u1_pre_topc(C_165))) | ~l1_pre_topc(A_166))), inference(cnfTransformation, [status(thm)], [f_178])).
% 10.43/4.19  tff(c_818, plain, (![A_166]: (m1_pre_topc('#skF_2', A_166) | ~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), A_166) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_166))), inference(superposition, [status(thm), theory('equality')], [c_54, c_791])).
% 10.43/4.19  tff(c_992, plain, (![A_167]: (m1_pre_topc('#skF_2', A_167) | ~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), A_167) | ~l1_pre_topc(A_167))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_54, c_193, c_54, c_68, c_66, c_818])).
% 10.43/4.19  tff(c_1004, plain, (m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_334, c_992])).
% 10.43/4.19  tff(c_1031, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_193, c_93, c_1004])).
% 10.43/4.19  tff(c_1033, plain, $false, inference(negUnitSimplification, [status(thm)], [c_360, c_1031])).
% 10.43/4.19  tff(c_1035, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(splitRight, [status(thm)], [c_331])).
% 10.43/4.19  tff(c_306, plain, (![A_119]: (m1_pre_topc(A_119, '#skF_3') | ~m1_pre_topc(A_119, '#skF_2') | ~l1_pre_topc(A_119))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_294])).
% 10.43/4.19  tff(c_1038, plain, (m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_1035, c_306])).
% 10.43/4.19  tff(c_1048, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1038])).
% 10.43/4.19  tff(c_124, plain, (![B_87, A_88]: (m1_subset_1(u1_struct_0(B_87), k1_zfmisc_1(u1_struct_0(A_88))) | ~m1_pre_topc(B_87, A_88) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_185])).
% 10.43/4.19  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.43/4.19  tff(c_128, plain, (![B_87, A_88]: (r1_tarski(u1_struct_0(B_87), u1_struct_0(A_88)) | ~m1_pre_topc(B_87, A_88) | ~l1_pre_topc(A_88))), inference(resolution, [status(thm)], [c_124, c_8])).
% 10.43/4.19  tff(c_129, plain, (![B_89, A_90]: (r1_tarski(u1_struct_0(B_89), u1_struct_0(A_90)) | ~m1_pre_topc(B_89, A_90) | ~l1_pre_topc(A_90))), inference(resolution, [status(thm)], [c_124, c_8])).
% 10.43/4.19  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.43/4.19  tff(c_1124, plain, (![B_181, A_182]: (u1_struct_0(B_181)=u1_struct_0(A_182) | ~r1_tarski(u1_struct_0(A_182), u1_struct_0(B_181)) | ~m1_pre_topc(B_181, A_182) | ~l1_pre_topc(A_182))), inference(resolution, [status(thm)], [c_129, c_2])).
% 10.43/4.19  tff(c_1235, plain, (![B_188, A_189]: (u1_struct_0(B_188)=u1_struct_0(A_189) | ~m1_pre_topc(A_189, B_188) | ~l1_pre_topc(B_188) | ~m1_pre_topc(B_188, A_189) | ~l1_pre_topc(A_189))), inference(resolution, [status(thm)], [c_128, c_1124])).
% 10.43/4.19  tff(c_1259, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_62, c_1235])).
% 10.43/4.19  tff(c_1293, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_1048, c_66, c_1259])).
% 10.43/4.19  tff(c_58, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_218])).
% 10.43/4.19  tff(c_1301, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1293, c_58])).
% 10.43/4.19  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_218])).
% 10.43/4.19  tff(c_1300, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_1293, c_56])).
% 10.43/4.19  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.43/4.19  tff(c_1578, plain, (![E_201, C_202, B_198, D_197, A_199, F_200]: (r1_funct_2(A_199, B_198, C_202, D_197, E_201, E_201) | ~m1_subset_1(F_200, k1_zfmisc_1(k2_zfmisc_1(C_202, D_197))) | ~v1_funct_2(F_200, C_202, D_197) | ~v1_funct_1(F_200) | ~m1_subset_1(E_201, k1_zfmisc_1(k2_zfmisc_1(A_199, B_198))) | ~v1_funct_2(E_201, A_199, B_198) | ~v1_funct_1(E_201) | v1_xboole_0(D_197) | v1_xboole_0(B_198))), inference(cnfTransformation, [status(thm)], [f_124])).
% 10.43/4.19  tff(c_2751, plain, (![B_262, A_265, E_260, C_261, A_264, D_263]: (r1_funct_2(A_264, B_262, C_261, D_263, E_260, E_260) | ~v1_funct_2(A_265, C_261, D_263) | ~v1_funct_1(A_265) | ~m1_subset_1(E_260, k1_zfmisc_1(k2_zfmisc_1(A_264, B_262))) | ~v1_funct_2(E_260, A_264, B_262) | ~v1_funct_1(E_260) | v1_xboole_0(D_263) | v1_xboole_0(B_262) | ~r1_tarski(A_265, k2_zfmisc_1(C_261, D_263)))), inference(resolution, [status(thm)], [c_10, c_1578])).
% 10.43/4.19  tff(c_2753, plain, (![C_261, D_263, A_265]: (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), C_261, D_263, '#skF_4', '#skF_4') | ~v1_funct_2(A_265, C_261, D_263) | ~v1_funct_1(A_265) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(D_263) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski(A_265, k2_zfmisc_1(C_261, D_263)))), inference(resolution, [status(thm)], [c_1300, c_2751])).
% 10.43/4.19  tff(c_2761, plain, (![C_261, D_263, A_265]: (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), C_261, D_263, '#skF_4', '#skF_4') | ~v1_funct_2(A_265, C_261, D_263) | ~v1_funct_1(A_265) | v1_xboole_0(D_263) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski(A_265, k2_zfmisc_1(C_261, D_263)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1301, c_2753])).
% 10.43/4.19  tff(c_13213, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_2761])).
% 10.43/4.19  tff(c_26, plain, (![A_21]: (~v1_xboole_0(u1_struct_0(A_21)) | ~l1_struct_0(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.43/4.19  tff(c_13626, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_13213, c_26])).
% 10.43/4.19  tff(c_13629, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_76, c_13626])).
% 10.43/4.19  tff(c_13632, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_13629])).
% 10.43/4.19  tff(c_13636, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_13632])).
% 10.43/4.19  tff(c_13638, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_2761])).
% 10.43/4.19  tff(c_74, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_218])).
% 10.43/4.19  tff(c_70, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_218])).
% 10.43/4.19  tff(c_1634, plain, (![A_205, B_206, C_207, D_208]: (k2_partfun1(u1_struct_0(A_205), u1_struct_0(B_206), C_207, u1_struct_0(D_208))=k2_tmap_1(A_205, B_206, C_207, D_208) | ~m1_pre_topc(D_208, A_205) | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_205), u1_struct_0(B_206)))) | ~v1_funct_2(C_207, u1_struct_0(A_205), u1_struct_0(B_206)) | ~v1_funct_1(C_207) | ~l1_pre_topc(B_206) | ~v2_pre_topc(B_206) | v2_struct_0(B_206) | ~l1_pre_topc(A_205) | ~v2_pre_topc(A_205) | v2_struct_0(A_205))), inference(cnfTransformation, [status(thm)], [f_151])).
% 10.43/4.19  tff(c_1642, plain, (![B_206, C_207, D_208]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0(B_206), C_207, u1_struct_0(D_208))=k2_tmap_1('#skF_2', B_206, C_207, D_208) | ~m1_pre_topc(D_208, '#skF_2') | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_206)))) | ~v1_funct_2(C_207, u1_struct_0('#skF_2'), u1_struct_0(B_206)) | ~v1_funct_1(C_207) | ~l1_pre_topc(B_206) | ~v2_pre_topc(B_206) | v2_struct_0(B_206) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1293, c_1634])).
% 10.43/4.19  tff(c_1660, plain, (![B_206, C_207, D_208]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_206), C_207, u1_struct_0(D_208))=k2_tmap_1('#skF_2', B_206, C_207, D_208) | ~m1_pre_topc(D_208, '#skF_2') | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_206)))) | ~v1_funct_2(C_207, u1_struct_0('#skF_3'), u1_struct_0(B_206)) | ~v1_funct_1(C_207) | ~l1_pre_topc(B_206) | ~v2_pre_topc(B_206) | v2_struct_0(B_206) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_1293, c_1293, c_1642])).
% 10.43/4.19  tff(c_2139, plain, (![B_235, C_236, D_237]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_235), C_236, u1_struct_0(D_237))=k2_tmap_1('#skF_2', B_235, C_236, D_237) | ~m1_pre_topc(D_237, '#skF_2') | ~m1_subset_1(C_236, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_235)))) | ~v1_funct_2(C_236, u1_struct_0('#skF_3'), u1_struct_0(B_235)) | ~v1_funct_1(C_236) | ~l1_pre_topc(B_235) | ~v2_pre_topc(B_235) | v2_struct_0(B_235))), inference(negUnitSimplification, [status(thm)], [c_70, c_1660])).
% 10.43/4.19  tff(c_2143, plain, (![D_237]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_237))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_237) | ~m1_pre_topc(D_237, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_1300, c_2139])).
% 10.43/4.19  tff(c_2156, plain, (![D_237]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_237))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_237) | ~m1_pre_topc(D_237, '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_60, c_1301, c_2143])).
% 10.43/4.19  tff(c_2291, plain, (![D_242]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_242))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_242) | ~m1_pre_topc(D_242, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_76, c_2156])).
% 10.43/4.19  tff(c_2317, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0('#skF_3'))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1293, c_2291])).
% 10.43/4.19  tff(c_2331, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0('#skF_3'))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1035, c_2317])).
% 10.43/4.19  tff(c_2157, plain, (![D_237]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_237))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_237) | ~m1_pre_topc(D_237, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_76, c_2156])).
% 10.43/4.19  tff(c_2336, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_2')=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2331, c_2157])).
% 10.43/4.19  tff(c_2357, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_2')=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2336])).
% 10.43/4.19  tff(c_16, plain, (![A_9, B_10, C_11, D_12]: (m1_subset_1(k2_partfun1(A_9, B_10, C_11, D_12), k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))) | ~v1_funct_1(C_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.43/4.19  tff(c_2350, plain, (m1_subset_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2331, c_16])).
% 10.43/4.19  tff(c_2365, plain, (m1_subset_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1300, c_2350])).
% 10.43/4.19  tff(c_2433, plain, (m1_subset_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_2357, c_2365])).
% 10.43/4.19  tff(c_97, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_56, c_8])).
% 10.43/4.19  tff(c_1299, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1293, c_97])).
% 10.43/4.19  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.43/4.19  tff(c_2370, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0('#skF_3'))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2357, c_2331])).
% 10.43/4.19  tff(c_1389, plain, (![A_190, B_191, D_192, C_193]: (r2_relset_1(A_190, B_191, k2_partfun1(A_190, B_191, D_192, C_193), D_192) | ~r1_tarski(A_190, C_193) | ~m1_subset_1(D_192, k1_zfmisc_1(k2_zfmisc_1(A_190, B_191))) | ~v1_funct_2(D_192, A_190, B_191) | ~v1_funct_1(D_192))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.43/4.19  tff(c_1396, plain, (![A_190, B_191, A_3, C_193]: (r2_relset_1(A_190, B_191, k2_partfun1(A_190, B_191, A_3, C_193), A_3) | ~r1_tarski(A_190, C_193) | ~v1_funct_2(A_3, A_190, B_191) | ~v1_funct_1(A_3) | ~r1_tarski(A_3, k2_zfmisc_1(A_190, B_191)))), inference(resolution, [status(thm)], [c_10, c_1389])).
% 10.43/4.19  tff(c_2474, plain, (r2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4') | ~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_3')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2370, c_1396])).
% 10.43/4.19  tff(c_2498, plain, (r2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1299, c_60, c_1301, c_6, c_2474])).
% 10.43/4.19  tff(c_14, plain, (![D_8, C_7, A_5, B_6]: (D_8=C_7 | ~r2_relset_1(A_5, B_6, C_7, D_8) | ~m1_subset_1(D_8, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.43/4.19  tff(c_2516, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~m1_subset_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_2498, c_14])).
% 10.43/4.19  tff(c_2519, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2433, c_1300, c_2516])).
% 10.43/4.19  tff(c_52, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_218])).
% 10.43/4.19  tff(c_1297, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1293, c_52])).
% 10.43/4.19  tff(c_2545, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2519, c_1297])).
% 10.43/4.19  tff(c_13800, plain, (![C_500, D_501, A_502]: (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), C_500, D_501, '#skF_4', '#skF_4') | ~v1_funct_2(A_502, C_500, D_501) | ~v1_funct_1(A_502) | v1_xboole_0(D_501) | ~r1_tarski(A_502, k2_zfmisc_1(C_500, D_501)))), inference(splitRight, [status(thm)], [c_2761])).
% 10.43/4.19  tff(c_13810, plain, (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_1299, c_13800])).
% 10.43/4.19  tff(c_13822, plain, (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1301, c_13810])).
% 10.43/4.19  tff(c_13824, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13638, c_2545, c_13822])).
% 10.43/4.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.43/4.19  
% 10.43/4.19  Inference rules
% 10.43/4.19  ----------------------
% 10.43/4.19  #Ref     : 0
% 10.43/4.19  #Sup     : 2844
% 10.43/4.19  #Fact    : 0
% 10.43/4.19  #Define  : 0
% 10.43/4.19  #Split   : 10
% 10.43/4.19  #Chain   : 0
% 10.43/4.19  #Close   : 0
% 10.43/4.19  
% 10.43/4.19  Ordering : KBO
% 10.43/4.19  
% 10.43/4.19  Simplification rules
% 10.43/4.19  ----------------------
% 10.43/4.19  #Subsume      : 409
% 10.43/4.19  #Demod        : 7157
% 10.43/4.19  #Tautology    : 997
% 10.43/4.19  #SimpNegUnit  : 163
% 10.43/4.19  #BackRed      : 26
% 10.43/4.19  
% 10.43/4.19  #Partial instantiations: 0
% 10.43/4.19  #Strategies tried      : 1
% 10.43/4.19  
% 10.43/4.19  Timing (in seconds)
% 10.43/4.19  ----------------------
% 10.43/4.19  Preprocessing        : 0.38
% 10.43/4.19  Parsing              : 0.20
% 10.43/4.19  CNF conversion       : 0.03
% 10.43/4.19  Main loop            : 3.02
% 10.43/4.19  Inferencing          : 0.71
% 10.43/4.19  Reduction            : 1.28
% 10.43/4.19  Demodulation         : 1.03
% 10.43/4.19  BG Simplification    : 0.09
% 10.43/4.19  Subsumption          : 0.83
% 10.43/4.19  Abstraction          : 0.15
% 10.43/4.19  MUC search           : 0.00
% 10.43/4.19  Cooper               : 0.00
% 10.43/4.19  Total                : 3.46
% 10.43/4.19  Index Insertion      : 0.00
% 10.43/4.19  Index Deletion       : 0.00
% 10.43/4.19  Index Matching       : 0.00
% 10.43/4.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
