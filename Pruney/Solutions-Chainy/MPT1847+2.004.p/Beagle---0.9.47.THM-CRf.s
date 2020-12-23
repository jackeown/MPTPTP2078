%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:52 EST 2020

% Result     : Theorem 15.80s
% Output     : CNFRefutation 15.80s
% Verified   : 
% Statistics : Number of formulae       :  195 (2749 expanded)
%              Number of leaves         :   43 ( 965 expanded)
%              Depth                    :   20
%              Number of atoms          :  377 (7120 expanded)
%              Number of equality atoms :   53 (1229 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_155,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ! [C] :
                ( m1_pre_topc(C,A)
               => ( ( g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C))
                    & v1_tex_2(B,A) )
                 => v1_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_tex_2)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_133,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v1_subset_1(C,u1_struct_0(A)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

tff(f_33,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_112,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( ( v1_pre_topc(C)
                & m1_pre_topc(C,A) )
             => ( C = k1_pre_topc(A,B)
              <=> k2_struct_0(C) = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_pre_topc)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(B,A)
          <=> ( r1_tarski(k2_struct_0(B),k2_struct_0(A))
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
                 => ( r2_hidden(C,u1_pre_topc(B))
                  <=> ? [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                        & r2_hidden(D,u1_pre_topc(A))
                        & C = k9_subset_1(u1_struct_0(B),D,k2_struct_0(B)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).

tff(f_119,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_140,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_38,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_76,plain,(
    ~ v1_tex_2('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_82,plain,(
    m1_pre_topc('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_86,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_84,plain,(
    m1_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_121,plain,(
    ! [B_92,A_93] :
      ( l1_pre_topc(B_92)
      | ~ m1_pre_topc(B_92,A_93)
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_127,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_121])).

tff(c_133,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_127])).

tff(c_124,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_121])).

tff(c_130,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_124])).

tff(c_52,plain,(
    ! [A_56] :
      ( l1_struct_0(A_56)
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_107,plain,(
    ! [A_90] :
      ( u1_struct_0(A_90) = k2_struct_0(A_90)
      | ~ l1_struct_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_111,plain,(
    ! [A_56] :
      ( u1_struct_0(A_56) = k2_struct_0(A_56)
      | ~ l1_pre_topc(A_56) ) ),
    inference(resolution,[status(thm)],[c_52,c_107])).

tff(c_144,plain,(
    u1_struct_0('#skF_7') = k2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_130,c_111])).

tff(c_6269,plain,(
    ! [B_318,A_319] :
      ( u1_struct_0(B_318) = '#skF_4'(A_319,B_318)
      | v1_tex_2(B_318,A_319)
      | ~ m1_pre_topc(B_318,A_319)
      | ~ l1_pre_topc(A_319) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_6272,plain,
    ( u1_struct_0('#skF_7') = '#skF_4'('#skF_5','#skF_7')
    | ~ m1_pre_topc('#skF_7','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_6269,c_76])).

tff(c_6275,plain,(
    k2_struct_0('#skF_7') = '#skF_4'('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_144,c_6272])).

tff(c_6284,plain,(
    u1_struct_0('#skF_7') = '#skF_4'('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6275,c_144])).

tff(c_8,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_88,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_428,plain,(
    ! [A_117,B_118] :
      ( m1_pre_topc(k1_pre_topc(A_117,B_118),A_117)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_451,plain,(
    ! [A_119] :
      ( m1_pre_topc(k1_pre_topc(A_119,u1_struct_0(A_119)),A_119)
      | ~ l1_pre_topc(A_119) ) ),
    inference(resolution,[status(thm)],[c_88,c_428])).

tff(c_54,plain,(
    ! [B_59,A_57] :
      ( l1_pre_topc(B_59)
      | ~ m1_pre_topc(B_59,A_57)
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_469,plain,(
    ! [A_119] :
      ( l1_pre_topc(k1_pre_topc(A_119,u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119) ) ),
    inference(resolution,[status(thm)],[c_451,c_54])).

tff(c_6302,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_7','#skF_4'('#skF_5','#skF_7')))
    | ~ l1_pre_topc('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_6284,c_469])).

tff(c_6344,plain,(
    l1_pre_topc(k1_pre_topc('#skF_7','#skF_4'('#skF_5','#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_6302])).

tff(c_450,plain,(
    ! [A_117] :
      ( m1_pre_topc(k1_pre_topc(A_117,u1_struct_0(A_117)),A_117)
      | ~ l1_pre_topc(A_117) ) ),
    inference(resolution,[status(thm)],[c_88,c_428])).

tff(c_6305,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_7','#skF_4'('#skF_5','#skF_7')),'#skF_7')
    | ~ l1_pre_topc('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_6284,c_450])).

tff(c_6346,plain,(
    m1_pre_topc(k1_pre_topc('#skF_7','#skF_4'('#skF_5','#skF_7')),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_6305])).

tff(c_6376,plain,(
    ! [A_321,B_322] :
      ( m1_pre_topc(A_321,g1_pre_topc(u1_struct_0(B_322),u1_pre_topc(B_322)))
      | ~ m1_pre_topc(A_321,B_322)
      | ~ l1_pre_topc(B_322)
      | ~ l1_pre_topc(A_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_6385,plain,(
    ! [A_321] :
      ( m1_pre_topc(A_321,g1_pre_topc('#skF_4'('#skF_5','#skF_7'),u1_pre_topc('#skF_7')))
      | ~ m1_pre_topc(A_321,'#skF_7')
      | ~ l1_pre_topc('#skF_7')
      | ~ l1_pre_topc(A_321) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6284,c_6376])).

tff(c_13532,plain,(
    ! [A_501] :
      ( m1_pre_topc(A_501,g1_pre_topc('#skF_4'('#skF_5','#skF_7'),u1_pre_topc('#skF_7')))
      | ~ m1_pre_topc(A_501,'#skF_7')
      | ~ l1_pre_topc(A_501) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_6385])).

tff(c_148,plain,(
    u1_struct_0('#skF_6') = k2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_133,c_111])).

tff(c_80,plain,(
    g1_pre_topc(u1_struct_0('#skF_7'),u1_pre_topc('#skF_7')) = g1_pre_topc(u1_struct_0('#skF_6'),u1_pre_topc('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_149,plain,(
    g1_pre_topc(u1_struct_0('#skF_6'),u1_pre_topc('#skF_6')) = g1_pre_topc(k2_struct_0('#skF_7'),u1_pre_topc('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_80])).

tff(c_158,plain,(
    g1_pre_topc(k2_struct_0('#skF_7'),u1_pre_topc('#skF_7')) = g1_pre_topc(k2_struct_0('#skF_6'),u1_pre_topc('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_149])).

tff(c_6283,plain,(
    g1_pre_topc(k2_struct_0('#skF_6'),u1_pre_topc('#skF_6')) = g1_pre_topc('#skF_4'('#skF_5','#skF_7'),u1_pre_topc('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6275,c_158])).

tff(c_284,plain,(
    ! [B_106,A_107] :
      ( m1_pre_topc(B_106,A_107)
      | ~ m1_pre_topc(B_106,g1_pre_topc(u1_struct_0(A_107),u1_pre_topc(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_287,plain,(
    ! [B_106] :
      ( m1_pre_topc(B_106,'#skF_6')
      | ~ m1_pre_topc(B_106,g1_pre_topc(k2_struct_0('#skF_6'),u1_pre_topc('#skF_6')))
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_284])).

tff(c_295,plain,(
    ! [B_106] :
      ( m1_pre_topc(B_106,'#skF_6')
      | ~ m1_pre_topc(B_106,g1_pre_topc(k2_struct_0('#skF_6'),u1_pre_topc('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_287])).

tff(c_6727,plain,(
    ! [B_106] :
      ( m1_pre_topc(B_106,'#skF_6')
      | ~ m1_pre_topc(B_106,g1_pre_topc('#skF_4'('#skF_5','#skF_7'),u1_pre_topc('#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6283,c_295])).

tff(c_13619,plain,(
    ! [A_505] :
      ( m1_pre_topc(A_505,'#skF_6')
      | ~ m1_pre_topc(A_505,'#skF_7')
      | ~ l1_pre_topc(A_505) ) ),
    inference(resolution,[status(thm)],[c_13532,c_6727])).

tff(c_13658,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_7','#skF_4'('#skF_5','#skF_7')),'#skF_6')
    | ~ l1_pre_topc(k1_pre_topc('#skF_7','#skF_4'('#skF_5','#skF_7'))) ),
    inference(resolution,[status(thm)],[c_6346,c_13619])).

tff(c_13690,plain,(
    m1_pre_topc(k1_pre_topc('#skF_7','#skF_4'('#skF_5','#skF_7')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6344,c_13658])).

tff(c_219,plain,(
    ! [A_101,B_102] :
      ( v1_pre_topc(k1_pre_topc(A_101,B_102))
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_244,plain,(
    ! [A_103] :
      ( v1_pre_topc(k1_pre_topc(A_103,u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(resolution,[status(thm)],[c_88,c_219])).

tff(c_250,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_7',k2_struct_0('#skF_7')))
    | ~ l1_pre_topc('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_244])).

tff(c_257,plain,(
    v1_pre_topc(k1_pre_topc('#skF_7',k2_struct_0('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_250])).

tff(c_6282,plain,(
    v1_pre_topc(k1_pre_topc('#skF_7','#skF_4'('#skF_5','#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6275,c_257])).

tff(c_7345,plain,(
    ! [A_355,B_356] :
      ( k2_struct_0(k1_pre_topc(A_355,B_356)) = B_356
      | ~ m1_pre_topc(k1_pre_topc(A_355,B_356),A_355)
      | ~ v1_pre_topc(k1_pre_topc(A_355,B_356))
      | ~ m1_subset_1(B_356,k1_zfmisc_1(u1_struct_0(A_355)))
      | ~ l1_pre_topc(A_355) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_7366,plain,
    ( k2_struct_0(k1_pre_topc('#skF_7','#skF_4'('#skF_5','#skF_7'))) = '#skF_4'('#skF_5','#skF_7')
    | ~ v1_pre_topc(k1_pre_topc('#skF_7','#skF_4'('#skF_5','#skF_7')))
    | ~ m1_subset_1('#skF_4'('#skF_5','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_7')))
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_6346,c_7345])).

tff(c_7399,plain,(
    k2_struct_0(k1_pre_topc('#skF_7','#skF_4'('#skF_5','#skF_7'))) = '#skF_4'('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_88,c_6284,c_6282,c_7366])).

tff(c_38,plain,(
    ! [B_36,A_14] :
      ( r1_tarski(k2_struct_0(B_36),k2_struct_0(A_14))
      | ~ m1_pre_topc(B_36,A_14)
      | ~ l1_pre_topc(B_36)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_7616,plain,(
    ! [A_14] :
      ( r1_tarski('#skF_4'('#skF_5','#skF_7'),k2_struct_0(A_14))
      | ~ m1_pre_topc(k1_pre_topc('#skF_7','#skF_4'('#skF_5','#skF_7')),A_14)
      | ~ l1_pre_topc(k1_pre_topc('#skF_7','#skF_4'('#skF_5','#skF_7')))
      | ~ l1_pre_topc(A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7399,c_38])).

tff(c_26755,plain,(
    ! [A_698] :
      ( r1_tarski('#skF_4'('#skF_5','#skF_7'),k2_struct_0(A_698))
      | ~ m1_pre_topc(k1_pre_topc('#skF_7','#skF_4'('#skF_5','#skF_7')),A_698)
      | ~ l1_pre_topc(A_698) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6344,c_7616])).

tff(c_112,plain,(
    ! [A_91] :
      ( u1_struct_0(A_91) = k2_struct_0(A_91)
      | ~ l1_pre_topc(A_91) ) ),
    inference(resolution,[status(thm)],[c_52,c_107])).

tff(c_116,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_86,c_112])).

tff(c_175,plain,(
    ! [B_98,A_99] :
      ( m1_subset_1(u1_struct_0(B_98),k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ m1_pre_topc(B_98,A_99)
      | ~ l1_pre_topc(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_196,plain,(
    ! [B_98] :
      ( m1_subset_1(u1_struct_0(B_98),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_pre_topc(B_98,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_175])).

tff(c_323,plain,(
    ! [B_110] :
      ( m1_subset_1(u1_struct_0(B_110),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_pre_topc(B_110,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_196])).

tff(c_335,plain,
    ( m1_subset_1(k2_struct_0('#skF_7'),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | ~ m1_pre_topc('#skF_7','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_323])).

tff(c_344,plain,(
    m1_subset_1(k2_struct_0('#skF_7'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_335])).

tff(c_72,plain,(
    ! [B_80,A_79] :
      ( v1_subset_1(B_80,A_79)
      | B_80 = A_79
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_361,plain,
    ( v1_subset_1(k2_struct_0('#skF_7'),k2_struct_0('#skF_5'))
    | k2_struct_0('#skF_7') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_344,c_72])).

tff(c_6515,plain,
    ( v1_subset_1('#skF_4'('#skF_5','#skF_7'),k2_struct_0('#skF_5'))
    | k2_struct_0('#skF_5') = '#skF_4'('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6275,c_6275,c_361])).

tff(c_6516,plain,(
    k2_struct_0('#skF_5') = '#skF_4'('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_6515])).

tff(c_461,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_6',k2_struct_0('#skF_6')),'#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_451])).

tff(c_471,plain,(
    m1_pre_topc(k1_pre_topc('#skF_6',k2_struct_0('#skF_6')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_461])).

tff(c_478,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_6',k2_struct_0('#skF_6')))
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_471,c_54])).

tff(c_481,plain,(
    l1_pre_topc(k1_pre_topc('#skF_6',k2_struct_0('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_478])).

tff(c_527,plain,(
    ! [B_121,A_122] :
      ( u1_struct_0(B_121) = '#skF_4'(A_122,B_121)
      | v1_tex_2(B_121,A_122)
      | ~ m1_pre_topc(B_121,A_122)
      | ~ l1_pre_topc(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_530,plain,
    ( u1_struct_0('#skF_7') = '#skF_4'('#skF_5','#skF_7')
    | ~ m1_pre_topc('#skF_7','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_527,c_76])).

tff(c_533,plain,(
    k2_struct_0('#skF_7') = '#skF_4'('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_144,c_530])).

tff(c_624,plain,(
    g1_pre_topc(k2_struct_0('#skF_6'),u1_pre_topc('#skF_6')) = g1_pre_topc('#skF_4'('#skF_5','#skF_7'),u1_pre_topc('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_158])).

tff(c_762,plain,(
    ! [A_127,B_128] :
      ( m1_pre_topc(A_127,g1_pre_topc(u1_struct_0(B_128),u1_pre_topc(B_128)))
      | ~ m1_pre_topc(A_127,B_128)
      | ~ l1_pre_topc(B_128)
      | ~ l1_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_777,plain,(
    ! [A_127] :
      ( m1_pre_topc(A_127,g1_pre_topc(k2_struct_0('#skF_6'),u1_pre_topc('#skF_6')))
      | ~ m1_pre_topc(A_127,'#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ l1_pre_topc(A_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_762])).

tff(c_785,plain,(
    ! [A_127] :
      ( m1_pre_topc(A_127,g1_pre_topc(k2_struct_0('#skF_6'),u1_pre_topc('#skF_6')))
      | ~ m1_pre_topc(A_127,'#skF_6')
      | ~ l1_pre_topc(A_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_777])).

tff(c_6215,plain,(
    ! [A_316] :
      ( m1_pre_topc(A_316,g1_pre_topc('#skF_4'('#skF_5','#skF_7'),u1_pre_topc('#skF_7')))
      | ~ m1_pre_topc(A_316,'#skF_6')
      | ~ l1_pre_topc(A_316) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_624,c_785])).

tff(c_290,plain,(
    ! [B_106] :
      ( m1_pre_topc(B_106,'#skF_7')
      | ~ m1_pre_topc(B_106,g1_pre_topc(k2_struct_0('#skF_7'),u1_pre_topc('#skF_7')))
      | ~ l1_pre_topc('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_284])).

tff(c_297,plain,(
    ! [B_106] :
      ( m1_pre_topc(B_106,'#skF_7')
      | ~ m1_pre_topc(B_106,g1_pre_topc(k2_struct_0('#skF_6'),u1_pre_topc('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_158,c_290])).

tff(c_4792,plain,(
    ! [B_106] :
      ( m1_pre_topc(B_106,'#skF_7')
      | ~ m1_pre_topc(B_106,g1_pre_topc('#skF_4'('#skF_5','#skF_7'),u1_pre_topc('#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_624,c_297])).

tff(c_6237,plain,(
    ! [A_317] :
      ( m1_pre_topc(A_317,'#skF_7')
      | ~ m1_pre_topc(A_317,'#skF_6')
      | ~ l1_pre_topc(A_317) ) ),
    inference(resolution,[status(thm)],[c_6215,c_4792])).

tff(c_12,plain,(
    ! [A_5] : ~ v1_subset_1(k2_subset_1(A_5),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_87,plain,(
    ! [A_5] : ~ v1_subset_1(A_5,A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_12])).

tff(c_78,plain,(
    v1_tex_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_332,plain,
    ( m1_subset_1(k2_struct_0('#skF_6'),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | ~ m1_pre_topc('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_323])).

tff(c_342,plain,(
    m1_subset_1(k2_struct_0('#skF_6'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_332])).

tff(c_353,plain,
    ( v1_subset_1(k2_struct_0('#skF_6'),k2_struct_0('#skF_5'))
    | k2_struct_0('#skF_5') = k2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_342,c_72])).

tff(c_526,plain,(
    k2_struct_0('#skF_5') = k2_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_353])).

tff(c_805,plain,
    ( v1_subset_1('#skF_4'('#skF_5','#skF_7'),k2_struct_0('#skF_6'))
    | k2_struct_0('#skF_6') = '#skF_4'('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_526,c_533,c_526,c_361])).

tff(c_806,plain,(
    k2_struct_0('#skF_6') = '#skF_4'('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_805])).

tff(c_821,plain,(
    u1_struct_0('#skF_6') = '#skF_4'('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_806,c_148])).

tff(c_542,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_116])).

tff(c_813,plain,(
    u1_struct_0('#skF_5') = '#skF_4'('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_806,c_542])).

tff(c_62,plain,(
    ! [B_68,A_66] :
      ( m1_subset_1(u1_struct_0(B_68),k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ m1_pre_topc(B_68,A_66)
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1172,plain,(
    ! [B_143,A_144] :
      ( v1_subset_1(u1_struct_0(B_143),u1_struct_0(A_144))
      | ~ m1_subset_1(u1_struct_0(B_143),k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ v1_tex_2(B_143,A_144)
      | ~ m1_pre_topc(B_143,A_144)
      | ~ l1_pre_topc(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_3872,plain,(
    ! [B_236,A_237] :
      ( v1_subset_1(u1_struct_0(B_236),u1_struct_0(A_237))
      | ~ v1_tex_2(B_236,A_237)
      | ~ m1_pre_topc(B_236,A_237)
      | ~ l1_pre_topc(A_237) ) ),
    inference(resolution,[status(thm)],[c_62,c_1172])).

tff(c_3906,plain,(
    ! [B_236] :
      ( v1_subset_1(u1_struct_0(B_236),'#skF_4'('#skF_5','#skF_7'))
      | ~ v1_tex_2(B_236,'#skF_5')
      | ~ m1_pre_topc(B_236,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_813,c_3872])).

tff(c_4208,plain,(
    ! [B_247] :
      ( v1_subset_1(u1_struct_0(B_247),'#skF_4'('#skF_5','#skF_7'))
      | ~ v1_tex_2(B_247,'#skF_5')
      | ~ m1_pre_topc(B_247,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_3906])).

tff(c_4226,plain,
    ( v1_subset_1('#skF_4'('#skF_5','#skF_7'),'#skF_4'('#skF_5','#skF_7'))
    | ~ v1_tex_2('#skF_6','#skF_5')
    | ~ m1_pre_topc('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_821,c_4208])).

tff(c_4237,plain,(
    v1_subset_1('#skF_4'('#skF_5','#skF_7'),'#skF_4'('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_78,c_4226])).

tff(c_4239,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_4237])).

tff(c_4241,plain,(
    k2_struct_0('#skF_6') != '#skF_4'('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_805])).

tff(c_551,plain,(
    ! [B_36] :
      ( r1_tarski(k2_struct_0(B_36),k2_struct_0('#skF_6'))
      | ~ m1_pre_topc(B_36,'#skF_5')
      | ~ l1_pre_topc(B_36)
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_526,c_38])).

tff(c_5733,plain,(
    ! [B_294] :
      ( r1_tarski(k2_struct_0(B_294),k2_struct_0('#skF_6'))
      | ~ m1_pre_topc(B_294,'#skF_5')
      | ~ l1_pre_topc(B_294) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_551])).

tff(c_5753,plain,
    ( r1_tarski('#skF_4'('#skF_5','#skF_7'),k2_struct_0('#skF_6'))
    | ~ m1_pre_topc('#skF_7','#skF_5')
    | ~ l1_pre_topc('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_533,c_5733])).

tff(c_5769,plain,(
    r1_tarski('#skF_4'('#skF_5','#skF_7'),k2_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_82,c_5753])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5773,plain,
    ( k2_struct_0('#skF_6') = '#skF_4'('#skF_5','#skF_7')
    | ~ r1_tarski(k2_struct_0('#skF_6'),'#skF_4'('#skF_5','#skF_7')) ),
    inference(resolution,[status(thm)],[c_5769,c_2])).

tff(c_5776,plain,(
    ~ r1_tarski(k2_struct_0('#skF_6'),'#skF_4'('#skF_5','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_4241,c_5773])).

tff(c_247,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_6',k2_struct_0('#skF_6')))
    | ~ l1_pre_topc('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_244])).

tff(c_255,plain,(
    v1_pre_topc(k1_pre_topc('#skF_6',k2_struct_0('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_247])).

tff(c_4964,plain,(
    ! [A_284,B_285] :
      ( k2_struct_0(k1_pre_topc(A_284,B_285)) = B_285
      | ~ m1_pre_topc(k1_pre_topc(A_284,B_285),A_284)
      | ~ v1_pre_topc(k1_pre_topc(A_284,B_285))
      | ~ m1_subset_1(B_285,k1_zfmisc_1(u1_struct_0(A_284)))
      | ~ l1_pre_topc(A_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4989,plain,
    ( k2_struct_0(k1_pre_topc('#skF_6',k2_struct_0('#skF_6'))) = k2_struct_0('#skF_6')
    | ~ v1_pre_topc(k1_pre_topc('#skF_6',k2_struct_0('#skF_6')))
    | ~ m1_subset_1(k2_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_471,c_4964])).

tff(c_5023,plain,(
    k2_struct_0(k1_pre_topc('#skF_6',k2_struct_0('#skF_6'))) = k2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_88,c_148,c_255,c_4989])).

tff(c_632,plain,(
    ! [B_36] :
      ( r1_tarski(k2_struct_0(B_36),'#skF_4'('#skF_5','#skF_7'))
      | ~ m1_pre_topc(B_36,'#skF_7')
      | ~ l1_pre_topc(B_36)
      | ~ l1_pre_topc('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_533,c_38])).

tff(c_6009,plain,(
    ! [B_309] :
      ( r1_tarski(k2_struct_0(B_309),'#skF_4'('#skF_5','#skF_7'))
      | ~ m1_pre_topc(B_309,'#skF_7')
      | ~ l1_pre_topc(B_309) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_632])).

tff(c_6029,plain,
    ( r1_tarski(k2_struct_0('#skF_6'),'#skF_4'('#skF_5','#skF_7'))
    | ~ m1_pre_topc(k1_pre_topc('#skF_6',k2_struct_0('#skF_6')),'#skF_7')
    | ~ l1_pre_topc(k1_pre_topc('#skF_6',k2_struct_0('#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_5023,c_6009])).

tff(c_6050,plain,
    ( r1_tarski(k2_struct_0('#skF_6'),'#skF_4'('#skF_5','#skF_7'))
    | ~ m1_pre_topc(k1_pre_topc('#skF_6',k2_struct_0('#skF_6')),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_6029])).

tff(c_6051,plain,(
    ~ m1_pre_topc(k1_pre_topc('#skF_6',k2_struct_0('#skF_6')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_5776,c_6050])).

tff(c_6243,plain,
    ( ~ m1_pre_topc(k1_pre_topc('#skF_6',k2_struct_0('#skF_6')),'#skF_6')
    | ~ l1_pre_topc(k1_pre_topc('#skF_6',k2_struct_0('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_6237,c_6051])).

tff(c_6266,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_471,c_6243])).

tff(c_6268,plain,(
    k2_struct_0('#skF_5') != k2_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_353])).

tff(c_6522,plain,(
    k2_struct_0('#skF_6') != '#skF_4'('#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6516,c_6268])).

tff(c_6526,plain,(
    m1_subset_1(k2_struct_0('#skF_6'),k1_zfmisc_1('#skF_4'('#skF_5','#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6516,c_342])).

tff(c_436,plain,(
    ! [B_118] :
      ( m1_pre_topc(k1_pre_topc('#skF_7',B_118),'#skF_7')
      | ~ m1_subset_1(B_118,k1_zfmisc_1(k2_struct_0('#skF_7')))
      | ~ l1_pre_topc('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_428])).

tff(c_447,plain,(
    ! [B_118] :
      ( m1_pre_topc(k1_pre_topc('#skF_7',B_118),'#skF_7')
      | ~ m1_subset_1(B_118,k1_zfmisc_1(k2_struct_0('#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_436])).

tff(c_6682,plain,(
    ! [B_335] :
      ( m1_pre_topc(k1_pre_topc('#skF_7',B_335),'#skF_7')
      | ~ m1_subset_1(B_335,k1_zfmisc_1('#skF_4'('#skF_5','#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6275,c_447])).

tff(c_6690,plain,(
    m1_pre_topc(k1_pre_topc('#skF_7',k2_struct_0('#skF_6')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_6526,c_6682])).

tff(c_6695,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_7',k2_struct_0('#skF_6')))
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_6690,c_54])).

tff(c_6698,plain,(
    l1_pre_topc(k1_pre_topc('#skF_7',k2_struct_0('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_6695])).

tff(c_50,plain,(
    ! [A_54,B_55] :
      ( v1_pre_topc(k1_pre_topc(A_54,B_55))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_6331,plain,(
    ! [B_55] :
      ( v1_pre_topc(k1_pre_topc('#skF_7',B_55))
      | ~ m1_subset_1(B_55,k1_zfmisc_1('#skF_4'('#skF_5','#skF_7')))
      | ~ l1_pre_topc('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6284,c_50])).

tff(c_6670,plain,(
    ! [B_334] :
      ( v1_pre_topc(k1_pre_topc('#skF_7',B_334))
      | ~ m1_subset_1(B_334,k1_zfmisc_1('#skF_4'('#skF_5','#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_6331])).

tff(c_6678,plain,(
    v1_pre_topc(k1_pre_topc('#skF_7',k2_struct_0('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_6526,c_6670])).

tff(c_7358,plain,
    ( k2_struct_0(k1_pre_topc('#skF_7',k2_struct_0('#skF_6'))) = k2_struct_0('#skF_6')
    | ~ v1_pre_topc(k1_pre_topc('#skF_7',k2_struct_0('#skF_6')))
    | ~ m1_subset_1(k2_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_7')))
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_6690,c_7345])).

tff(c_7387,plain,(
    k2_struct_0(k1_pre_topc('#skF_7',k2_struct_0('#skF_6'))) = k2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_6526,c_6284,c_6678,c_7358])).

tff(c_6291,plain,(
    ! [B_36] :
      ( r1_tarski(k2_struct_0(B_36),'#skF_4'('#skF_5','#skF_7'))
      | ~ m1_pre_topc(B_36,'#skF_7')
      | ~ l1_pre_topc(B_36)
      | ~ l1_pre_topc('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6275,c_38])).

tff(c_8870,plain,(
    ! [B_386] :
      ( r1_tarski(k2_struct_0(B_386),'#skF_4'('#skF_5','#skF_7'))
      | ~ m1_pre_topc(B_386,'#skF_7')
      | ~ l1_pre_topc(B_386) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_6291])).

tff(c_8881,plain,
    ( r1_tarski(k2_struct_0('#skF_6'),'#skF_4'('#skF_5','#skF_7'))
    | ~ m1_pre_topc(k1_pre_topc('#skF_7',k2_struct_0('#skF_6')),'#skF_7')
    | ~ l1_pre_topc(k1_pre_topc('#skF_7',k2_struct_0('#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_7387,c_8870])).

tff(c_8900,plain,(
    r1_tarski(k2_struct_0('#skF_6'),'#skF_4'('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6698,c_6690,c_8881])).

tff(c_8910,plain,
    ( k2_struct_0('#skF_6') = '#skF_4'('#skF_5','#skF_7')
    | ~ r1_tarski('#skF_4'('#skF_5','#skF_7'),k2_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_8900,c_2])).

tff(c_8913,plain,(
    ~ r1_tarski('#skF_4'('#skF_5','#skF_7'),k2_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_6522,c_8910])).

tff(c_26767,plain,
    ( ~ m1_pre_topc(k1_pre_topc('#skF_7','#skF_4'('#skF_5','#skF_7')),'#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_26755,c_8913])).

tff(c_26824,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_13690,c_26767])).

tff(c_26825,plain,(
    v1_subset_1('#skF_4'('#skF_5','#skF_7'),k2_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_6515])).

tff(c_6453,plain,(
    ! [A_324,B_325] :
      ( ~ v1_subset_1('#skF_4'(A_324,B_325),u1_struct_0(A_324))
      | v1_tex_2(B_325,A_324)
      | ~ m1_pre_topc(B_325,A_324)
      | ~ l1_pre_topc(A_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_6462,plain,(
    ! [B_325] :
      ( ~ v1_subset_1('#skF_4'('#skF_5',B_325),k2_struct_0('#skF_5'))
      | v1_tex_2(B_325,'#skF_5')
      | ~ m1_pre_topc(B_325,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_6453])).

tff(c_27426,plain,(
    ! [B_724] :
      ( ~ v1_subset_1('#skF_4'('#skF_5',B_724),k2_struct_0('#skF_5'))
      | v1_tex_2(B_724,'#skF_5')
      | ~ m1_pre_topc(B_724,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_6462])).

tff(c_27429,plain,
    ( v1_tex_2('#skF_7','#skF_5')
    | ~ m1_pre_topc('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_26825,c_27426])).

tff(c_27432,plain,(
    v1_tex_2('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_27429])).

tff(c_27434,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_27432])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:45:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.80/7.02  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.80/7.03  
% 15.80/7.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.80/7.04  %$ v1_tex_2 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 15.80/7.04  
% 15.80/7.04  %Foreground sorts:
% 15.80/7.04  
% 15.80/7.04  
% 15.80/7.04  %Background operators:
% 15.80/7.04  
% 15.80/7.04  
% 15.80/7.04  %Foreground operators:
% 15.80/7.04  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 15.80/7.04  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 15.80/7.04  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 15.80/7.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.80/7.04  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 15.80/7.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.80/7.04  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 15.80/7.04  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 15.80/7.04  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 15.80/7.04  tff('#skF_7', type, '#skF_7': $i).
% 15.80/7.04  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 15.80/7.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.80/7.04  tff('#skF_5', type, '#skF_5': $i).
% 15.80/7.04  tff('#skF_6', type, '#skF_6': $i).
% 15.80/7.04  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 15.80/7.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.80/7.04  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 15.80/7.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.80/7.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.80/7.04  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 15.80/7.04  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 15.80/7.04  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 15.80/7.04  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 15.80/7.04  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 15.80/7.04  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 15.80/7.04  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 15.80/7.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.80/7.04  
% 15.80/7.06  tff(f_155, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (((g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) & v1_tex_2(B, A)) => v1_tex_2(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_tex_2)).
% 15.80/7.06  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 15.80/7.06  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 15.80/7.06  tff(f_56, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 15.80/7.06  tff(f_133, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 15.80/7.06  tff(f_33, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 15.80/7.06  tff(f_35, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 15.80/7.06  tff(f_85, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 15.80/7.06  tff(f_112, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 15.80/7.06  tff(f_103, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 15.80/7.06  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((v1_pre_topc(C) & m1_pre_topc(C, A)) => ((C = k1_pre_topc(A, B)) <=> (k2_struct_0(C) = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_pre_topc)).
% 15.80/7.06  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(B, A) <=> (r1_tarski(k2_struct_0(B), k2_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (r2_hidden(C, u1_pre_topc(B)) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & r2_hidden(D, u1_pre_topc(A))) & (C = k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_pre_topc)).
% 15.80/7.06  tff(f_119, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 15.80/7.06  tff(f_140, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 15.80/7.06  tff(f_38, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_subset_1)).
% 15.80/7.06  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.80/7.06  tff(c_76, plain, (~v1_tex_2('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_155])).
% 15.80/7.06  tff(c_82, plain, (m1_pre_topc('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_155])).
% 15.80/7.06  tff(c_86, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_155])).
% 15.80/7.06  tff(c_84, plain, (m1_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_155])).
% 15.80/7.06  tff(c_121, plain, (![B_92, A_93]: (l1_pre_topc(B_92) | ~m1_pre_topc(B_92, A_93) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_96])).
% 15.80/7.06  tff(c_127, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_84, c_121])).
% 15.80/7.06  tff(c_133, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_127])).
% 15.80/7.06  tff(c_124, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_82, c_121])).
% 15.80/7.06  tff(c_130, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_124])).
% 15.80/7.06  tff(c_52, plain, (![A_56]: (l1_struct_0(A_56) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_89])).
% 15.80/7.06  tff(c_107, plain, (![A_90]: (u1_struct_0(A_90)=k2_struct_0(A_90) | ~l1_struct_0(A_90))), inference(cnfTransformation, [status(thm)], [f_56])).
% 15.80/7.06  tff(c_111, plain, (![A_56]: (u1_struct_0(A_56)=k2_struct_0(A_56) | ~l1_pre_topc(A_56))), inference(resolution, [status(thm)], [c_52, c_107])).
% 15.80/7.06  tff(c_144, plain, (u1_struct_0('#skF_7')=k2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_130, c_111])).
% 15.80/7.06  tff(c_6269, plain, (![B_318, A_319]: (u1_struct_0(B_318)='#skF_4'(A_319, B_318) | v1_tex_2(B_318, A_319) | ~m1_pre_topc(B_318, A_319) | ~l1_pre_topc(A_319))), inference(cnfTransformation, [status(thm)], [f_133])).
% 15.80/7.06  tff(c_6272, plain, (u1_struct_0('#skF_7')='#skF_4'('#skF_5', '#skF_7') | ~m1_pre_topc('#skF_7', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_6269, c_76])).
% 15.80/7.06  tff(c_6275, plain, (k2_struct_0('#skF_7')='#skF_4'('#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_144, c_6272])).
% 15.80/7.06  tff(c_6284, plain, (u1_struct_0('#skF_7')='#skF_4'('#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6275, c_144])).
% 15.80/7.06  tff(c_8, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_33])).
% 15.80/7.06  tff(c_10, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.80/7.06  tff(c_88, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 15.80/7.06  tff(c_428, plain, (![A_117, B_118]: (m1_pre_topc(k1_pre_topc(A_117, B_118), A_117) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_pre_topc(A_117))), inference(cnfTransformation, [status(thm)], [f_85])).
% 15.80/7.06  tff(c_451, plain, (![A_119]: (m1_pre_topc(k1_pre_topc(A_119, u1_struct_0(A_119)), A_119) | ~l1_pre_topc(A_119))), inference(resolution, [status(thm)], [c_88, c_428])).
% 15.80/7.06  tff(c_54, plain, (![B_59, A_57]: (l1_pre_topc(B_59) | ~m1_pre_topc(B_59, A_57) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_96])).
% 15.80/7.06  tff(c_469, plain, (![A_119]: (l1_pre_topc(k1_pre_topc(A_119, u1_struct_0(A_119))) | ~l1_pre_topc(A_119))), inference(resolution, [status(thm)], [c_451, c_54])).
% 15.80/7.06  tff(c_6302, plain, (l1_pre_topc(k1_pre_topc('#skF_7', '#skF_4'('#skF_5', '#skF_7'))) | ~l1_pre_topc('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_6284, c_469])).
% 15.80/7.06  tff(c_6344, plain, (l1_pre_topc(k1_pre_topc('#skF_7', '#skF_4'('#skF_5', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_6302])).
% 15.80/7.06  tff(c_450, plain, (![A_117]: (m1_pre_topc(k1_pre_topc(A_117, u1_struct_0(A_117)), A_117) | ~l1_pre_topc(A_117))), inference(resolution, [status(thm)], [c_88, c_428])).
% 15.80/7.06  tff(c_6305, plain, (m1_pre_topc(k1_pre_topc('#skF_7', '#skF_4'('#skF_5', '#skF_7')), '#skF_7') | ~l1_pre_topc('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_6284, c_450])).
% 15.80/7.06  tff(c_6346, plain, (m1_pre_topc(k1_pre_topc('#skF_7', '#skF_4'('#skF_5', '#skF_7')), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_6305])).
% 15.80/7.06  tff(c_6376, plain, (![A_321, B_322]: (m1_pre_topc(A_321, g1_pre_topc(u1_struct_0(B_322), u1_pre_topc(B_322))) | ~m1_pre_topc(A_321, B_322) | ~l1_pre_topc(B_322) | ~l1_pre_topc(A_321))), inference(cnfTransformation, [status(thm)], [f_112])).
% 15.80/7.06  tff(c_6385, plain, (![A_321]: (m1_pre_topc(A_321, g1_pre_topc('#skF_4'('#skF_5', '#skF_7'), u1_pre_topc('#skF_7'))) | ~m1_pre_topc(A_321, '#skF_7') | ~l1_pre_topc('#skF_7') | ~l1_pre_topc(A_321))), inference(superposition, [status(thm), theory('equality')], [c_6284, c_6376])).
% 15.80/7.06  tff(c_13532, plain, (![A_501]: (m1_pre_topc(A_501, g1_pre_topc('#skF_4'('#skF_5', '#skF_7'), u1_pre_topc('#skF_7'))) | ~m1_pre_topc(A_501, '#skF_7') | ~l1_pre_topc(A_501))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_6385])).
% 15.80/7.06  tff(c_148, plain, (u1_struct_0('#skF_6')=k2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_133, c_111])).
% 15.80/7.06  tff(c_80, plain, (g1_pre_topc(u1_struct_0('#skF_7'), u1_pre_topc('#skF_7'))=g1_pre_topc(u1_struct_0('#skF_6'), u1_pre_topc('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_155])).
% 15.80/7.06  tff(c_149, plain, (g1_pre_topc(u1_struct_0('#skF_6'), u1_pre_topc('#skF_6'))=g1_pre_topc(k2_struct_0('#skF_7'), u1_pre_topc('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_80])).
% 15.80/7.06  tff(c_158, plain, (g1_pre_topc(k2_struct_0('#skF_7'), u1_pre_topc('#skF_7'))=g1_pre_topc(k2_struct_0('#skF_6'), u1_pre_topc('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_149])).
% 15.80/7.06  tff(c_6283, plain, (g1_pre_topc(k2_struct_0('#skF_6'), u1_pre_topc('#skF_6'))=g1_pre_topc('#skF_4'('#skF_5', '#skF_7'), u1_pre_topc('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_6275, c_158])).
% 15.80/7.06  tff(c_284, plain, (![B_106, A_107]: (m1_pre_topc(B_106, A_107) | ~m1_pre_topc(B_106, g1_pre_topc(u1_struct_0(A_107), u1_pre_topc(A_107))) | ~l1_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_103])).
% 15.80/7.06  tff(c_287, plain, (![B_106]: (m1_pre_topc(B_106, '#skF_6') | ~m1_pre_topc(B_106, g1_pre_topc(k2_struct_0('#skF_6'), u1_pre_topc('#skF_6'))) | ~l1_pre_topc('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_148, c_284])).
% 15.80/7.06  tff(c_295, plain, (![B_106]: (m1_pre_topc(B_106, '#skF_6') | ~m1_pre_topc(B_106, g1_pre_topc(k2_struct_0('#skF_6'), u1_pre_topc('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_287])).
% 15.80/7.06  tff(c_6727, plain, (![B_106]: (m1_pre_topc(B_106, '#skF_6') | ~m1_pre_topc(B_106, g1_pre_topc('#skF_4'('#skF_5', '#skF_7'), u1_pre_topc('#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_6283, c_295])).
% 15.80/7.06  tff(c_13619, plain, (![A_505]: (m1_pre_topc(A_505, '#skF_6') | ~m1_pre_topc(A_505, '#skF_7') | ~l1_pre_topc(A_505))), inference(resolution, [status(thm)], [c_13532, c_6727])).
% 15.80/7.06  tff(c_13658, plain, (m1_pre_topc(k1_pre_topc('#skF_7', '#skF_4'('#skF_5', '#skF_7')), '#skF_6') | ~l1_pre_topc(k1_pre_topc('#skF_7', '#skF_4'('#skF_5', '#skF_7')))), inference(resolution, [status(thm)], [c_6346, c_13619])).
% 15.80/7.06  tff(c_13690, plain, (m1_pre_topc(k1_pre_topc('#skF_7', '#skF_4'('#skF_5', '#skF_7')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6344, c_13658])).
% 15.80/7.06  tff(c_219, plain, (![A_101, B_102]: (v1_pre_topc(k1_pre_topc(A_101, B_102)) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_85])).
% 15.80/7.06  tff(c_244, plain, (![A_103]: (v1_pre_topc(k1_pre_topc(A_103, u1_struct_0(A_103))) | ~l1_pre_topc(A_103))), inference(resolution, [status(thm)], [c_88, c_219])).
% 15.80/7.06  tff(c_250, plain, (v1_pre_topc(k1_pre_topc('#skF_7', k2_struct_0('#skF_7'))) | ~l1_pre_topc('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_144, c_244])).
% 15.80/7.06  tff(c_257, plain, (v1_pre_topc(k1_pre_topc('#skF_7', k2_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_250])).
% 15.80/7.06  tff(c_6282, plain, (v1_pre_topc(k1_pre_topc('#skF_7', '#skF_4'('#skF_5', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_6275, c_257])).
% 15.80/7.06  tff(c_7345, plain, (![A_355, B_356]: (k2_struct_0(k1_pre_topc(A_355, B_356))=B_356 | ~m1_pre_topc(k1_pre_topc(A_355, B_356), A_355) | ~v1_pre_topc(k1_pre_topc(A_355, B_356)) | ~m1_subset_1(B_356, k1_zfmisc_1(u1_struct_0(A_355))) | ~l1_pre_topc(A_355))), inference(cnfTransformation, [status(thm)], [f_52])).
% 15.80/7.06  tff(c_7366, plain, (k2_struct_0(k1_pre_topc('#skF_7', '#skF_4'('#skF_5', '#skF_7')))='#skF_4'('#skF_5', '#skF_7') | ~v1_pre_topc(k1_pre_topc('#skF_7', '#skF_4'('#skF_5', '#skF_7'))) | ~m1_subset_1('#skF_4'('#skF_5', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_6346, c_7345])).
% 15.80/7.06  tff(c_7399, plain, (k2_struct_0(k1_pre_topc('#skF_7', '#skF_4'('#skF_5', '#skF_7')))='#skF_4'('#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_88, c_6284, c_6282, c_7366])).
% 15.80/7.06  tff(c_38, plain, (![B_36, A_14]: (r1_tarski(k2_struct_0(B_36), k2_struct_0(A_14)) | ~m1_pre_topc(B_36, A_14) | ~l1_pre_topc(B_36) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_77])).
% 15.80/7.06  tff(c_7616, plain, (![A_14]: (r1_tarski('#skF_4'('#skF_5', '#skF_7'), k2_struct_0(A_14)) | ~m1_pre_topc(k1_pre_topc('#skF_7', '#skF_4'('#skF_5', '#skF_7')), A_14) | ~l1_pre_topc(k1_pre_topc('#skF_7', '#skF_4'('#skF_5', '#skF_7'))) | ~l1_pre_topc(A_14))), inference(superposition, [status(thm), theory('equality')], [c_7399, c_38])).
% 15.80/7.06  tff(c_26755, plain, (![A_698]: (r1_tarski('#skF_4'('#skF_5', '#skF_7'), k2_struct_0(A_698)) | ~m1_pre_topc(k1_pre_topc('#skF_7', '#skF_4'('#skF_5', '#skF_7')), A_698) | ~l1_pre_topc(A_698))), inference(demodulation, [status(thm), theory('equality')], [c_6344, c_7616])).
% 15.80/7.06  tff(c_112, plain, (![A_91]: (u1_struct_0(A_91)=k2_struct_0(A_91) | ~l1_pre_topc(A_91))), inference(resolution, [status(thm)], [c_52, c_107])).
% 15.80/7.06  tff(c_116, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_86, c_112])).
% 15.80/7.06  tff(c_175, plain, (![B_98, A_99]: (m1_subset_1(u1_struct_0(B_98), k1_zfmisc_1(u1_struct_0(A_99))) | ~m1_pre_topc(B_98, A_99) | ~l1_pre_topc(A_99))), inference(cnfTransformation, [status(thm)], [f_119])).
% 15.80/7.06  tff(c_196, plain, (![B_98]: (m1_subset_1(u1_struct_0(B_98), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_pre_topc(B_98, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_175])).
% 15.80/7.06  tff(c_323, plain, (![B_110]: (m1_subset_1(u1_struct_0(B_110), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_pre_topc(B_110, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_196])).
% 15.80/7.06  tff(c_335, plain, (m1_subset_1(k2_struct_0('#skF_7'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_7', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_144, c_323])).
% 15.80/7.06  tff(c_344, plain, (m1_subset_1(k2_struct_0('#skF_7'), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_335])).
% 15.80/7.06  tff(c_72, plain, (![B_80, A_79]: (v1_subset_1(B_80, A_79) | B_80=A_79 | ~m1_subset_1(B_80, k1_zfmisc_1(A_79)))), inference(cnfTransformation, [status(thm)], [f_140])).
% 15.80/7.06  tff(c_361, plain, (v1_subset_1(k2_struct_0('#skF_7'), k2_struct_0('#skF_5')) | k2_struct_0('#skF_7')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_344, c_72])).
% 15.80/7.06  tff(c_6515, plain, (v1_subset_1('#skF_4'('#skF_5', '#skF_7'), k2_struct_0('#skF_5')) | k2_struct_0('#skF_5')='#skF_4'('#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6275, c_6275, c_361])).
% 15.80/7.06  tff(c_6516, plain, (k2_struct_0('#skF_5')='#skF_4'('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_6515])).
% 15.80/7.06  tff(c_461, plain, (m1_pre_topc(k1_pre_topc('#skF_6', k2_struct_0('#skF_6')), '#skF_6') | ~l1_pre_topc('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_148, c_451])).
% 15.80/7.06  tff(c_471, plain, (m1_pre_topc(k1_pre_topc('#skF_6', k2_struct_0('#skF_6')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_461])).
% 15.80/7.06  tff(c_478, plain, (l1_pre_topc(k1_pre_topc('#skF_6', k2_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_471, c_54])).
% 15.80/7.06  tff(c_481, plain, (l1_pre_topc(k1_pre_topc('#skF_6', k2_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_478])).
% 15.80/7.06  tff(c_527, plain, (![B_121, A_122]: (u1_struct_0(B_121)='#skF_4'(A_122, B_121) | v1_tex_2(B_121, A_122) | ~m1_pre_topc(B_121, A_122) | ~l1_pre_topc(A_122))), inference(cnfTransformation, [status(thm)], [f_133])).
% 15.80/7.06  tff(c_530, plain, (u1_struct_0('#skF_7')='#skF_4'('#skF_5', '#skF_7') | ~m1_pre_topc('#skF_7', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_527, c_76])).
% 15.80/7.06  tff(c_533, plain, (k2_struct_0('#skF_7')='#skF_4'('#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_144, c_530])).
% 15.80/7.06  tff(c_624, plain, (g1_pre_topc(k2_struct_0('#skF_6'), u1_pre_topc('#skF_6'))=g1_pre_topc('#skF_4'('#skF_5', '#skF_7'), u1_pre_topc('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_533, c_158])).
% 15.80/7.06  tff(c_762, plain, (![A_127, B_128]: (m1_pre_topc(A_127, g1_pre_topc(u1_struct_0(B_128), u1_pre_topc(B_128))) | ~m1_pre_topc(A_127, B_128) | ~l1_pre_topc(B_128) | ~l1_pre_topc(A_127))), inference(cnfTransformation, [status(thm)], [f_112])).
% 15.80/7.06  tff(c_777, plain, (![A_127]: (m1_pre_topc(A_127, g1_pre_topc(k2_struct_0('#skF_6'), u1_pre_topc('#skF_6'))) | ~m1_pre_topc(A_127, '#skF_6') | ~l1_pre_topc('#skF_6') | ~l1_pre_topc(A_127))), inference(superposition, [status(thm), theory('equality')], [c_148, c_762])).
% 15.80/7.06  tff(c_785, plain, (![A_127]: (m1_pre_topc(A_127, g1_pre_topc(k2_struct_0('#skF_6'), u1_pre_topc('#skF_6'))) | ~m1_pre_topc(A_127, '#skF_6') | ~l1_pre_topc(A_127))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_777])).
% 15.80/7.06  tff(c_6215, plain, (![A_316]: (m1_pre_topc(A_316, g1_pre_topc('#skF_4'('#skF_5', '#skF_7'), u1_pre_topc('#skF_7'))) | ~m1_pre_topc(A_316, '#skF_6') | ~l1_pre_topc(A_316))), inference(demodulation, [status(thm), theory('equality')], [c_624, c_785])).
% 15.80/7.06  tff(c_290, plain, (![B_106]: (m1_pre_topc(B_106, '#skF_7') | ~m1_pre_topc(B_106, g1_pre_topc(k2_struct_0('#skF_7'), u1_pre_topc('#skF_7'))) | ~l1_pre_topc('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_144, c_284])).
% 15.80/7.06  tff(c_297, plain, (![B_106]: (m1_pre_topc(B_106, '#skF_7') | ~m1_pre_topc(B_106, g1_pre_topc(k2_struct_0('#skF_6'), u1_pre_topc('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_158, c_290])).
% 15.80/7.06  tff(c_4792, plain, (![B_106]: (m1_pre_topc(B_106, '#skF_7') | ~m1_pre_topc(B_106, g1_pre_topc('#skF_4'('#skF_5', '#skF_7'), u1_pre_topc('#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_624, c_297])).
% 15.80/7.06  tff(c_6237, plain, (![A_317]: (m1_pre_topc(A_317, '#skF_7') | ~m1_pre_topc(A_317, '#skF_6') | ~l1_pre_topc(A_317))), inference(resolution, [status(thm)], [c_6215, c_4792])).
% 15.80/7.06  tff(c_12, plain, (![A_5]: (~v1_subset_1(k2_subset_1(A_5), A_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 15.80/7.06  tff(c_87, plain, (![A_5]: (~v1_subset_1(A_5, A_5))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_12])).
% 15.80/7.06  tff(c_78, plain, (v1_tex_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_155])).
% 15.80/7.06  tff(c_332, plain, (m1_subset_1(k2_struct_0('#skF_6'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_148, c_323])).
% 15.80/7.06  tff(c_342, plain, (m1_subset_1(k2_struct_0('#skF_6'), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_332])).
% 15.80/7.06  tff(c_353, plain, (v1_subset_1(k2_struct_0('#skF_6'), k2_struct_0('#skF_5')) | k2_struct_0('#skF_5')=k2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_342, c_72])).
% 15.80/7.06  tff(c_526, plain, (k2_struct_0('#skF_5')=k2_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_353])).
% 15.80/7.06  tff(c_805, plain, (v1_subset_1('#skF_4'('#skF_5', '#skF_7'), k2_struct_0('#skF_6')) | k2_struct_0('#skF_6')='#skF_4'('#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_533, c_526, c_533, c_526, c_361])).
% 15.80/7.06  tff(c_806, plain, (k2_struct_0('#skF_6')='#skF_4'('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_805])).
% 15.80/7.06  tff(c_821, plain, (u1_struct_0('#skF_6')='#skF_4'('#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_806, c_148])).
% 15.80/7.06  tff(c_542, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_526, c_116])).
% 15.80/7.06  tff(c_813, plain, (u1_struct_0('#skF_5')='#skF_4'('#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_806, c_542])).
% 15.80/7.06  tff(c_62, plain, (![B_68, A_66]: (m1_subset_1(u1_struct_0(B_68), k1_zfmisc_1(u1_struct_0(A_66))) | ~m1_pre_topc(B_68, A_66) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_119])).
% 15.80/7.06  tff(c_1172, plain, (![B_143, A_144]: (v1_subset_1(u1_struct_0(B_143), u1_struct_0(A_144)) | ~m1_subset_1(u1_struct_0(B_143), k1_zfmisc_1(u1_struct_0(A_144))) | ~v1_tex_2(B_143, A_144) | ~m1_pre_topc(B_143, A_144) | ~l1_pre_topc(A_144))), inference(cnfTransformation, [status(thm)], [f_133])).
% 15.80/7.06  tff(c_3872, plain, (![B_236, A_237]: (v1_subset_1(u1_struct_0(B_236), u1_struct_0(A_237)) | ~v1_tex_2(B_236, A_237) | ~m1_pre_topc(B_236, A_237) | ~l1_pre_topc(A_237))), inference(resolution, [status(thm)], [c_62, c_1172])).
% 15.80/7.06  tff(c_3906, plain, (![B_236]: (v1_subset_1(u1_struct_0(B_236), '#skF_4'('#skF_5', '#skF_7')) | ~v1_tex_2(B_236, '#skF_5') | ~m1_pre_topc(B_236, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_813, c_3872])).
% 15.80/7.06  tff(c_4208, plain, (![B_247]: (v1_subset_1(u1_struct_0(B_247), '#skF_4'('#skF_5', '#skF_7')) | ~v1_tex_2(B_247, '#skF_5') | ~m1_pre_topc(B_247, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_3906])).
% 15.80/7.06  tff(c_4226, plain, (v1_subset_1('#skF_4'('#skF_5', '#skF_7'), '#skF_4'('#skF_5', '#skF_7')) | ~v1_tex_2('#skF_6', '#skF_5') | ~m1_pre_topc('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_821, c_4208])).
% 15.80/7.06  tff(c_4237, plain, (v1_subset_1('#skF_4'('#skF_5', '#skF_7'), '#skF_4'('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_78, c_4226])).
% 15.80/7.06  tff(c_4239, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_4237])).
% 15.80/7.06  tff(c_4241, plain, (k2_struct_0('#skF_6')!='#skF_4'('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_805])).
% 15.80/7.06  tff(c_551, plain, (![B_36]: (r1_tarski(k2_struct_0(B_36), k2_struct_0('#skF_6')) | ~m1_pre_topc(B_36, '#skF_5') | ~l1_pre_topc(B_36) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_526, c_38])).
% 15.80/7.06  tff(c_5733, plain, (![B_294]: (r1_tarski(k2_struct_0(B_294), k2_struct_0('#skF_6')) | ~m1_pre_topc(B_294, '#skF_5') | ~l1_pre_topc(B_294))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_551])).
% 15.80/7.06  tff(c_5753, plain, (r1_tarski('#skF_4'('#skF_5', '#skF_7'), k2_struct_0('#skF_6')) | ~m1_pre_topc('#skF_7', '#skF_5') | ~l1_pre_topc('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_533, c_5733])).
% 15.80/7.06  tff(c_5769, plain, (r1_tarski('#skF_4'('#skF_5', '#skF_7'), k2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_82, c_5753])).
% 15.80/7.06  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.80/7.06  tff(c_5773, plain, (k2_struct_0('#skF_6')='#skF_4'('#skF_5', '#skF_7') | ~r1_tarski(k2_struct_0('#skF_6'), '#skF_4'('#skF_5', '#skF_7'))), inference(resolution, [status(thm)], [c_5769, c_2])).
% 15.80/7.06  tff(c_5776, plain, (~r1_tarski(k2_struct_0('#skF_6'), '#skF_4'('#skF_5', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_4241, c_5773])).
% 15.80/7.06  tff(c_247, plain, (v1_pre_topc(k1_pre_topc('#skF_6', k2_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_148, c_244])).
% 15.80/7.06  tff(c_255, plain, (v1_pre_topc(k1_pre_topc('#skF_6', k2_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_247])).
% 15.80/7.06  tff(c_4964, plain, (![A_284, B_285]: (k2_struct_0(k1_pre_topc(A_284, B_285))=B_285 | ~m1_pre_topc(k1_pre_topc(A_284, B_285), A_284) | ~v1_pre_topc(k1_pre_topc(A_284, B_285)) | ~m1_subset_1(B_285, k1_zfmisc_1(u1_struct_0(A_284))) | ~l1_pre_topc(A_284))), inference(cnfTransformation, [status(thm)], [f_52])).
% 15.80/7.06  tff(c_4989, plain, (k2_struct_0(k1_pre_topc('#skF_6', k2_struct_0('#skF_6')))=k2_struct_0('#skF_6') | ~v1_pre_topc(k1_pre_topc('#skF_6', k2_struct_0('#skF_6'))) | ~m1_subset_1(k2_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_471, c_4964])).
% 15.80/7.06  tff(c_5023, plain, (k2_struct_0(k1_pre_topc('#skF_6', k2_struct_0('#skF_6')))=k2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_88, c_148, c_255, c_4989])).
% 15.80/7.06  tff(c_632, plain, (![B_36]: (r1_tarski(k2_struct_0(B_36), '#skF_4'('#skF_5', '#skF_7')) | ~m1_pre_topc(B_36, '#skF_7') | ~l1_pre_topc(B_36) | ~l1_pre_topc('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_533, c_38])).
% 15.80/7.06  tff(c_6009, plain, (![B_309]: (r1_tarski(k2_struct_0(B_309), '#skF_4'('#skF_5', '#skF_7')) | ~m1_pre_topc(B_309, '#skF_7') | ~l1_pre_topc(B_309))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_632])).
% 15.80/7.06  tff(c_6029, plain, (r1_tarski(k2_struct_0('#skF_6'), '#skF_4'('#skF_5', '#skF_7')) | ~m1_pre_topc(k1_pre_topc('#skF_6', k2_struct_0('#skF_6')), '#skF_7') | ~l1_pre_topc(k1_pre_topc('#skF_6', k2_struct_0('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_5023, c_6009])).
% 15.80/7.06  tff(c_6050, plain, (r1_tarski(k2_struct_0('#skF_6'), '#skF_4'('#skF_5', '#skF_7')) | ~m1_pre_topc(k1_pre_topc('#skF_6', k2_struct_0('#skF_6')), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_481, c_6029])).
% 15.80/7.06  tff(c_6051, plain, (~m1_pre_topc(k1_pre_topc('#skF_6', k2_struct_0('#skF_6')), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_5776, c_6050])).
% 15.80/7.06  tff(c_6243, plain, (~m1_pre_topc(k1_pre_topc('#skF_6', k2_struct_0('#skF_6')), '#skF_6') | ~l1_pre_topc(k1_pre_topc('#skF_6', k2_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_6237, c_6051])).
% 15.80/7.06  tff(c_6266, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_481, c_471, c_6243])).
% 15.80/7.06  tff(c_6268, plain, (k2_struct_0('#skF_5')!=k2_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_353])).
% 15.80/7.06  tff(c_6522, plain, (k2_struct_0('#skF_6')!='#skF_4'('#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6516, c_6268])).
% 15.80/7.06  tff(c_6526, plain, (m1_subset_1(k2_struct_0('#skF_6'), k1_zfmisc_1('#skF_4'('#skF_5', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_6516, c_342])).
% 15.80/7.06  tff(c_436, plain, (![B_118]: (m1_pre_topc(k1_pre_topc('#skF_7', B_118), '#skF_7') | ~m1_subset_1(B_118, k1_zfmisc_1(k2_struct_0('#skF_7'))) | ~l1_pre_topc('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_144, c_428])).
% 15.80/7.06  tff(c_447, plain, (![B_118]: (m1_pre_topc(k1_pre_topc('#skF_7', B_118), '#skF_7') | ~m1_subset_1(B_118, k1_zfmisc_1(k2_struct_0('#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_436])).
% 15.80/7.06  tff(c_6682, plain, (![B_335]: (m1_pre_topc(k1_pre_topc('#skF_7', B_335), '#skF_7') | ~m1_subset_1(B_335, k1_zfmisc_1('#skF_4'('#skF_5', '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_6275, c_447])).
% 15.80/7.06  tff(c_6690, plain, (m1_pre_topc(k1_pre_topc('#skF_7', k2_struct_0('#skF_6')), '#skF_7')), inference(resolution, [status(thm)], [c_6526, c_6682])).
% 15.80/7.06  tff(c_6695, plain, (l1_pre_topc(k1_pre_topc('#skF_7', k2_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_6690, c_54])).
% 15.80/7.06  tff(c_6698, plain, (l1_pre_topc(k1_pre_topc('#skF_7', k2_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_6695])).
% 15.80/7.06  tff(c_50, plain, (![A_54, B_55]: (v1_pre_topc(k1_pre_topc(A_54, B_55)) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_85])).
% 15.80/7.06  tff(c_6331, plain, (![B_55]: (v1_pre_topc(k1_pre_topc('#skF_7', B_55)) | ~m1_subset_1(B_55, k1_zfmisc_1('#skF_4'('#skF_5', '#skF_7'))) | ~l1_pre_topc('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_6284, c_50])).
% 15.80/7.06  tff(c_6670, plain, (![B_334]: (v1_pre_topc(k1_pre_topc('#skF_7', B_334)) | ~m1_subset_1(B_334, k1_zfmisc_1('#skF_4'('#skF_5', '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_6331])).
% 15.80/7.06  tff(c_6678, plain, (v1_pre_topc(k1_pre_topc('#skF_7', k2_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_6526, c_6670])).
% 15.80/7.06  tff(c_7358, plain, (k2_struct_0(k1_pre_topc('#skF_7', k2_struct_0('#skF_6')))=k2_struct_0('#skF_6') | ~v1_pre_topc(k1_pre_topc('#skF_7', k2_struct_0('#skF_6'))) | ~m1_subset_1(k2_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_6690, c_7345])).
% 15.80/7.06  tff(c_7387, plain, (k2_struct_0(k1_pre_topc('#skF_7', k2_struct_0('#skF_6')))=k2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_6526, c_6284, c_6678, c_7358])).
% 15.80/7.06  tff(c_6291, plain, (![B_36]: (r1_tarski(k2_struct_0(B_36), '#skF_4'('#skF_5', '#skF_7')) | ~m1_pre_topc(B_36, '#skF_7') | ~l1_pre_topc(B_36) | ~l1_pre_topc('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_6275, c_38])).
% 15.80/7.06  tff(c_8870, plain, (![B_386]: (r1_tarski(k2_struct_0(B_386), '#skF_4'('#skF_5', '#skF_7')) | ~m1_pre_topc(B_386, '#skF_7') | ~l1_pre_topc(B_386))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_6291])).
% 15.80/7.06  tff(c_8881, plain, (r1_tarski(k2_struct_0('#skF_6'), '#skF_4'('#skF_5', '#skF_7')) | ~m1_pre_topc(k1_pre_topc('#skF_7', k2_struct_0('#skF_6')), '#skF_7') | ~l1_pre_topc(k1_pre_topc('#skF_7', k2_struct_0('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_7387, c_8870])).
% 15.80/7.06  tff(c_8900, plain, (r1_tarski(k2_struct_0('#skF_6'), '#skF_4'('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_6698, c_6690, c_8881])).
% 15.80/7.06  tff(c_8910, plain, (k2_struct_0('#skF_6')='#skF_4'('#skF_5', '#skF_7') | ~r1_tarski('#skF_4'('#skF_5', '#skF_7'), k2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_8900, c_2])).
% 15.80/7.06  tff(c_8913, plain, (~r1_tarski('#skF_4'('#skF_5', '#skF_7'), k2_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_6522, c_8910])).
% 15.80/7.06  tff(c_26767, plain, (~m1_pre_topc(k1_pre_topc('#skF_7', '#skF_4'('#skF_5', '#skF_7')), '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_26755, c_8913])).
% 15.80/7.06  tff(c_26824, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_133, c_13690, c_26767])).
% 15.80/7.06  tff(c_26825, plain, (v1_subset_1('#skF_4'('#skF_5', '#skF_7'), k2_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_6515])).
% 15.80/7.06  tff(c_6453, plain, (![A_324, B_325]: (~v1_subset_1('#skF_4'(A_324, B_325), u1_struct_0(A_324)) | v1_tex_2(B_325, A_324) | ~m1_pre_topc(B_325, A_324) | ~l1_pre_topc(A_324))), inference(cnfTransformation, [status(thm)], [f_133])).
% 15.80/7.06  tff(c_6462, plain, (![B_325]: (~v1_subset_1('#skF_4'('#skF_5', B_325), k2_struct_0('#skF_5')) | v1_tex_2(B_325, '#skF_5') | ~m1_pre_topc(B_325, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_6453])).
% 15.80/7.06  tff(c_27426, plain, (![B_724]: (~v1_subset_1('#skF_4'('#skF_5', B_724), k2_struct_0('#skF_5')) | v1_tex_2(B_724, '#skF_5') | ~m1_pre_topc(B_724, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_6462])).
% 15.80/7.06  tff(c_27429, plain, (v1_tex_2('#skF_7', '#skF_5') | ~m1_pre_topc('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_26825, c_27426])).
% 15.80/7.06  tff(c_27432, plain, (v1_tex_2('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_27429])).
% 15.80/7.06  tff(c_27434, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_27432])).
% 15.80/7.06  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.80/7.06  
% 15.80/7.06  Inference rules
% 15.80/7.06  ----------------------
% 15.80/7.06  #Ref     : 0
% 15.80/7.06  #Sup     : 6271
% 15.80/7.06  #Fact    : 0
% 15.80/7.06  #Define  : 0
% 15.80/7.06  #Split   : 33
% 15.80/7.06  #Chain   : 0
% 15.80/7.06  #Close   : 0
% 15.80/7.06  
% 15.80/7.06  Ordering : KBO
% 15.80/7.06  
% 15.80/7.06  Simplification rules
% 15.80/7.06  ----------------------
% 15.80/7.06  #Subsume      : 668
% 15.80/7.06  #Demod        : 7031
% 15.80/7.06  #Tautology    : 1411
% 15.80/7.06  #SimpNegUnit  : 331
% 15.80/7.06  #BackRed      : 78
% 15.80/7.06  
% 15.80/7.06  #Partial instantiations: 0
% 15.80/7.06  #Strategies tried      : 1
% 15.80/7.06  
% 15.80/7.06  Timing (in seconds)
% 15.80/7.06  ----------------------
% 15.80/7.07  Preprocessing        : 0.59
% 15.80/7.07  Parsing              : 0.28
% 15.80/7.07  CNF conversion       : 0.05
% 15.80/7.07  Main loop            : 5.63
% 15.80/7.07  Inferencing          : 1.23
% 15.80/7.07  Reduction            : 2.39
% 15.80/7.07  Demodulation         : 1.83
% 15.80/7.07  BG Simplification    : 0.15
% 15.80/7.07  Subsumption          : 1.52
% 15.80/7.07  Abstraction          : 0.18
% 15.80/7.07  MUC search           : 0.00
% 15.80/7.07  Cooper               : 0.00
% 15.80/7.07  Total                : 6.28
% 15.80/7.07  Index Insertion      : 0.00
% 15.80/7.07  Index Deletion       : 0.00
% 15.80/7.07  Index Matching       : 0.00
% 15.80/7.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
