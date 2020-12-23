%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:59 EST 2020

% Result     : Theorem 5.26s
% Output     : CNFRefutation 5.42s
% Verified   : 
% Statistics : Number of formulae       :  234 (5843 expanded)
%              Number of leaves         :   37 (1954 expanded)
%              Depth                    :   35
%              Number of atoms          :  613 (17315 expanded)
%              Number of equality atoms :  101 (3030 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tsep_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k8_tmap_1 > k5_tmap_1 > k1_tops_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k8_tmap_1,type,(
    k8_tmap_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_tmap_1,type,(
    k5_tmap_1: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_158,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ( ( v1_tsep_1(B,A)
                & m1_pre_topc(B,A) )
            <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k8_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_tmap_1)).

tff(f_138,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_134,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_pre_topc(k8_tmap_1(A,B))
        & v2_pre_topc(k8_tmap_1(A,B))
        & l1_pre_topc(k8_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_127,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ( u1_struct_0(k8_tmap_1(A,B)) = u1_struct_0(A)
            & ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => u1_pre_topc(k8_tmap_1(A,B)) = k5_tmap_1(A,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_tmap_1)).

tff(f_105,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,u1_pre_topc(A))
          <=> u1_pre_topc(A) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tsep_1(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tsep_1)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_40,plain,(
    ! [A_35] :
      ( m1_pre_topc(A_35,A_35)
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_10,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_68,plain,(
    ! [A_39] :
      ( u1_struct_0(A_39) = k2_struct_0(A_39)
      | ~ l1_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_73,plain,(
    ! [A_40] :
      ( u1_struct_0(A_40) = k2_struct_0(A_40)
      | ~ l1_pre_topc(A_40) ) ),
    inference(resolution,[status(thm)],[c_10,c_68])).

tff(c_77,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_73])).

tff(c_1661,plain,(
    ! [B_135,A_136] :
      ( m1_subset_1(u1_struct_0(B_135),k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ m1_pre_topc(B_135,A_136)
      | ~ l1_pre_topc(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1667,plain,(
    ! [B_135] :
      ( m1_subset_1(u1_struct_0(B_135),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_135,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_1661])).

tff(c_1670,plain,(
    ! [B_137] :
      ( m1_subset_1(u1_struct_0(B_137),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_137,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1667])).

tff(c_1673,plain,
    ( m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_1670])).

tff(c_1674,plain,(
    ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1673])).

tff(c_1677,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_1674])).

tff(c_1681,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1677])).

tff(c_1683,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1673])).

tff(c_28,plain,(
    ! [A_20,B_21] :
      ( v1_pre_topc(k8_tmap_1(A_20,B_21))
      | ~ m1_pre_topc(B_21,A_20)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_24,plain,(
    ! [A_20,B_21] :
      ( l1_pre_topc(k8_tmap_1(A_20,B_21))
      | ~ m1_pre_topc(B_21,A_20)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1682,plain,(
    m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1673])).

tff(c_1701,plain,(
    ! [B_149,A_150] :
      ( r2_hidden(B_149,u1_pre_topc(A_150))
      | ~ v3_pre_topc(B_149,A_150)
      | ~ m1_subset_1(B_149,k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ l1_pre_topc(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1710,plain,(
    ! [B_149] :
      ( r2_hidden(B_149,u1_pre_topc('#skF_2'))
      | ~ v3_pre_topc(B_149,'#skF_2')
      | ~ m1_subset_1(B_149,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_1701])).

tff(c_1715,plain,(
    ! [B_151] :
      ( r2_hidden(B_151,u1_pre_topc('#skF_2'))
      | ~ v3_pre_topc(B_151,'#skF_2')
      | ~ m1_subset_1(B_151,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1710])).

tff(c_1722,plain,
    ( r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1682,c_1715])).

tff(c_1724,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1722])).

tff(c_14,plain,(
    ! [A_9] :
      ( k1_tops_1(A_9,k2_struct_0(A_9)) = k2_struct_0(A_9)
      | ~ l1_pre_topc(A_9)
      | ~ v2_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1731,plain,(
    ! [A_153,B_154] :
      ( v3_pre_topc(k1_tops_1(A_153,B_154),A_153)
      | ~ m1_subset_1(B_154,k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ l1_pre_topc(A_153)
      | ~ v2_pre_topc(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1737,plain,(
    ! [B_154] :
      ( v3_pre_topc(k1_tops_1('#skF_2',B_154),'#skF_2')
      | ~ m1_subset_1(B_154,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_1731])).

tff(c_1742,plain,(
    ! [B_155] :
      ( v3_pre_topc(k1_tops_1('#skF_2',B_155),'#skF_2')
      | ~ m1_subset_1(B_155,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1737])).

tff(c_1749,plain,(
    v3_pre_topc(k1_tops_1('#skF_2',k2_struct_0('#skF_2')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1682,c_1742])).

tff(c_1767,plain,
    ( v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1749])).

tff(c_1769,plain,(
    v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1767])).

tff(c_1771,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1724,c_1769])).

tff(c_1772,plain,(
    r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1722])).

tff(c_38,plain,(
    ! [B_34,A_32] :
      ( m1_subset_1(u1_struct_0(B_34),k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ m1_pre_topc(B_34,A_32)
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2311,plain,(
    ! [A_210,B_211] :
      ( k5_tmap_1(A_210,u1_struct_0(B_211)) = u1_pre_topc(k8_tmap_1(A_210,B_211))
      | ~ m1_subset_1(u1_struct_0(B_211),k1_zfmisc_1(u1_struct_0(A_210)))
      | ~ m1_pre_topc(B_211,A_210)
      | v2_struct_0(B_211)
      | ~ l1_pre_topc(A_210)
      | ~ v2_pre_topc(A_210)
      | v2_struct_0(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2346,plain,(
    ! [A_214,B_215] :
      ( k5_tmap_1(A_214,u1_struct_0(B_215)) = u1_pre_topc(k8_tmap_1(A_214,B_215))
      | v2_struct_0(B_215)
      | ~ v2_pre_topc(A_214)
      | v2_struct_0(A_214)
      | ~ m1_pre_topc(B_215,A_214)
      | ~ l1_pre_topc(A_214) ) ),
    inference(resolution,[status(thm)],[c_38,c_2311])).

tff(c_2368,plain,(
    ! [A_214] :
      ( k5_tmap_1(A_214,k2_struct_0('#skF_2')) = u1_pre_topc(k8_tmap_1(A_214,'#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ v2_pre_topc(A_214)
      | v2_struct_0(A_214)
      | ~ m1_pre_topc('#skF_2',A_214)
      | ~ l1_pre_topc(A_214) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_2346])).

tff(c_2408,plain,(
    ! [A_217] :
      ( k5_tmap_1(A_217,k2_struct_0('#skF_2')) = u1_pre_topc(k8_tmap_1(A_217,'#skF_2'))
      | ~ v2_pre_topc(A_217)
      | v2_struct_0(A_217)
      | ~ m1_pre_topc('#skF_2',A_217)
      | ~ l1_pre_topc(A_217) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2368])).

tff(c_2073,plain,(
    ! [A_192,B_193] :
      ( k5_tmap_1(A_192,B_193) = u1_pre_topc(A_192)
      | ~ r2_hidden(B_193,u1_pre_topc(A_192))
      | ~ m1_subset_1(B_193,k1_zfmisc_1(u1_struct_0(A_192)))
      | ~ l1_pre_topc(A_192)
      | ~ v2_pre_topc(A_192)
      | v2_struct_0(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2091,plain,(
    ! [B_193] :
      ( k5_tmap_1('#skF_2',B_193) = u1_pre_topc('#skF_2')
      | ~ r2_hidden(B_193,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_193,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_2073])).

tff(c_2096,plain,(
    ! [B_193] :
      ( k5_tmap_1('#skF_2',B_193) = u1_pre_topc('#skF_2')
      | ~ r2_hidden(B_193,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_193,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_2091])).

tff(c_2109,plain,(
    ! [B_197] :
      ( k5_tmap_1('#skF_2',B_197) = u1_pre_topc('#skF_2')
      | ~ r2_hidden(B_197,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_197,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2096])).

tff(c_2115,plain,
    ( k5_tmap_1('#skF_2',k2_struct_0('#skF_2')) = u1_pre_topc('#skF_2')
    | ~ r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1682,c_2109])).

tff(c_2122,plain,(
    k5_tmap_1('#skF_2',k2_struct_0('#skF_2')) = u1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1772,c_2115])).

tff(c_2414,plain,
    ( u1_pre_topc(k8_tmap_1('#skF_2','#skF_2')) = u1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2408,c_2122])).

tff(c_2423,plain,
    ( u1_pre_topc(k8_tmap_1('#skF_2','#skF_2')) = u1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1683,c_48,c_2414])).

tff(c_2424,plain,(
    u1_pre_topc(k8_tmap_1('#skF_2','#skF_2')) = u1_pre_topc('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2423])).

tff(c_1781,plain,(
    ! [B_160,A_161] :
      ( v3_pre_topc(B_160,A_161)
      | ~ r2_hidden(B_160,u1_pre_topc(A_161))
      | ~ m1_subset_1(B_160,k1_zfmisc_1(u1_struct_0(A_161)))
      | ~ l1_pre_topc(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1889,plain,(
    ! [B_175,A_176] :
      ( v3_pre_topc(u1_struct_0(B_175),A_176)
      | ~ r2_hidden(u1_struct_0(B_175),u1_pre_topc(A_176))
      | ~ m1_pre_topc(B_175,A_176)
      | ~ l1_pre_topc(A_176) ) ),
    inference(resolution,[status(thm)],[c_38,c_1781])).

tff(c_1895,plain,(
    ! [A_176] :
      ( v3_pre_topc(u1_struct_0('#skF_2'),A_176)
      | ~ r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc(A_176))
      | ~ m1_pre_topc('#skF_2',A_176)
      | ~ l1_pre_topc(A_176) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_1889])).

tff(c_1899,plain,(
    ! [A_176] :
      ( v3_pre_topc(k2_struct_0('#skF_2'),A_176)
      | ~ r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc(A_176))
      | ~ m1_pre_topc('#skF_2',A_176)
      | ~ l1_pre_topc(A_176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_1895])).

tff(c_2438,plain,
    ( v3_pre_topc(k2_struct_0('#skF_2'),k8_tmap_1('#skF_2','#skF_2'))
    | ~ r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
    | ~ m1_pre_topc('#skF_2',k8_tmap_1('#skF_2','#skF_2'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2424,c_1899])).

tff(c_2461,plain,
    ( v3_pre_topc(k2_struct_0('#skF_2'),k8_tmap_1('#skF_2','#skF_2'))
    | ~ m1_pre_topc('#skF_2',k8_tmap_1('#skF_2','#skF_2'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1772,c_2438])).

tff(c_2469,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2461])).

tff(c_2472,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_2469])).

tff(c_2475,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1683,c_2472])).

tff(c_2477,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2475])).

tff(c_2479,plain,(
    l1_pre_topc(k8_tmap_1('#skF_2','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2461])).

tff(c_72,plain,(
    ! [A_6] :
      ( u1_struct_0(A_6) = k2_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_68])).

tff(c_2519,plain,(
    u1_struct_0(k8_tmap_1('#skF_2','#skF_2')) = k2_struct_0(k8_tmap_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2479,c_72])).

tff(c_36,plain,(
    ! [A_25,B_29] :
      ( u1_struct_0(k8_tmap_1(A_25,B_29)) = u1_struct_0(A_25)
      | ~ m1_pre_topc(B_29,A_25)
      | v2_struct_0(B_29)
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2562,plain,
    ( k2_struct_0(k8_tmap_1('#skF_2','#skF_2')) = u1_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2519,c_36])).

tff(c_2627,plain,
    ( k2_struct_0(k8_tmap_1('#skF_2','#skF_2')) = k2_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1683,c_77,c_2562])).

tff(c_2628,plain,(
    k2_struct_0(k8_tmap_1('#skF_2','#skF_2')) = k2_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2627])).

tff(c_2654,plain,(
    u1_struct_0(k8_tmap_1('#skF_2','#skF_2')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2628,c_2519])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2748,plain,
    ( g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc(k8_tmap_1('#skF_2','#skF_2'))) = k8_tmap_1('#skF_2','#skF_2')
    | ~ v1_pre_topc(k8_tmap_1('#skF_2','#skF_2'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2654,c_2])).

tff(c_2799,plain,
    ( g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k8_tmap_1('#skF_2','#skF_2')
    | ~ v1_pre_topc(k8_tmap_1('#skF_2','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2479,c_2424,c_2748])).

tff(c_2951,plain,(
    ~ v1_pre_topc(k8_tmap_1('#skF_2','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2799])).

tff(c_2954,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_2951])).

tff(c_2957,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1683,c_2954])).

tff(c_2959,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2957])).

tff(c_2960,plain,(
    g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k8_tmap_1('#skF_2','#skF_2') ),
    inference(splitRight,[status(thm)],[c_2799])).

tff(c_62,plain,
    ( v1_tsep_1('#skF_3','#skF_2')
    | g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k8_tmap_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_78,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k8_tmap_1('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_83,plain,(
    g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k8_tmap_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_78])).

tff(c_42,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_52,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k8_tmap_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ v1_tsep_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_65,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k8_tmap_1('#skF_2','#skF_3')
    | ~ v1_tsep_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_52])).

tff(c_113,plain,(
    ~ v1_tsep_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_77,c_65])).

tff(c_149,plain,(
    ! [B_51,A_52] :
      ( u1_struct_0(B_51) = '#skF_1'(A_52,B_51)
      | v1_tsep_1(B_51,A_52)
      | ~ m1_pre_topc(B_51,A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_152,plain,
    ( u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_149,c_113])).

tff(c_155,plain,(
    u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_152])).

tff(c_114,plain,(
    ! [B_43,A_44] :
      ( m1_subset_1(u1_struct_0(B_43),k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ m1_pre_topc(B_43,A_44)
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_120,plain,(
    ! [B_43] :
      ( m1_subset_1(u1_struct_0(B_43),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_43,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_114])).

tff(c_122,plain,(
    ! [B_43] :
      ( m1_subset_1(u1_struct_0(B_43),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_43,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_120])).

tff(c_162,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_122])).

tff(c_175,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_162])).

tff(c_990,plain,(
    ! [A_123,B_124] :
      ( k5_tmap_1(A_123,u1_struct_0(B_124)) = u1_pre_topc(k8_tmap_1(A_123,B_124))
      | ~ m1_subset_1(u1_struct_0(B_124),k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ m1_pre_topc(B_124,A_123)
      | v2_struct_0(B_124)
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123)
      | v2_struct_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1017,plain,(
    ! [B_124] :
      ( k5_tmap_1('#skF_2',u1_struct_0(B_124)) = u1_pre_topc(k8_tmap_1('#skF_2',B_124))
      | ~ m1_subset_1(u1_struct_0(B_124),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_124,'#skF_2')
      | v2_struct_0(B_124)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_990])).

tff(c_1025,plain,(
    ! [B_124] :
      ( k5_tmap_1('#skF_2',u1_struct_0(B_124)) = u1_pre_topc(k8_tmap_1('#skF_2',B_124))
      | ~ m1_subset_1(u1_struct_0(B_124),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_124,'#skF_2')
      | v2_struct_0(B_124)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1017])).

tff(c_1081,plain,(
    ! [B_127] :
      ( k5_tmap_1('#skF_2',u1_struct_0(B_127)) = u1_pre_topc(k8_tmap_1('#skF_2',B_127))
      | ~ m1_subset_1(u1_struct_0(B_127),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_127,'#skF_2')
      | v2_struct_0(B_127) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1025])).

tff(c_1090,plain,
    ( k5_tmap_1('#skF_2',u1_struct_0('#skF_3')) = u1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_1081])).

tff(c_1098,plain,
    ( k5_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')) = u1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_175,c_155,c_1090])).

tff(c_1099,plain,(
    k5_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')) = u1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1098])).

tff(c_189,plain,(
    ! [B_58,A_59] :
      ( v3_pre_topc(B_58,A_59)
      | ~ r2_hidden(B_58,u1_pre_topc(A_59))
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_204,plain,(
    ! [B_58] :
      ( v3_pre_topc(B_58,'#skF_2')
      | ~ r2_hidden(B_58,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_58,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_189])).

tff(c_210,plain,(
    ! [B_60] :
      ( v3_pre_topc(B_60,'#skF_2')
      | ~ r2_hidden(B_60,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_204])).

tff(c_220,plain,
    ( v3_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | ~ r2_hidden('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_2')) ),
    inference(resolution,[status(thm)],[c_175,c_210])).

tff(c_312,plain,(
    ~ r2_hidden('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_220])).

tff(c_830,plain,(
    ! [B_116,A_117] :
      ( r2_hidden(B_116,u1_pre_topc(A_117))
      | k5_tmap_1(A_117,B_116) != u1_pre_topc(A_117)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117)
      | ~ v2_pre_topc(A_117)
      | v2_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_854,plain,(
    ! [B_116] :
      ( r2_hidden(B_116,u1_pre_topc('#skF_2'))
      | k5_tmap_1('#skF_2',B_116) != u1_pre_topc('#skF_2')
      | ~ m1_subset_1(B_116,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_830])).

tff(c_861,plain,(
    ! [B_116] :
      ( r2_hidden(B_116,u1_pre_topc('#skF_2'))
      | k5_tmap_1('#skF_2',B_116) != u1_pre_topc('#skF_2')
      | ~ m1_subset_1(B_116,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_854])).

tff(c_886,plain,(
    ! [B_119] :
      ( r2_hidden(B_119,u1_pre_topc('#skF_2'))
      | k5_tmap_1('#skF_2',B_119) != u1_pre_topc('#skF_2')
      | ~ m1_subset_1(B_119,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_861])).

tff(c_892,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_2'))
    | k5_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')) != u1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_175,c_886])).

tff(c_902,plain,(
    k5_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')) != u1_pre_topc('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_312,c_892])).

tff(c_1136,plain,(
    u1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) != u1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1099,c_902])).

tff(c_123,plain,(
    ! [B_45] :
      ( m1_subset_1(u1_struct_0(B_45),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_45,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_120])).

tff(c_126,plain,
    ( m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_123])).

tff(c_127,plain,(
    ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_130,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_127])).

tff(c_134,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_130])).

tff(c_136,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_135,plain,(
    m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_221,plain,
    ( v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) ),
    inference(resolution,[status(thm)],[c_135,c_210])).

tff(c_223,plain,(
    ~ r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_237,plain,(
    ! [A_63,B_64] :
      ( v3_pre_topc(k1_tops_1(A_63,B_64),A_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_247,plain,(
    ! [B_64] :
      ( v3_pre_topc(k1_tops_1('#skF_2',B_64),'#skF_2')
      | ~ m1_subset_1(B_64,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_237])).

tff(c_274,plain,(
    ! [B_67] :
      ( v3_pre_topc(k1_tops_1('#skF_2',B_67),'#skF_2')
      | ~ m1_subset_1(B_67,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_247])).

tff(c_285,plain,(
    v3_pre_topc(k1_tops_1('#skF_2',k2_struct_0('#skF_2')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_135,c_274])).

tff(c_289,plain,
    ( v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_285])).

tff(c_291,plain,(
    v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_289])).

tff(c_253,plain,(
    ! [B_65,A_66] :
      ( r2_hidden(B_65,u1_pre_topc(A_66))
      | ~ v3_pre_topc(B_65,A_66)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_268,plain,(
    ! [B_65] :
      ( r2_hidden(B_65,u1_pre_topc('#skF_2'))
      | ~ v3_pre_topc(B_65,'#skF_2')
      | ~ m1_subset_1(B_65,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_253])).

tff(c_292,plain,(
    ! [B_68] :
      ( r2_hidden(B_68,u1_pre_topc('#skF_2'))
      | ~ v3_pre_topc(B_68,'#skF_2')
      | ~ m1_subset_1(B_68,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_268])).

tff(c_298,plain,
    ( r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_135,c_292])).

tff(c_307,plain,(
    r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_298])).

tff(c_309,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_223,c_307])).

tff(c_311,plain,(
    r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_797,plain,(
    ! [A_114,B_115] :
      ( k5_tmap_1(A_114,B_115) = u1_pre_topc(A_114)
      | ~ r2_hidden(B_115,u1_pre_topc(A_114))
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114)
      | ~ v2_pre_topc(A_114)
      | v2_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_821,plain,(
    ! [B_115] :
      ( k5_tmap_1('#skF_2',B_115) = u1_pre_topc('#skF_2')
      | ~ r2_hidden(B_115,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_115,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_797])).

tff(c_828,plain,(
    ! [B_115] :
      ( k5_tmap_1('#skF_2',B_115) = u1_pre_topc('#skF_2')
      | ~ r2_hidden(B_115,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_115,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_821])).

tff(c_863,plain,(
    ! [B_118] :
      ( k5_tmap_1('#skF_2',B_118) = u1_pre_topc('#skF_2')
      | ~ r2_hidden(B_118,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_828])).

tff(c_872,plain,
    ( k5_tmap_1('#skF_2',k2_struct_0('#skF_2')) = u1_pre_topc('#skF_2')
    | ~ r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) ),
    inference(resolution,[status(thm)],[c_135,c_863])).

tff(c_880,plain,(
    k5_tmap_1('#skF_2',k2_struct_0('#skF_2')) = u1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_872])).

tff(c_1096,plain,
    ( k5_tmap_1('#skF_2',u1_struct_0('#skF_2')) = u1_pre_topc(k8_tmap_1('#skF_2','#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_1081])).

tff(c_1102,plain,
    ( u1_pre_topc(k8_tmap_1('#skF_2','#skF_2')) = u1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_135,c_880,c_77,c_1096])).

tff(c_1103,plain,(
    u1_pre_topc(k8_tmap_1('#skF_2','#skF_2')) = u1_pre_topc('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1102])).

tff(c_117,plain,(
    ! [A_44] :
      ( m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ m1_pre_topc('#skF_2',A_44)
      | ~ l1_pre_topc(A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_114])).

tff(c_206,plain,(
    ! [A_44] :
      ( v3_pre_topc(k2_struct_0('#skF_2'),A_44)
      | ~ r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc(A_44))
      | ~ m1_pre_topc('#skF_2',A_44)
      | ~ l1_pre_topc(A_44) ) ),
    inference(resolution,[status(thm)],[c_117,c_189])).

tff(c_1125,plain,
    ( v3_pre_topc(k2_struct_0('#skF_2'),k8_tmap_1('#skF_2','#skF_2'))
    | ~ r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
    | ~ m1_pre_topc('#skF_2',k8_tmap_1('#skF_2','#skF_2'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1103,c_206])).

tff(c_1134,plain,
    ( v3_pre_topc(k2_struct_0('#skF_2'),k8_tmap_1('#skF_2','#skF_2'))
    | ~ m1_pre_topc('#skF_2',k8_tmap_1('#skF_2','#skF_2'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_1125])).

tff(c_1174,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1134])).

tff(c_1228,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_1174])).

tff(c_1231,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_136,c_1228])).

tff(c_1233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1231])).

tff(c_1235,plain,(
    l1_pre_topc(k8_tmap_1('#skF_2','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1134])).

tff(c_1239,plain,(
    u1_struct_0(k8_tmap_1('#skF_2','#skF_2')) = k2_struct_0(k8_tmap_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1235,c_72])).

tff(c_1282,plain,
    ( k2_struct_0(k8_tmap_1('#skF_2','#skF_2')) = u1_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1239,c_36])).

tff(c_1354,plain,
    ( k2_struct_0(k8_tmap_1('#skF_2','#skF_2')) = k2_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_136,c_77,c_1282])).

tff(c_1355,plain,(
    k2_struct_0(k8_tmap_1('#skF_2','#skF_2')) = k2_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1354])).

tff(c_1384,plain,(
    u1_struct_0(k8_tmap_1('#skF_2','#skF_2')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1355,c_1239])).

tff(c_1484,plain,
    ( g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc(k8_tmap_1('#skF_2','#skF_2'))) = k8_tmap_1('#skF_2','#skF_2')
    | ~ v1_pre_topc(k8_tmap_1('#skF_2','#skF_2'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1384,c_2])).

tff(c_1540,plain,
    ( k8_tmap_1('#skF_2','#skF_2') = k8_tmap_1('#skF_2','#skF_3')
    | ~ v1_pre_topc(k8_tmap_1('#skF_2','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1235,c_83,c_1103,c_1484])).

tff(c_1548,plain,(
    ~ v1_pre_topc(k8_tmap_1('#skF_2','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1540])).

tff(c_1551,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_1548])).

tff(c_1554,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_136,c_1551])).

tff(c_1556,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1554])).

tff(c_1557,plain,(
    k8_tmap_1('#skF_2','#skF_2') = k8_tmap_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_1540])).

tff(c_1617,plain,(
    u1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) = u1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1557,c_1103])).

tff(c_1619,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1136,c_1617])).

tff(c_1620,plain,(
    v3_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_220])).

tff(c_18,plain,(
    ! [A_10,B_16] :
      ( ~ v3_pre_topc('#skF_1'(A_10,B_16),A_10)
      | v1_tsep_1(B_16,A_10)
      | ~ m1_pre_topc(B_16,A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1624,plain,
    ( v1_tsep_1('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1620,c_18])).

tff(c_1627,plain,(
    v1_tsep_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_1624])).

tff(c_1629,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_1627])).

tff(c_1631,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k8_tmap_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_1636,plain,(
    g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k8_tmap_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_1631])).

tff(c_2962,plain,(
    k8_tmap_1('#skF_2','#skF_2') != k8_tmap_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2960,c_1636])).

tff(c_1630,plain,(
    v1_tsep_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_2047,plain,(
    ! [B_190,A_191] :
      ( v3_pre_topc(u1_struct_0(B_190),A_191)
      | ~ m1_subset_1(u1_struct_0(B_190),k1_zfmisc_1(u1_struct_0(A_191)))
      | ~ v1_tsep_1(B_190,A_191)
      | ~ m1_pre_topc(B_190,A_191)
      | ~ l1_pre_topc(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2069,plain,(
    ! [B_34,A_32] :
      ( v3_pre_topc(u1_struct_0(B_34),A_32)
      | ~ v1_tsep_1(B_34,A_32)
      | ~ m1_pre_topc(B_34,A_32)
      | ~ l1_pre_topc(A_32) ) ),
    inference(resolution,[status(thm)],[c_38,c_2047])).

tff(c_1712,plain,(
    ! [B_34,A_32] :
      ( r2_hidden(u1_struct_0(B_34),u1_pre_topc(A_32))
      | ~ v3_pre_topc(u1_struct_0(B_34),A_32)
      | ~ m1_pre_topc(B_34,A_32)
      | ~ l1_pre_topc(A_32) ) ),
    inference(resolution,[status(thm)],[c_38,c_1701])).

tff(c_1669,plain,(
    ! [B_135] :
      ( m1_subset_1(u1_struct_0(B_135),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_135,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1667])).

tff(c_2124,plain,(
    ! [B_198] :
      ( k5_tmap_1('#skF_2',u1_struct_0(B_198)) = u1_pre_topc('#skF_2')
      | ~ r2_hidden(u1_struct_0(B_198),u1_pre_topc('#skF_2'))
      | ~ m1_pre_topc(B_198,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1669,c_2109])).

tff(c_2131,plain,(
    ! [B_34] :
      ( k5_tmap_1('#skF_2',u1_struct_0(B_34)) = u1_pre_topc('#skF_2')
      | ~ v3_pre_topc(u1_struct_0(B_34),'#skF_2')
      | ~ m1_pre_topc(B_34,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1712,c_2124])).

tff(c_2152,plain,(
    ! [B_199] :
      ( k5_tmap_1('#skF_2',u1_struct_0(B_199)) = u1_pre_topc('#skF_2')
      | ~ v3_pre_topc(u1_struct_0(B_199),'#skF_2')
      | ~ m1_pre_topc(B_199,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2131])).

tff(c_2156,plain,(
    ! [B_34] :
      ( k5_tmap_1('#skF_2',u1_struct_0(B_34)) = u1_pre_topc('#skF_2')
      | ~ v1_tsep_1(B_34,'#skF_2')
      | ~ m1_pre_topc(B_34,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_2069,c_2152])).

tff(c_2168,plain,(
    ! [B_34] :
      ( k5_tmap_1('#skF_2',u1_struct_0(B_34)) = u1_pre_topc('#skF_2')
      | ~ v1_tsep_1(B_34,'#skF_2')
      | ~ m1_pre_topc(B_34,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2156])).

tff(c_2353,plain,(
    ! [B_215] :
      ( u1_pre_topc(k8_tmap_1('#skF_2',B_215)) = u1_pre_topc('#skF_2')
      | ~ v1_tsep_1(B_215,'#skF_2')
      | ~ m1_pre_topc(B_215,'#skF_2')
      | v2_struct_0(B_215)
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_215,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2346,c_2168])).

tff(c_2371,plain,(
    ! [B_215] :
      ( u1_pre_topc(k8_tmap_1('#skF_2',B_215)) = u1_pre_topc('#skF_2')
      | ~ v1_tsep_1(B_215,'#skF_2')
      | v2_struct_0(B_215)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_215,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_2353])).

tff(c_2372,plain,(
    ! [B_215] :
      ( u1_pre_topc(k8_tmap_1('#skF_2',B_215)) = u1_pre_topc('#skF_2')
      | ~ v1_tsep_1(B_215,'#skF_2')
      | v2_struct_0(B_215)
      | ~ m1_pre_topc(B_215,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2371])).

tff(c_1900,plain,(
    ! [A_177,B_178] :
      ( u1_struct_0(k8_tmap_1(A_177,B_178)) = u1_struct_0(A_177)
      | ~ m1_pre_topc(B_178,A_177)
      | v2_struct_0(B_178)
      | ~ l1_pre_topc(A_177)
      | ~ v2_pre_topc(A_177)
      | v2_struct_0(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_3613,plain,(
    ! [A_257,B_258] :
      ( g1_pre_topc(u1_struct_0(A_257),u1_pre_topc(k8_tmap_1(A_257,B_258))) = k8_tmap_1(A_257,B_258)
      | ~ v1_pre_topc(k8_tmap_1(A_257,B_258))
      | ~ l1_pre_topc(k8_tmap_1(A_257,B_258))
      | ~ m1_pre_topc(B_258,A_257)
      | v2_struct_0(B_258)
      | ~ l1_pre_topc(A_257)
      | ~ v2_pre_topc(A_257)
      | v2_struct_0(A_257) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1900,c_2])).

tff(c_3628,plain,(
    ! [B_215] :
      ( k8_tmap_1('#skF_2',B_215) = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ v1_pre_topc(k8_tmap_1('#skF_2',B_215))
      | ~ l1_pre_topc(k8_tmap_1('#skF_2',B_215))
      | ~ m1_pre_topc(B_215,'#skF_2')
      | v2_struct_0(B_215)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ v1_tsep_1(B_215,'#skF_2')
      | v2_struct_0(B_215)
      | ~ m1_pre_topc(B_215,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2372,c_3613])).

tff(c_3646,plain,(
    ! [B_215] :
      ( k8_tmap_1('#skF_2',B_215) = k8_tmap_1('#skF_2','#skF_2')
      | ~ v1_pre_topc(k8_tmap_1('#skF_2',B_215))
      | ~ l1_pre_topc(k8_tmap_1('#skF_2',B_215))
      | v2_struct_0('#skF_2')
      | ~ v1_tsep_1(B_215,'#skF_2')
      | v2_struct_0(B_215)
      | ~ m1_pre_topc(B_215,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_2960,c_77,c_3628])).

tff(c_3707,plain,(
    ! [B_263] :
      ( k8_tmap_1('#skF_2',B_263) = k8_tmap_1('#skF_2','#skF_2')
      | ~ v1_pre_topc(k8_tmap_1('#skF_2',B_263))
      | ~ l1_pre_topc(k8_tmap_1('#skF_2',B_263))
      | ~ v1_tsep_1(B_263,'#skF_2')
      | v2_struct_0(B_263)
      | ~ m1_pre_topc(B_263,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_3646])).

tff(c_3714,plain,(
    ! [B_21] :
      ( k8_tmap_1('#skF_2',B_21) = k8_tmap_1('#skF_2','#skF_2')
      | ~ l1_pre_topc(k8_tmap_1('#skF_2',B_21))
      | ~ v1_tsep_1(B_21,'#skF_2')
      | v2_struct_0(B_21)
      | ~ m1_pre_topc(B_21,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_3707])).

tff(c_3722,plain,(
    ! [B_21] :
      ( k8_tmap_1('#skF_2',B_21) = k8_tmap_1('#skF_2','#skF_2')
      | ~ l1_pre_topc(k8_tmap_1('#skF_2',B_21))
      | ~ v1_tsep_1(B_21,'#skF_2')
      | v2_struct_0(B_21)
      | ~ m1_pre_topc(B_21,'#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_3714])).

tff(c_3785,plain,(
    ! [B_268] :
      ( k8_tmap_1('#skF_2',B_268) = k8_tmap_1('#skF_2','#skF_2')
      | ~ l1_pre_topc(k8_tmap_1('#skF_2',B_268))
      | ~ v1_tsep_1(B_268,'#skF_2')
      | v2_struct_0(B_268)
      | ~ m1_pre_topc(B_268,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_3722])).

tff(c_3792,plain,(
    ! [B_21] :
      ( k8_tmap_1('#skF_2',B_21) = k8_tmap_1('#skF_2','#skF_2')
      | ~ v1_tsep_1(B_21,'#skF_2')
      | v2_struct_0(B_21)
      | ~ m1_pre_topc(B_21,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_3785])).

tff(c_3800,plain,(
    ! [B_21] :
      ( k8_tmap_1('#skF_2',B_21) = k8_tmap_1('#skF_2','#skF_2')
      | ~ v1_tsep_1(B_21,'#skF_2')
      | v2_struct_0(B_21)
      | ~ m1_pre_topc(B_21,'#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_3792])).

tff(c_3802,plain,(
    ! [B_269] :
      ( k8_tmap_1('#skF_2',B_269) = k8_tmap_1('#skF_2','#skF_2')
      | ~ v1_tsep_1(B_269,'#skF_2')
      | v2_struct_0(B_269)
      | ~ m1_pre_topc(B_269,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_3800])).

tff(c_3809,plain,
    ( k8_tmap_1('#skF_2','#skF_2') = k8_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_1630,c_3802])).

tff(c_3815,plain,
    ( k8_tmap_1('#skF_2','#skF_2') = k8_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3809])).

tff(c_3817,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_2962,c_3815])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:46:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.26/1.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.42/1.99  
% 5.42/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.42/1.99  %$ v3_pre_topc > v1_tsep_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k8_tmap_1 > k5_tmap_1 > k1_tops_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 5.42/1.99  
% 5.42/1.99  %Foreground sorts:
% 5.42/1.99  
% 5.42/1.99  
% 5.42/1.99  %Background operators:
% 5.42/1.99  
% 5.42/1.99  
% 5.42/1.99  %Foreground operators:
% 5.42/1.99  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.42/1.99  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 5.42/1.99  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.42/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.42/1.99  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 5.42/1.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.42/1.99  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.42/1.99  tff(k8_tmap_1, type, k8_tmap_1: ($i * $i) > $i).
% 5.42/1.99  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.42/1.99  tff('#skF_2', type, '#skF_2': $i).
% 5.42/1.99  tff('#skF_3', type, '#skF_3': $i).
% 5.42/1.99  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 5.42/1.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.42/1.99  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.42/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.42/1.99  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 5.42/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.42/1.99  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.42/1.99  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.42/1.99  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 5.42/1.99  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.42/1.99  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.42/1.99  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.42/1.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.42/1.99  
% 5.42/2.02  tff(f_158, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k8_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_tmap_1)).
% 5.42/2.02  tff(f_138, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 5.42/2.02  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.42/2.02  tff(f_35, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 5.42/2.02  tff(f_134, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 5.42/2.02  tff(f_91, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_pre_topc(k8_tmap_1(A, B)) & v2_pre_topc(k8_tmap_1(A, B))) & l1_pre_topc(k8_tmap_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 5.42/2.02  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 5.42/2.02  tff(f_62, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tops_1)).
% 5.42/2.02  tff(f_56, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 5.42/2.02  tff(f_127, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => ((u1_struct_0(k8_tmap_1(A, B)) = u1_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (u1_pre_topc(k8_tmap_1(A, B)) = k5_tmap_1(A, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_tmap_1)).
% 5.42/2.02  tff(f_105, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) <=> (u1_pre_topc(A) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tmap_1)).
% 5.42/2.02  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 5.42/2.02  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tsep_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tsep_1)).
% 5.42/2.02  tff(c_44, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.42/2.02  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.42/2.02  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.42/2.02  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.42/2.02  tff(c_40, plain, (![A_35]: (m1_pre_topc(A_35, A_35) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.42/2.02  tff(c_10, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.42/2.02  tff(c_68, plain, (![A_39]: (u1_struct_0(A_39)=k2_struct_0(A_39) | ~l1_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.42/2.02  tff(c_73, plain, (![A_40]: (u1_struct_0(A_40)=k2_struct_0(A_40) | ~l1_pre_topc(A_40))), inference(resolution, [status(thm)], [c_10, c_68])).
% 5.42/2.02  tff(c_77, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_73])).
% 5.42/2.02  tff(c_1661, plain, (![B_135, A_136]: (m1_subset_1(u1_struct_0(B_135), k1_zfmisc_1(u1_struct_0(A_136))) | ~m1_pre_topc(B_135, A_136) | ~l1_pre_topc(A_136))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.42/2.02  tff(c_1667, plain, (![B_135]: (m1_subset_1(u1_struct_0(B_135), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(B_135, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_77, c_1661])).
% 5.42/2.02  tff(c_1670, plain, (![B_137]: (m1_subset_1(u1_struct_0(B_137), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(B_137, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1667])).
% 5.42/2.02  tff(c_1673, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_77, c_1670])).
% 5.42/2.02  tff(c_1674, plain, (~m1_pre_topc('#skF_2', '#skF_2')), inference(splitLeft, [status(thm)], [c_1673])).
% 5.42/2.02  tff(c_1677, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_1674])).
% 5.42/2.02  tff(c_1681, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_1677])).
% 5.42/2.02  tff(c_1683, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(splitRight, [status(thm)], [c_1673])).
% 5.42/2.02  tff(c_28, plain, (![A_20, B_21]: (v1_pre_topc(k8_tmap_1(A_20, B_21)) | ~m1_pre_topc(B_21, A_20) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.42/2.02  tff(c_24, plain, (![A_20, B_21]: (l1_pre_topc(k8_tmap_1(A_20, B_21)) | ~m1_pre_topc(B_21, A_20) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.42/2.02  tff(c_1682, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_1673])).
% 5.42/2.02  tff(c_1701, plain, (![B_149, A_150]: (r2_hidden(B_149, u1_pre_topc(A_150)) | ~v3_pre_topc(B_149, A_150) | ~m1_subset_1(B_149, k1_zfmisc_1(u1_struct_0(A_150))) | ~l1_pre_topc(A_150))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.42/2.02  tff(c_1710, plain, (![B_149]: (r2_hidden(B_149, u1_pre_topc('#skF_2')) | ~v3_pre_topc(B_149, '#skF_2') | ~m1_subset_1(B_149, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_77, c_1701])).
% 5.42/2.02  tff(c_1715, plain, (![B_151]: (r2_hidden(B_151, u1_pre_topc('#skF_2')) | ~v3_pre_topc(B_151, '#skF_2') | ~m1_subset_1(B_151, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1710])).
% 5.42/2.02  tff(c_1722, plain, (r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_1682, c_1715])).
% 5.42/2.02  tff(c_1724, plain, (~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_1722])).
% 5.42/2.02  tff(c_14, plain, (![A_9]: (k1_tops_1(A_9, k2_struct_0(A_9))=k2_struct_0(A_9) | ~l1_pre_topc(A_9) | ~v2_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.42/2.02  tff(c_1731, plain, (![A_153, B_154]: (v3_pre_topc(k1_tops_1(A_153, B_154), A_153) | ~m1_subset_1(B_154, k1_zfmisc_1(u1_struct_0(A_153))) | ~l1_pre_topc(A_153) | ~v2_pre_topc(A_153))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.42/2.02  tff(c_1737, plain, (![B_154]: (v3_pre_topc(k1_tops_1('#skF_2', B_154), '#skF_2') | ~m1_subset_1(B_154, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_77, c_1731])).
% 5.42/2.02  tff(c_1742, plain, (![B_155]: (v3_pre_topc(k1_tops_1('#skF_2', B_155), '#skF_2') | ~m1_subset_1(B_155, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1737])).
% 5.42/2.02  tff(c_1749, plain, (v3_pre_topc(k1_tops_1('#skF_2', k2_struct_0('#skF_2')), '#skF_2')), inference(resolution, [status(thm)], [c_1682, c_1742])).
% 5.42/2.02  tff(c_1767, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_14, c_1749])).
% 5.42/2.02  tff(c_1769, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1767])).
% 5.42/2.02  tff(c_1771, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1724, c_1769])).
% 5.42/2.02  tff(c_1772, plain, (r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), inference(splitRight, [status(thm)], [c_1722])).
% 5.42/2.02  tff(c_38, plain, (![B_34, A_32]: (m1_subset_1(u1_struct_0(B_34), k1_zfmisc_1(u1_struct_0(A_32))) | ~m1_pre_topc(B_34, A_32) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.42/2.02  tff(c_2311, plain, (![A_210, B_211]: (k5_tmap_1(A_210, u1_struct_0(B_211))=u1_pre_topc(k8_tmap_1(A_210, B_211)) | ~m1_subset_1(u1_struct_0(B_211), k1_zfmisc_1(u1_struct_0(A_210))) | ~m1_pre_topc(B_211, A_210) | v2_struct_0(B_211) | ~l1_pre_topc(A_210) | ~v2_pre_topc(A_210) | v2_struct_0(A_210))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.42/2.02  tff(c_2346, plain, (![A_214, B_215]: (k5_tmap_1(A_214, u1_struct_0(B_215))=u1_pre_topc(k8_tmap_1(A_214, B_215)) | v2_struct_0(B_215) | ~v2_pre_topc(A_214) | v2_struct_0(A_214) | ~m1_pre_topc(B_215, A_214) | ~l1_pre_topc(A_214))), inference(resolution, [status(thm)], [c_38, c_2311])).
% 5.42/2.02  tff(c_2368, plain, (![A_214]: (k5_tmap_1(A_214, k2_struct_0('#skF_2'))=u1_pre_topc(k8_tmap_1(A_214, '#skF_2')) | v2_struct_0('#skF_2') | ~v2_pre_topc(A_214) | v2_struct_0(A_214) | ~m1_pre_topc('#skF_2', A_214) | ~l1_pre_topc(A_214))), inference(superposition, [status(thm), theory('equality')], [c_77, c_2346])).
% 5.42/2.02  tff(c_2408, plain, (![A_217]: (k5_tmap_1(A_217, k2_struct_0('#skF_2'))=u1_pre_topc(k8_tmap_1(A_217, '#skF_2')) | ~v2_pre_topc(A_217) | v2_struct_0(A_217) | ~m1_pre_topc('#skF_2', A_217) | ~l1_pre_topc(A_217))), inference(negUnitSimplification, [status(thm)], [c_50, c_2368])).
% 5.42/2.02  tff(c_2073, plain, (![A_192, B_193]: (k5_tmap_1(A_192, B_193)=u1_pre_topc(A_192) | ~r2_hidden(B_193, u1_pre_topc(A_192)) | ~m1_subset_1(B_193, k1_zfmisc_1(u1_struct_0(A_192))) | ~l1_pre_topc(A_192) | ~v2_pre_topc(A_192) | v2_struct_0(A_192))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.42/2.02  tff(c_2091, plain, (![B_193]: (k5_tmap_1('#skF_2', B_193)=u1_pre_topc('#skF_2') | ~r2_hidden(B_193, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_193, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_77, c_2073])).
% 5.42/2.02  tff(c_2096, plain, (![B_193]: (k5_tmap_1('#skF_2', B_193)=u1_pre_topc('#skF_2') | ~r2_hidden(B_193, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_193, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_2091])).
% 5.42/2.02  tff(c_2109, plain, (![B_197]: (k5_tmap_1('#skF_2', B_197)=u1_pre_topc('#skF_2') | ~r2_hidden(B_197, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_197, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_2096])).
% 5.42/2.02  tff(c_2115, plain, (k5_tmap_1('#skF_2', k2_struct_0('#skF_2'))=u1_pre_topc('#skF_2') | ~r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_1682, c_2109])).
% 5.42/2.02  tff(c_2122, plain, (k5_tmap_1('#skF_2', k2_struct_0('#skF_2'))=u1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1772, c_2115])).
% 5.42/2.02  tff(c_2414, plain, (u1_pre_topc(k8_tmap_1('#skF_2', '#skF_2'))=u1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2408, c_2122])).
% 5.42/2.02  tff(c_2423, plain, (u1_pre_topc(k8_tmap_1('#skF_2', '#skF_2'))=u1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1683, c_48, c_2414])).
% 5.42/2.02  tff(c_2424, plain, (u1_pre_topc(k8_tmap_1('#skF_2', '#skF_2'))=u1_pre_topc('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_2423])).
% 5.42/2.02  tff(c_1781, plain, (![B_160, A_161]: (v3_pre_topc(B_160, A_161) | ~r2_hidden(B_160, u1_pre_topc(A_161)) | ~m1_subset_1(B_160, k1_zfmisc_1(u1_struct_0(A_161))) | ~l1_pre_topc(A_161))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.42/2.02  tff(c_1889, plain, (![B_175, A_176]: (v3_pre_topc(u1_struct_0(B_175), A_176) | ~r2_hidden(u1_struct_0(B_175), u1_pre_topc(A_176)) | ~m1_pre_topc(B_175, A_176) | ~l1_pre_topc(A_176))), inference(resolution, [status(thm)], [c_38, c_1781])).
% 5.42/2.02  tff(c_1895, plain, (![A_176]: (v3_pre_topc(u1_struct_0('#skF_2'), A_176) | ~r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc(A_176)) | ~m1_pre_topc('#skF_2', A_176) | ~l1_pre_topc(A_176))), inference(superposition, [status(thm), theory('equality')], [c_77, c_1889])).
% 5.42/2.02  tff(c_1899, plain, (![A_176]: (v3_pre_topc(k2_struct_0('#skF_2'), A_176) | ~r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc(A_176)) | ~m1_pre_topc('#skF_2', A_176) | ~l1_pre_topc(A_176))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_1895])).
% 5.42/2.02  tff(c_2438, plain, (v3_pre_topc(k2_struct_0('#skF_2'), k8_tmap_1('#skF_2', '#skF_2')) | ~r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~m1_pre_topc('#skF_2', k8_tmap_1('#skF_2', '#skF_2')) | ~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2424, c_1899])).
% 5.42/2.02  tff(c_2461, plain, (v3_pre_topc(k2_struct_0('#skF_2'), k8_tmap_1('#skF_2', '#skF_2')) | ~m1_pre_topc('#skF_2', k8_tmap_1('#skF_2', '#skF_2')) | ~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1772, c_2438])).
% 5.42/2.02  tff(c_2469, plain, (~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_2'))), inference(splitLeft, [status(thm)], [c_2461])).
% 5.42/2.02  tff(c_2472, plain, (~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_24, c_2469])).
% 5.42/2.02  tff(c_2475, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1683, c_2472])).
% 5.42/2.02  tff(c_2477, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_2475])).
% 5.42/2.02  tff(c_2479, plain, (l1_pre_topc(k8_tmap_1('#skF_2', '#skF_2'))), inference(splitRight, [status(thm)], [c_2461])).
% 5.42/2.02  tff(c_72, plain, (![A_6]: (u1_struct_0(A_6)=k2_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(resolution, [status(thm)], [c_10, c_68])).
% 5.42/2.02  tff(c_2519, plain, (u1_struct_0(k8_tmap_1('#skF_2', '#skF_2'))=k2_struct_0(k8_tmap_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_2479, c_72])).
% 5.42/2.02  tff(c_36, plain, (![A_25, B_29]: (u1_struct_0(k8_tmap_1(A_25, B_29))=u1_struct_0(A_25) | ~m1_pre_topc(B_29, A_25) | v2_struct_0(B_29) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.42/2.02  tff(c_2562, plain, (k2_struct_0(k8_tmap_1('#skF_2', '#skF_2'))=u1_struct_0('#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2519, c_36])).
% 5.42/2.02  tff(c_2627, plain, (k2_struct_0(k8_tmap_1('#skF_2', '#skF_2'))=k2_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1683, c_77, c_2562])).
% 5.42/2.02  tff(c_2628, plain, (k2_struct_0(k8_tmap_1('#skF_2', '#skF_2'))=k2_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_2627])).
% 5.42/2.02  tff(c_2654, plain, (u1_struct_0(k8_tmap_1('#skF_2', '#skF_2'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2628, c_2519])).
% 5.42/2.02  tff(c_2, plain, (![A_1]: (g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))=A_1 | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.42/2.02  tff(c_2748, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc(k8_tmap_1('#skF_2', '#skF_2')))=k8_tmap_1('#skF_2', '#skF_2') | ~v1_pre_topc(k8_tmap_1('#skF_2', '#skF_2')) | ~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2654, c_2])).
% 5.42/2.02  tff(c_2799, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k8_tmap_1('#skF_2', '#skF_2') | ~v1_pre_topc(k8_tmap_1('#skF_2', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2479, c_2424, c_2748])).
% 5.42/2.02  tff(c_2951, plain, (~v1_pre_topc(k8_tmap_1('#skF_2', '#skF_2'))), inference(splitLeft, [status(thm)], [c_2799])).
% 5.42/2.02  tff(c_2954, plain, (~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_2951])).
% 5.42/2.02  tff(c_2957, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1683, c_2954])).
% 5.42/2.02  tff(c_2959, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_2957])).
% 5.42/2.02  tff(c_2960, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k8_tmap_1('#skF_2', '#skF_2')), inference(splitRight, [status(thm)], [c_2799])).
% 5.42/2.02  tff(c_62, plain, (v1_tsep_1('#skF_3', '#skF_2') | g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k8_tmap_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.42/2.02  tff(c_78, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k8_tmap_1('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_62])).
% 5.42/2.02  tff(c_83, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k8_tmap_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_78])).
% 5.42/2.02  tff(c_42, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.42/2.02  tff(c_52, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k8_tmap_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~v1_tsep_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.42/2.02  tff(c_65, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k8_tmap_1('#skF_2', '#skF_3') | ~v1_tsep_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_52])).
% 5.42/2.02  tff(c_113, plain, (~v1_tsep_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_77, c_65])).
% 5.42/2.02  tff(c_149, plain, (![B_51, A_52]: (u1_struct_0(B_51)='#skF_1'(A_52, B_51) | v1_tsep_1(B_51, A_52) | ~m1_pre_topc(B_51, A_52) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.42/2.02  tff(c_152, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_149, c_113])).
% 5.42/2.02  tff(c_155, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_152])).
% 5.42/2.02  tff(c_114, plain, (![B_43, A_44]: (m1_subset_1(u1_struct_0(B_43), k1_zfmisc_1(u1_struct_0(A_44))) | ~m1_pre_topc(B_43, A_44) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.42/2.02  tff(c_120, plain, (![B_43]: (m1_subset_1(u1_struct_0(B_43), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(B_43, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_77, c_114])).
% 5.42/2.02  tff(c_122, plain, (![B_43]: (m1_subset_1(u1_struct_0(B_43), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(B_43, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_120])).
% 5.42/2.02  tff(c_162, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_155, c_122])).
% 5.42/2.02  tff(c_175, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_162])).
% 5.42/2.02  tff(c_990, plain, (![A_123, B_124]: (k5_tmap_1(A_123, u1_struct_0(B_124))=u1_pre_topc(k8_tmap_1(A_123, B_124)) | ~m1_subset_1(u1_struct_0(B_124), k1_zfmisc_1(u1_struct_0(A_123))) | ~m1_pre_topc(B_124, A_123) | v2_struct_0(B_124) | ~l1_pre_topc(A_123) | ~v2_pre_topc(A_123) | v2_struct_0(A_123))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.42/2.02  tff(c_1017, plain, (![B_124]: (k5_tmap_1('#skF_2', u1_struct_0(B_124))=u1_pre_topc(k8_tmap_1('#skF_2', B_124)) | ~m1_subset_1(u1_struct_0(B_124), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(B_124, '#skF_2') | v2_struct_0(B_124) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_77, c_990])).
% 5.42/2.02  tff(c_1025, plain, (![B_124]: (k5_tmap_1('#skF_2', u1_struct_0(B_124))=u1_pre_topc(k8_tmap_1('#skF_2', B_124)) | ~m1_subset_1(u1_struct_0(B_124), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(B_124, '#skF_2') | v2_struct_0(B_124) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1017])).
% 5.42/2.02  tff(c_1081, plain, (![B_127]: (k5_tmap_1('#skF_2', u1_struct_0(B_127))=u1_pre_topc(k8_tmap_1('#skF_2', B_127)) | ~m1_subset_1(u1_struct_0(B_127), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(B_127, '#skF_2') | v2_struct_0(B_127))), inference(negUnitSimplification, [status(thm)], [c_50, c_1025])).
% 5.42/2.02  tff(c_1090, plain, (k5_tmap_1('#skF_2', u1_struct_0('#skF_3'))=u1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_155, c_1081])).
% 5.42/2.02  tff(c_1098, plain, (k5_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))=u1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_175, c_155, c_1090])).
% 5.42/2.02  tff(c_1099, plain, (k5_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))=u1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_44, c_1098])).
% 5.42/2.02  tff(c_189, plain, (![B_58, A_59]: (v3_pre_topc(B_58, A_59) | ~r2_hidden(B_58, u1_pre_topc(A_59)) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.42/2.02  tff(c_204, plain, (![B_58]: (v3_pre_topc(B_58, '#skF_2') | ~r2_hidden(B_58, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_58, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_77, c_189])).
% 5.42/2.02  tff(c_210, plain, (![B_60]: (v3_pre_topc(B_60, '#skF_2') | ~r2_hidden(B_60, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_60, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_204])).
% 5.42/2.02  tff(c_220, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | ~r2_hidden('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_175, c_210])).
% 5.42/2.02  tff(c_312, plain, (~r2_hidden('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_2'))), inference(splitLeft, [status(thm)], [c_220])).
% 5.42/2.02  tff(c_830, plain, (![B_116, A_117]: (r2_hidden(B_116, u1_pre_topc(A_117)) | k5_tmap_1(A_117, B_116)!=u1_pre_topc(A_117) | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_pre_topc(A_117) | ~v2_pre_topc(A_117) | v2_struct_0(A_117))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.42/2.02  tff(c_854, plain, (![B_116]: (r2_hidden(B_116, u1_pre_topc('#skF_2')) | k5_tmap_1('#skF_2', B_116)!=u1_pre_topc('#skF_2') | ~m1_subset_1(B_116, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_77, c_830])).
% 5.42/2.02  tff(c_861, plain, (![B_116]: (r2_hidden(B_116, u1_pre_topc('#skF_2')) | k5_tmap_1('#skF_2', B_116)!=u1_pre_topc('#skF_2') | ~m1_subset_1(B_116, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_854])).
% 5.42/2.02  tff(c_886, plain, (![B_119]: (r2_hidden(B_119, u1_pre_topc('#skF_2')) | k5_tmap_1('#skF_2', B_119)!=u1_pre_topc('#skF_2') | ~m1_subset_1(B_119, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_861])).
% 5.42/2.02  tff(c_892, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_2')) | k5_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))!=u1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_175, c_886])).
% 5.42/2.02  tff(c_902, plain, (k5_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))!=u1_pre_topc('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_312, c_892])).
% 5.42/2.02  tff(c_1136, plain, (u1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))!=u1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1099, c_902])).
% 5.42/2.02  tff(c_123, plain, (![B_45]: (m1_subset_1(u1_struct_0(B_45), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(B_45, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_120])).
% 5.42/2.02  tff(c_126, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_77, c_123])).
% 5.42/2.02  tff(c_127, plain, (~m1_pre_topc('#skF_2', '#skF_2')), inference(splitLeft, [status(thm)], [c_126])).
% 5.42/2.02  tff(c_130, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_127])).
% 5.42/2.02  tff(c_134, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_130])).
% 5.42/2.02  tff(c_136, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(splitRight, [status(thm)], [c_126])).
% 5.42/2.02  tff(c_135, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_126])).
% 5.42/2.02  tff(c_221, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_135, c_210])).
% 5.42/2.02  tff(c_223, plain, (~r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), inference(splitLeft, [status(thm)], [c_221])).
% 5.42/2.02  tff(c_237, plain, (![A_63, B_64]: (v3_pre_topc(k1_tops_1(A_63, B_64), A_63) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63) | ~v2_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.42/2.02  tff(c_247, plain, (![B_64]: (v3_pre_topc(k1_tops_1('#skF_2', B_64), '#skF_2') | ~m1_subset_1(B_64, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_77, c_237])).
% 5.42/2.02  tff(c_274, plain, (![B_67]: (v3_pre_topc(k1_tops_1('#skF_2', B_67), '#skF_2') | ~m1_subset_1(B_67, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_247])).
% 5.42/2.02  tff(c_285, plain, (v3_pre_topc(k1_tops_1('#skF_2', k2_struct_0('#skF_2')), '#skF_2')), inference(resolution, [status(thm)], [c_135, c_274])).
% 5.42/2.02  tff(c_289, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_14, c_285])).
% 5.42/2.02  tff(c_291, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_289])).
% 5.42/2.02  tff(c_253, plain, (![B_65, A_66]: (r2_hidden(B_65, u1_pre_topc(A_66)) | ~v3_pre_topc(B_65, A_66) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.42/2.02  tff(c_268, plain, (![B_65]: (r2_hidden(B_65, u1_pre_topc('#skF_2')) | ~v3_pre_topc(B_65, '#skF_2') | ~m1_subset_1(B_65, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_77, c_253])).
% 5.42/2.02  tff(c_292, plain, (![B_68]: (r2_hidden(B_68, u1_pre_topc('#skF_2')) | ~v3_pre_topc(B_68, '#skF_2') | ~m1_subset_1(B_68, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_268])).
% 5.42/2.02  tff(c_298, plain, (r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_135, c_292])).
% 5.42/2.02  tff(c_307, plain, (r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_291, c_298])).
% 5.42/2.02  tff(c_309, plain, $false, inference(negUnitSimplification, [status(thm)], [c_223, c_307])).
% 5.42/2.02  tff(c_311, plain, (r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), inference(splitRight, [status(thm)], [c_221])).
% 5.42/2.02  tff(c_797, plain, (![A_114, B_115]: (k5_tmap_1(A_114, B_115)=u1_pre_topc(A_114) | ~r2_hidden(B_115, u1_pre_topc(A_114)) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114) | ~v2_pre_topc(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.42/2.02  tff(c_821, plain, (![B_115]: (k5_tmap_1('#skF_2', B_115)=u1_pre_topc('#skF_2') | ~r2_hidden(B_115, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_115, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_77, c_797])).
% 5.42/2.02  tff(c_828, plain, (![B_115]: (k5_tmap_1('#skF_2', B_115)=u1_pre_topc('#skF_2') | ~r2_hidden(B_115, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_115, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_821])).
% 5.42/2.02  tff(c_863, plain, (![B_118]: (k5_tmap_1('#skF_2', B_118)=u1_pre_topc('#skF_2') | ~r2_hidden(B_118, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_118, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_828])).
% 5.42/2.02  tff(c_872, plain, (k5_tmap_1('#skF_2', k2_struct_0('#skF_2'))=u1_pre_topc('#skF_2') | ~r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_135, c_863])).
% 5.42/2.02  tff(c_880, plain, (k5_tmap_1('#skF_2', k2_struct_0('#skF_2'))=u1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_311, c_872])).
% 5.42/2.02  tff(c_1096, plain, (k5_tmap_1('#skF_2', u1_struct_0('#skF_2'))=u1_pre_topc(k8_tmap_1('#skF_2', '#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc('#skF_2', '#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_77, c_1081])).
% 5.42/2.02  tff(c_1102, plain, (u1_pre_topc(k8_tmap_1('#skF_2', '#skF_2'))=u1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_135, c_880, c_77, c_1096])).
% 5.42/2.02  tff(c_1103, plain, (u1_pre_topc(k8_tmap_1('#skF_2', '#skF_2'))=u1_pre_topc('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_1102])).
% 5.42/2.02  tff(c_117, plain, (![A_44]: (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_44))) | ~m1_pre_topc('#skF_2', A_44) | ~l1_pre_topc(A_44))), inference(superposition, [status(thm), theory('equality')], [c_77, c_114])).
% 5.42/2.02  tff(c_206, plain, (![A_44]: (v3_pre_topc(k2_struct_0('#skF_2'), A_44) | ~r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc(A_44)) | ~m1_pre_topc('#skF_2', A_44) | ~l1_pre_topc(A_44))), inference(resolution, [status(thm)], [c_117, c_189])).
% 5.42/2.02  tff(c_1125, plain, (v3_pre_topc(k2_struct_0('#skF_2'), k8_tmap_1('#skF_2', '#skF_2')) | ~r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~m1_pre_topc('#skF_2', k8_tmap_1('#skF_2', '#skF_2')) | ~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1103, c_206])).
% 5.42/2.02  tff(c_1134, plain, (v3_pre_topc(k2_struct_0('#skF_2'), k8_tmap_1('#skF_2', '#skF_2')) | ~m1_pre_topc('#skF_2', k8_tmap_1('#skF_2', '#skF_2')) | ~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_311, c_1125])).
% 5.42/2.02  tff(c_1174, plain, (~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_2'))), inference(splitLeft, [status(thm)], [c_1134])).
% 5.42/2.02  tff(c_1228, plain, (~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_24, c_1174])).
% 5.42/2.02  tff(c_1231, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_136, c_1228])).
% 5.42/2.02  tff(c_1233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_1231])).
% 5.42/2.02  tff(c_1235, plain, (l1_pre_topc(k8_tmap_1('#skF_2', '#skF_2'))), inference(splitRight, [status(thm)], [c_1134])).
% 5.42/2.02  tff(c_1239, plain, (u1_struct_0(k8_tmap_1('#skF_2', '#skF_2'))=k2_struct_0(k8_tmap_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_1235, c_72])).
% 5.42/2.02  tff(c_1282, plain, (k2_struct_0(k8_tmap_1('#skF_2', '#skF_2'))=u1_struct_0('#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1239, c_36])).
% 5.42/2.02  tff(c_1354, plain, (k2_struct_0(k8_tmap_1('#skF_2', '#skF_2'))=k2_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_136, c_77, c_1282])).
% 5.42/2.02  tff(c_1355, plain, (k2_struct_0(k8_tmap_1('#skF_2', '#skF_2'))=k2_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_1354])).
% 5.42/2.02  tff(c_1384, plain, (u1_struct_0(k8_tmap_1('#skF_2', '#skF_2'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1355, c_1239])).
% 5.42/2.02  tff(c_1484, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc(k8_tmap_1('#skF_2', '#skF_2')))=k8_tmap_1('#skF_2', '#skF_2') | ~v1_pre_topc(k8_tmap_1('#skF_2', '#skF_2')) | ~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1384, c_2])).
% 5.42/2.02  tff(c_1540, plain, (k8_tmap_1('#skF_2', '#skF_2')=k8_tmap_1('#skF_2', '#skF_3') | ~v1_pre_topc(k8_tmap_1('#skF_2', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1235, c_83, c_1103, c_1484])).
% 5.42/2.02  tff(c_1548, plain, (~v1_pre_topc(k8_tmap_1('#skF_2', '#skF_2'))), inference(splitLeft, [status(thm)], [c_1540])).
% 5.42/2.02  tff(c_1551, plain, (~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_1548])).
% 5.42/2.02  tff(c_1554, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_136, c_1551])).
% 5.42/2.02  tff(c_1556, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_1554])).
% 5.42/2.02  tff(c_1557, plain, (k8_tmap_1('#skF_2', '#skF_2')=k8_tmap_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_1540])).
% 5.42/2.02  tff(c_1617, plain, (u1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))=u1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1557, c_1103])).
% 5.42/2.02  tff(c_1619, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1136, c_1617])).
% 5.42/2.02  tff(c_1620, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_220])).
% 5.42/2.02  tff(c_18, plain, (![A_10, B_16]: (~v3_pre_topc('#skF_1'(A_10, B_16), A_10) | v1_tsep_1(B_16, A_10) | ~m1_pre_topc(B_16, A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.42/2.02  tff(c_1624, plain, (v1_tsep_1('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_1620, c_18])).
% 5.42/2.02  tff(c_1627, plain, (v1_tsep_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_1624])).
% 5.42/2.02  tff(c_1629, plain, $false, inference(negUnitSimplification, [status(thm)], [c_113, c_1627])).
% 5.42/2.02  tff(c_1631, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k8_tmap_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_62])).
% 5.42/2.02  tff(c_1636, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k8_tmap_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_1631])).
% 5.42/2.02  tff(c_2962, plain, (k8_tmap_1('#skF_2', '#skF_2')!=k8_tmap_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2960, c_1636])).
% 5.42/2.02  tff(c_1630, plain, (v1_tsep_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_62])).
% 5.42/2.02  tff(c_2047, plain, (![B_190, A_191]: (v3_pre_topc(u1_struct_0(B_190), A_191) | ~m1_subset_1(u1_struct_0(B_190), k1_zfmisc_1(u1_struct_0(A_191))) | ~v1_tsep_1(B_190, A_191) | ~m1_pre_topc(B_190, A_191) | ~l1_pre_topc(A_191))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.42/2.02  tff(c_2069, plain, (![B_34, A_32]: (v3_pre_topc(u1_struct_0(B_34), A_32) | ~v1_tsep_1(B_34, A_32) | ~m1_pre_topc(B_34, A_32) | ~l1_pre_topc(A_32))), inference(resolution, [status(thm)], [c_38, c_2047])).
% 5.42/2.02  tff(c_1712, plain, (![B_34, A_32]: (r2_hidden(u1_struct_0(B_34), u1_pre_topc(A_32)) | ~v3_pre_topc(u1_struct_0(B_34), A_32) | ~m1_pre_topc(B_34, A_32) | ~l1_pre_topc(A_32))), inference(resolution, [status(thm)], [c_38, c_1701])).
% 5.42/2.02  tff(c_1669, plain, (![B_135]: (m1_subset_1(u1_struct_0(B_135), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(B_135, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1667])).
% 5.42/2.02  tff(c_2124, plain, (![B_198]: (k5_tmap_1('#skF_2', u1_struct_0(B_198))=u1_pre_topc('#skF_2') | ~r2_hidden(u1_struct_0(B_198), u1_pre_topc('#skF_2')) | ~m1_pre_topc(B_198, '#skF_2'))), inference(resolution, [status(thm)], [c_1669, c_2109])).
% 5.42/2.02  tff(c_2131, plain, (![B_34]: (k5_tmap_1('#skF_2', u1_struct_0(B_34))=u1_pre_topc('#skF_2') | ~v3_pre_topc(u1_struct_0(B_34), '#skF_2') | ~m1_pre_topc(B_34, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_1712, c_2124])).
% 5.42/2.02  tff(c_2152, plain, (![B_199]: (k5_tmap_1('#skF_2', u1_struct_0(B_199))=u1_pre_topc('#skF_2') | ~v3_pre_topc(u1_struct_0(B_199), '#skF_2') | ~m1_pre_topc(B_199, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2131])).
% 5.42/2.02  tff(c_2156, plain, (![B_34]: (k5_tmap_1('#skF_2', u1_struct_0(B_34))=u1_pre_topc('#skF_2') | ~v1_tsep_1(B_34, '#skF_2') | ~m1_pre_topc(B_34, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_2069, c_2152])).
% 5.42/2.02  tff(c_2168, plain, (![B_34]: (k5_tmap_1('#skF_2', u1_struct_0(B_34))=u1_pre_topc('#skF_2') | ~v1_tsep_1(B_34, '#skF_2') | ~m1_pre_topc(B_34, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2156])).
% 5.42/2.02  tff(c_2353, plain, (![B_215]: (u1_pre_topc(k8_tmap_1('#skF_2', B_215))=u1_pre_topc('#skF_2') | ~v1_tsep_1(B_215, '#skF_2') | ~m1_pre_topc(B_215, '#skF_2') | v2_struct_0(B_215) | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(B_215, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2346, c_2168])).
% 5.42/2.02  tff(c_2371, plain, (![B_215]: (u1_pre_topc(k8_tmap_1('#skF_2', B_215))=u1_pre_topc('#skF_2') | ~v1_tsep_1(B_215, '#skF_2') | v2_struct_0(B_215) | v2_struct_0('#skF_2') | ~m1_pre_topc(B_215, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48, c_2353])).
% 5.42/2.02  tff(c_2372, plain, (![B_215]: (u1_pre_topc(k8_tmap_1('#skF_2', B_215))=u1_pre_topc('#skF_2') | ~v1_tsep_1(B_215, '#skF_2') | v2_struct_0(B_215) | ~m1_pre_topc(B_215, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_2371])).
% 5.42/2.02  tff(c_1900, plain, (![A_177, B_178]: (u1_struct_0(k8_tmap_1(A_177, B_178))=u1_struct_0(A_177) | ~m1_pre_topc(B_178, A_177) | v2_struct_0(B_178) | ~l1_pre_topc(A_177) | ~v2_pre_topc(A_177) | v2_struct_0(A_177))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.42/2.02  tff(c_3613, plain, (![A_257, B_258]: (g1_pre_topc(u1_struct_0(A_257), u1_pre_topc(k8_tmap_1(A_257, B_258)))=k8_tmap_1(A_257, B_258) | ~v1_pre_topc(k8_tmap_1(A_257, B_258)) | ~l1_pre_topc(k8_tmap_1(A_257, B_258)) | ~m1_pre_topc(B_258, A_257) | v2_struct_0(B_258) | ~l1_pre_topc(A_257) | ~v2_pre_topc(A_257) | v2_struct_0(A_257))), inference(superposition, [status(thm), theory('equality')], [c_1900, c_2])).
% 5.42/2.02  tff(c_3628, plain, (![B_215]: (k8_tmap_1('#skF_2', B_215)=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~v1_pre_topc(k8_tmap_1('#skF_2', B_215)) | ~l1_pre_topc(k8_tmap_1('#skF_2', B_215)) | ~m1_pre_topc(B_215, '#skF_2') | v2_struct_0(B_215) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~v1_tsep_1(B_215, '#skF_2') | v2_struct_0(B_215) | ~m1_pre_topc(B_215, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2372, c_3613])).
% 5.42/2.02  tff(c_3646, plain, (![B_215]: (k8_tmap_1('#skF_2', B_215)=k8_tmap_1('#skF_2', '#skF_2') | ~v1_pre_topc(k8_tmap_1('#skF_2', B_215)) | ~l1_pre_topc(k8_tmap_1('#skF_2', B_215)) | v2_struct_0('#skF_2') | ~v1_tsep_1(B_215, '#skF_2') | v2_struct_0(B_215) | ~m1_pre_topc(B_215, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_2960, c_77, c_3628])).
% 5.42/2.02  tff(c_3707, plain, (![B_263]: (k8_tmap_1('#skF_2', B_263)=k8_tmap_1('#skF_2', '#skF_2') | ~v1_pre_topc(k8_tmap_1('#skF_2', B_263)) | ~l1_pre_topc(k8_tmap_1('#skF_2', B_263)) | ~v1_tsep_1(B_263, '#skF_2') | v2_struct_0(B_263) | ~m1_pre_topc(B_263, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_3646])).
% 5.42/2.02  tff(c_3714, plain, (![B_21]: (k8_tmap_1('#skF_2', B_21)=k8_tmap_1('#skF_2', '#skF_2') | ~l1_pre_topc(k8_tmap_1('#skF_2', B_21)) | ~v1_tsep_1(B_21, '#skF_2') | v2_struct_0(B_21) | ~m1_pre_topc(B_21, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_3707])).
% 5.42/2.02  tff(c_3722, plain, (![B_21]: (k8_tmap_1('#skF_2', B_21)=k8_tmap_1('#skF_2', '#skF_2') | ~l1_pre_topc(k8_tmap_1('#skF_2', B_21)) | ~v1_tsep_1(B_21, '#skF_2') | v2_struct_0(B_21) | ~m1_pre_topc(B_21, '#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_3714])).
% 5.42/2.02  tff(c_3785, plain, (![B_268]: (k8_tmap_1('#skF_2', B_268)=k8_tmap_1('#skF_2', '#skF_2') | ~l1_pre_topc(k8_tmap_1('#skF_2', B_268)) | ~v1_tsep_1(B_268, '#skF_2') | v2_struct_0(B_268) | ~m1_pre_topc(B_268, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_3722])).
% 5.42/2.02  tff(c_3792, plain, (![B_21]: (k8_tmap_1('#skF_2', B_21)=k8_tmap_1('#skF_2', '#skF_2') | ~v1_tsep_1(B_21, '#skF_2') | v2_struct_0(B_21) | ~m1_pre_topc(B_21, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_3785])).
% 5.42/2.02  tff(c_3800, plain, (![B_21]: (k8_tmap_1('#skF_2', B_21)=k8_tmap_1('#skF_2', '#skF_2') | ~v1_tsep_1(B_21, '#skF_2') | v2_struct_0(B_21) | ~m1_pre_topc(B_21, '#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_3792])).
% 5.42/2.02  tff(c_3802, plain, (![B_269]: (k8_tmap_1('#skF_2', B_269)=k8_tmap_1('#skF_2', '#skF_2') | ~v1_tsep_1(B_269, '#skF_2') | v2_struct_0(B_269) | ~m1_pre_topc(B_269, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_3800])).
% 5.42/2.02  tff(c_3809, plain, (k8_tmap_1('#skF_2', '#skF_2')=k8_tmap_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_1630, c_3802])).
% 5.42/2.02  tff(c_3815, plain, (k8_tmap_1('#skF_2', '#skF_2')=k8_tmap_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_3809])).
% 5.42/2.02  tff(c_3817, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_2962, c_3815])).
% 5.42/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.42/2.02  
% 5.42/2.02  Inference rules
% 5.42/2.02  ----------------------
% 5.42/2.02  #Ref     : 0
% 5.42/2.02  #Sup     : 833
% 5.42/2.02  #Fact    : 0
% 5.42/2.02  #Define  : 0
% 5.42/2.02  #Split   : 17
% 5.42/2.02  #Chain   : 0
% 5.42/2.02  #Close   : 0
% 5.42/2.02  
% 5.42/2.02  Ordering : KBO
% 5.42/2.02  
% 5.42/2.02  Simplification rules
% 5.42/2.02  ----------------------
% 5.42/2.02  #Subsume      : 119
% 5.42/2.02  #Demod        : 744
% 5.42/2.02  #Tautology    : 248
% 5.42/2.02  #SimpNegUnit  : 104
% 5.42/2.02  #BackRed      : 9
% 5.42/2.02  
% 5.42/2.02  #Partial instantiations: 0
% 5.42/2.02  #Strategies tried      : 1
% 5.42/2.02  
% 5.42/2.02  Timing (in seconds)
% 5.42/2.02  ----------------------
% 5.42/2.03  Preprocessing        : 0.35
% 5.42/2.03  Parsing              : 0.19
% 5.42/2.03  CNF conversion       : 0.02
% 5.42/2.03  Main loop            : 0.87
% 5.42/2.03  Inferencing          : 0.31
% 5.42/2.03  Reduction            : 0.27
% 5.42/2.03  Demodulation         : 0.18
% 5.42/2.03  BG Simplification    : 0.04
% 5.42/2.03  Subsumption          : 0.18
% 5.42/2.03  Abstraction          : 0.04
% 5.42/2.03  MUC search           : 0.00
% 5.42/2.03  Cooper               : 0.00
% 5.42/2.03  Total                : 1.29
% 5.42/2.03  Index Insertion      : 0.00
% 5.42/2.03  Index Deletion       : 0.00
% 5.42/2.03  Index Matching       : 0.00
% 5.42/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
