%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:58 EST 2020

% Result     : Theorem 8.95s
% Output     : CNFRefutation 9.18s
% Verified   : 
% Statistics : Number of formulae       :  163 (1388 expanded)
%              Number of leaves         :   34 ( 483 expanded)
%              Depth                    :   21
%              Number of atoms          :  405 (4076 expanded)
%              Number of equality atoms :   24 ( 454 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tops_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_tdlat_3 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k1_enumset1 > k2_tarski > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_158,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                & v2_tdlat_3(A) )
             => v2_tdlat_3(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tex_2)).

tff(f_146,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_tdlat_3(A)
      <=> u1_pre_topc(A) = k2_tarski(k1_xboole_0,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tdlat_3)).

tff(f_113,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_120,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> r1_tarski(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tops_2)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( v1_tops_2(B,A)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C))))
                   => ( D = B
                     => v1_tops_2(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tops_2)).

tff(f_109,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
             => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_2)).

tff(c_58,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_52,plain,(
    v2_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_48,plain,(
    ! [A_57] :
      ( k2_tarski(k1_xboole_0,u1_struct_0(A_57)) = u1_pre_topc(A_57)
      | ~ v2_tdlat_3(A_57)
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_50,plain,(
    ~ v2_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_56,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_36,plain,(
    ! [A_45] :
      ( m1_pre_topc(A_45,A_45)
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_175,plain,(
    ! [A_86,B_87] :
      ( m1_pre_topc(A_86,g1_pre_topc(u1_struct_0(B_87),u1_pre_topc(B_87)))
      | ~ m1_pre_topc(A_86,B_87)
      | ~ l1_pre_topc(B_87)
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_54,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_137,plain,(
    ! [B_81,A_82] :
      ( m1_pre_topc(B_81,A_82)
      | ~ m1_pre_topc(B_81,g1_pre_topc(u1_struct_0(A_82),u1_pre_topc(A_82)))
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_140,plain,(
    ! [B_81] :
      ( m1_pre_topc(B_81,'#skF_2')
      | ~ m1_pre_topc(B_81,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_137])).

tff(c_146,plain,(
    ! [B_81] :
      ( m1_pre_topc(B_81,'#skF_2')
      | ~ m1_pre_topc(B_81,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_140])).

tff(c_179,plain,(
    ! [A_86] :
      ( m1_pre_topc(A_86,'#skF_2')
      | ~ m1_pre_topc(A_86,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ l1_pre_topc(A_86) ) ),
    inference(resolution,[status(thm)],[c_175,c_146])).

tff(c_193,plain,(
    ! [A_86] :
      ( m1_pre_topc(A_86,'#skF_2')
      | ~ m1_pre_topc(A_86,'#skF_1')
      | ~ l1_pre_topc(A_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_179])).

tff(c_190,plain,(
    ! [A_86] :
      ( m1_pre_topc(A_86,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_pre_topc(A_86,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_175])).

tff(c_254,plain,(
    ! [A_93] :
      ( m1_pre_topc(A_93,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_pre_topc(A_93,'#skF_2')
      | ~ l1_pre_topc(A_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_190])).

tff(c_18,plain,(
    ! [B_13,A_11] :
      ( m1_pre_topc(B_13,A_11)
      | ~ m1_pre_topc(B_13,g1_pre_topc(u1_struct_0(A_11),u1_pre_topc(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_262,plain,(
    ! [A_93] :
      ( m1_pre_topc(A_93,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_pre_topc(A_93,'#skF_2')
      | ~ l1_pre_topc(A_93) ) ),
    inference(resolution,[status(thm)],[c_254,c_18])).

tff(c_281,plain,(
    ! [A_94] :
      ( m1_pre_topc(A_94,'#skF_1')
      | ~ m1_pre_topc(A_94,'#skF_2')
      | ~ l1_pre_topc(A_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_262])).

tff(c_296,plain,
    ( m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_281])).

tff(c_306,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_296])).

tff(c_38,plain,(
    ! [B_48,A_46] :
      ( r1_tarski(u1_struct_0(B_48),u1_struct_0(A_46))
      | ~ m1_pre_topc(B_48,A_46)
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_123,plain,(
    ! [B_76,A_77] :
      ( r1_tarski(u1_struct_0(B_76),u1_struct_0(A_77))
      | ~ m1_pre_topc(B_76,A_77)
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_474,plain,(
    ! [B_102,A_103] :
      ( u1_struct_0(B_102) = u1_struct_0(A_103)
      | ~ r1_tarski(u1_struct_0(A_103),u1_struct_0(B_102))
      | ~ m1_pre_topc(B_102,A_103)
      | ~ l1_pre_topc(A_103) ) ),
    inference(resolution,[status(thm)],[c_123,c_2])).

tff(c_589,plain,(
    ! [B_119,A_120] :
      ( u1_struct_0(B_119) = u1_struct_0(A_120)
      | ~ m1_pre_topc(A_120,B_119)
      | ~ l1_pre_topc(B_119)
      | ~ m1_pre_topc(B_119,A_120)
      | ~ l1_pre_topc(A_120) ) ),
    inference(resolution,[status(thm)],[c_38,c_474])).

tff(c_597,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_306,c_589])).

tff(c_622,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_597])).

tff(c_636,plain,(
    ~ m1_pre_topc('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_622])).

tff(c_639,plain,
    ( ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_193,c_636])).

tff(c_642,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_639])).

tff(c_645,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_642])).

tff(c_649,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_645])).

tff(c_650,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_622])).

tff(c_46,plain,(
    ! [A_57] :
      ( v2_tdlat_3(A_57)
      | k2_tarski(k1_xboole_0,u1_struct_0(A_57)) != u1_pre_topc(A_57)
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_776,plain,
    ( v2_tdlat_3('#skF_2')
    | k2_tarski(k1_xboole_0,u1_struct_0('#skF_1')) != u1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_650,c_46])).

tff(c_822,plain,
    ( v2_tdlat_3('#skF_2')
    | k2_tarski(k1_xboole_0,u1_struct_0('#skF_1')) != u1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_776])).

tff(c_823,plain,(
    k2_tarski(k1_xboole_0,u1_struct_0('#skF_1')) != u1_pre_topc('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_822])).

tff(c_833,plain,
    ( u1_pre_topc('#skF_2') != u1_pre_topc('#skF_1')
    | ~ v2_tdlat_3('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_823])).

tff(c_835,plain,(
    u1_pre_topc('#skF_2') != u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_833])).

tff(c_16,plain,(
    ! [A_10] :
      ( m1_subset_1(u1_pre_topc(A_10),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_10))))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_785,plain,
    ( m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_650,c_16])).

tff(c_829,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_785])).

tff(c_651,plain,(
    m1_pre_topc('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_622])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_100,plain,(
    ! [A_72] :
      ( m1_subset_1(u1_pre_topc(A_72),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_72))))
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_104,plain,(
    ! [A_72] :
      ( r1_tarski(u1_pre_topc(A_72),k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(resolution,[status(thm)],[c_100,c_10])).

tff(c_779,plain,
    ( r1_tarski(u1_pre_topc('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_650,c_104])).

tff(c_825,plain,(
    r1_tarski(u1_pre_topc('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_779])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_437,plain,(
    ! [B_99,A_100] :
      ( v1_tops_2(B_99,A_100)
      | ~ r1_tarski(B_99,u1_pre_topc(A_100))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_100))))
      | ~ l1_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_448,plain,(
    ! [A_5,A_100] :
      ( v1_tops_2(A_5,A_100)
      | ~ r1_tarski(A_5,u1_pre_topc(A_100))
      | ~ l1_pre_topc(A_100)
      | ~ r1_tarski(A_5,k1_zfmisc_1(u1_struct_0(A_100))) ) ),
    inference(resolution,[status(thm)],[c_12,c_437])).

tff(c_728,plain,(
    ! [A_5] :
      ( v1_tops_2(A_5,'#skF_2')
      | ~ r1_tarski(A_5,u1_pre_topc('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_5,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_650,c_448])).

tff(c_1659,plain,(
    ! [A_149] :
      ( v1_tops_2(A_149,'#skF_2')
      | ~ r1_tarski(A_149,u1_pre_topc('#skF_2'))
      | ~ r1_tarski(A_149,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_728])).

tff(c_1668,plain,
    ( v1_tops_2(u1_pre_topc('#skF_2'),'#skF_2')
    | ~ r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_2')) ),
    inference(resolution,[status(thm)],[c_825,c_1659])).

tff(c_1685,plain,(
    v1_tops_2(u1_pre_topc('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1668])).

tff(c_30,plain,(
    ! [B_41,A_39] :
      ( r1_tarski(B_41,u1_pre_topc(A_39))
      | ~ v1_tops_2(B_41,A_39)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_39))))
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_912,plain,
    ( r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_1'))
    | ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_829,c_30])).

tff(c_922,plain,
    ( r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_1'))
    | ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_912])).

tff(c_965,plain,(
    ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_922])).

tff(c_969,plain,(
    ! [D_129,C_130,A_131] :
      ( v1_tops_2(D_129,C_130)
      | ~ m1_subset_1(D_129,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_130))))
      | ~ v1_tops_2(D_129,A_131)
      | ~ m1_pre_topc(C_130,A_131)
      | ~ m1_subset_1(D_129,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_131))))
      | ~ l1_pre_topc(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_971,plain,(
    ! [A_131] :
      ( v1_tops_2(u1_pre_topc('#skF_2'),'#skF_1')
      | ~ v1_tops_2(u1_pre_topc('#skF_2'),A_131)
      | ~ m1_pre_topc('#skF_1',A_131)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_131))))
      | ~ l1_pre_topc(A_131) ) ),
    inference(resolution,[status(thm)],[c_829,c_969])).

tff(c_6515,plain,(
    ! [A_271] :
      ( ~ v1_tops_2(u1_pre_topc('#skF_2'),A_271)
      | ~ m1_pre_topc('#skF_1',A_271)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_271))))
      | ~ l1_pre_topc(A_271) ) ),
    inference(negUnitSimplification,[status(thm)],[c_965,c_971])).

tff(c_6547,plain,
    ( ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_2')
    | ~ m1_pre_topc('#skF_1','#skF_2')
    | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_650,c_6515])).

tff(c_6582,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_829,c_651,c_1685,c_6547])).

tff(c_6583,plain,(
    r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_922])).

tff(c_6586,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_1')
    | ~ r1_tarski(u1_pre_topc('#skF_1'),u1_pre_topc('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6583,c_2])).

tff(c_6589,plain,(
    ~ r1_tarski(u1_pre_topc('#skF_1'),u1_pre_topc('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_835,c_6586])).

tff(c_307,plain,(
    ! [B_95,A_96] :
      ( r1_tarski(B_95,u1_pre_topc(A_96))
      | ~ v1_tops_2(B_95,A_96)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_96))))
      | ~ l1_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_317,plain,(
    ! [A_5,A_96] :
      ( r1_tarski(A_5,u1_pre_topc(A_96))
      | ~ v1_tops_2(A_5,A_96)
      | ~ l1_pre_topc(A_96)
      | ~ r1_tarski(A_5,k1_zfmisc_1(u1_struct_0(A_96))) ) ),
    inference(resolution,[status(thm)],[c_12,c_307])).

tff(c_737,plain,(
    ! [A_5] :
      ( r1_tarski(A_5,u1_pre_topc('#skF_2'))
      | ~ v1_tops_2(A_5,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_5,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_650,c_317])).

tff(c_7315,plain,(
    ! [A_294] :
      ( r1_tarski(A_294,u1_pre_topc('#skF_2'))
      | ~ v1_tops_2(A_294,'#skF_2')
      | ~ r1_tarski(A_294,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_737])).

tff(c_7332,plain,
    ( r1_tarski(u1_pre_topc('#skF_1'),u1_pre_topc('#skF_2'))
    | ~ v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_104,c_7315])).

tff(c_7347,plain,
    ( r1_tarski(u1_pre_topc('#skF_1'),u1_pre_topc('#skF_2'))
    | ~ v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_7332])).

tff(c_7348,plain,(
    ~ v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_6589,c_7347])).

tff(c_274,plain,(
    ! [A_93] :
      ( m1_pre_topc(A_93,'#skF_1')
      | ~ m1_pre_topc(A_93,'#skF_2')
      | ~ l1_pre_topc(A_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_262])).

tff(c_664,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_651,c_274])).

tff(c_677,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_664])).

tff(c_154,plain,(
    ! [B_84,A_85] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_84),u1_pre_topc(B_84)),A_85)
      | ~ m1_pre_topc(B_84,A_85)
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_14,plain,(
    ! [B_9,A_7] :
      ( l1_pre_topc(B_9)
      | ~ m1_pre_topc(B_9,A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_211,plain,(
    ! [B_89,A_90] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(B_89),u1_pre_topc(B_89)))
      | ~ m1_pre_topc(B_89,A_90)
      | ~ l1_pre_topc(A_90) ) ),
    inference(resolution,[status(thm)],[c_154,c_14])).

tff(c_226,plain,(
    ! [A_91] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_91),u1_pre_topc(A_91)))
      | ~ l1_pre_topc(A_91) ) ),
    inference(resolution,[status(thm)],[c_36,c_211])).

tff(c_229,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_226])).

tff(c_231,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_229])).

tff(c_170,plain,(
    ! [A_85] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),A_85)
      | ~ m1_pre_topc('#skF_2',A_85)
      | ~ l1_pre_topc(A_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_154])).

tff(c_285,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_1')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_170,c_281])).

tff(c_299,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_231,c_285])).

tff(c_334,plain,(
    ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_299])).

tff(c_337,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_193,c_334])).

tff(c_344,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_306,c_337])).

tff(c_346,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitRight,[status(thm)],[c_299])).

tff(c_345,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_299])).

tff(c_198,plain,(
    ! [A_86] :
      ( m1_pre_topc(A_86,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_pre_topc(A_86,'#skF_2')
      | ~ l1_pre_topc(A_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_190])).

tff(c_603,plain,(
    ! [A_86] :
      ( u1_struct_0(A_86) = u1_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ m1_pre_topc('#skF_2',A_86)
      | ~ m1_pre_topc(A_86,'#skF_1')
      | ~ l1_pre_topc(A_86) ) ),
    inference(resolution,[status(thm)],[c_193,c_589])).

tff(c_631,plain,(
    ! [A_86] :
      ( u1_struct_0(A_86) = u1_struct_0('#skF_2')
      | ~ m1_pre_topc('#skF_2',A_86)
      | ~ m1_pre_topc(A_86,'#skF_1')
      | ~ l1_pre_topc(A_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_603])).

tff(c_6903,plain,(
    ! [A_285] :
      ( u1_struct_0(A_285) = u1_struct_0('#skF_1')
      | ~ m1_pre_topc('#skF_2',A_285)
      | ~ m1_pre_topc(A_285,'#skF_1')
      | ~ l1_pre_topc(A_285) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_650,c_631])).

tff(c_6910,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1')
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_1')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_198,c_6903])).

tff(c_6929,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_346,c_231,c_345,c_6910])).

tff(c_546,plain,(
    ! [C_111,A_112,B_113] :
      ( m1_subset_1(C_111,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_112))))
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_113))))
      | ~ m1_pre_topc(B_113,A_112)
      | ~ l1_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6841,plain,(
    ! [A_282,A_283,B_284] :
      ( m1_subset_1(A_282,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_283))))
      | ~ m1_pre_topc(B_284,A_283)
      | ~ l1_pre_topc(A_283)
      | ~ r1_tarski(A_282,k1_zfmisc_1(u1_struct_0(B_284))) ) ),
    inference(resolution,[status(thm)],[c_12,c_546])).

tff(c_6895,plain,(
    ! [A_282,A_85] :
      ( m1_subset_1(A_282,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_85))))
      | ~ r1_tarski(A_282,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
      | ~ m1_pre_topc('#skF_2',A_85)
      | ~ l1_pre_topc(A_85) ) ),
    inference(resolution,[status(thm)],[c_170,c_6841])).

tff(c_7087,plain,(
    ! [A_286,A_287] :
      ( m1_subset_1(A_286,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_287))))
      | ~ r1_tarski(A_286,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_pre_topc('#skF_2',A_287)
      | ~ l1_pre_topc(A_287) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6929,c_6895])).

tff(c_9054,plain,(
    ! [A_341,A_342] :
      ( r1_tarski(A_341,k1_zfmisc_1(u1_struct_0(A_342)))
      | ~ r1_tarski(A_341,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_pre_topc('#skF_2',A_342)
      | ~ l1_pre_topc(A_342) ) ),
    inference(resolution,[status(thm)],[c_7087,c_10])).

tff(c_9069,plain,(
    ! [A_342] :
      ( r1_tarski(u1_pre_topc('#skF_1'),k1_zfmisc_1(u1_struct_0(A_342)))
      | ~ m1_pre_topc('#skF_2',A_342)
      | ~ l1_pre_topc(A_342)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_104,c_9054])).

tff(c_9216,plain,(
    ! [A_346] :
      ( r1_tarski(u1_pre_topc('#skF_1'),k1_zfmisc_1(u1_struct_0(A_346)))
      | ~ m1_pre_topc('#skF_2',A_346)
      | ~ l1_pre_topc(A_346) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_9069])).

tff(c_9241,plain,
    ( r1_tarski(u1_pre_topc('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_650,c_9216])).

tff(c_9259,plain,(
    r1_tarski(u1_pre_topc('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_346,c_9241])).

tff(c_559,plain,(
    ! [A_115,A_116] :
      ( m1_subset_1(u1_pre_topc(A_115),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_116))))
      | ~ m1_pre_topc(A_115,A_116)
      | ~ l1_pre_topc(A_116)
      | ~ l1_pre_topc(A_115) ) ),
    inference(resolution,[status(thm)],[c_16,c_546])).

tff(c_574,plain,(
    ! [A_115,A_116] :
      ( r1_tarski(u1_pre_topc(A_115),k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ m1_pre_topc(A_115,A_116)
      | ~ l1_pre_topc(A_116)
      | ~ l1_pre_topc(A_115) ) ),
    inference(resolution,[status(thm)],[c_559,c_10])).

tff(c_717,plain,(
    ! [A_115] :
      ( r1_tarski(u1_pre_topc(A_115),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_pre_topc(A_115,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_115) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_650,c_574])).

tff(c_6825,plain,(
    ! [A_281] :
      ( r1_tarski(u1_pre_topc(A_281),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_pre_topc(A_281,'#skF_2')
      | ~ l1_pre_topc(A_281) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_717])).

tff(c_6828,plain,(
    ! [A_281] :
      ( v1_tops_2(u1_pre_topc(A_281),'#skF_1')
      | ~ r1_tarski(u1_pre_topc(A_281),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_pre_topc(A_281,'#skF_2')
      | ~ l1_pre_topc(A_281) ) ),
    inference(resolution,[status(thm)],[c_6825,c_448])).

tff(c_8431,plain,(
    ! [A_324] :
      ( v1_tops_2(u1_pre_topc(A_324),'#skF_1')
      | ~ r1_tarski(u1_pre_topc(A_324),u1_pre_topc('#skF_1'))
      | ~ m1_pre_topc(A_324,'#skF_2')
      | ~ l1_pre_topc(A_324) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_6828])).

tff(c_8438,plain,
    ( v1_tops_2(u1_pre_topc('#skF_1'),'#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_8431])).

tff(c_8444,plain,(
    v1_tops_2(u1_pre_topc('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_651,c_8438])).

tff(c_24,plain,(
    ! [C_23,A_17,B_21] :
      ( m1_subset_1(C_23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_17))))
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_21))))
      | ~ m1_pre_topc(B_21,A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_9368,plain,(
    ! [A_349,A_350,A_351] :
      ( m1_subset_1(u1_pre_topc(A_349),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_350))))
      | ~ m1_pre_topc(A_351,A_350)
      | ~ l1_pre_topc(A_350)
      | ~ m1_pre_topc(A_349,A_351)
      | ~ l1_pre_topc(A_351)
      | ~ l1_pre_topc(A_349) ) ),
    inference(resolution,[status(thm)],[c_559,c_24])).

tff(c_9398,plain,(
    ! [A_349,A_86] :
      ( m1_subset_1(u1_pre_topc(A_349),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_pre_topc(A_349,A_86)
      | ~ l1_pre_topc(A_349)
      | ~ m1_pre_topc(A_86,'#skF_2')
      | ~ l1_pre_topc(A_86) ) ),
    inference(resolution,[status(thm)],[c_198,c_9368])).

tff(c_10232,plain,(
    ! [A_373,A_374] :
      ( m1_subset_1(u1_pre_topc(A_373),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_pre_topc(A_373,A_374)
      | ~ l1_pre_topc(A_373)
      | ~ m1_pre_topc(A_374,'#skF_2')
      | ~ l1_pre_topc(A_374) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_6929,c_9398])).

tff(c_10254,plain,
    ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ m1_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_677,c_10232])).

tff(c_10301,plain,(
    m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_651,c_10254])).

tff(c_10359,plain,(
    ! [A_17] :
      ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_17))))
      | ~ m1_pre_topc('#skF_1',A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(resolution,[status(thm)],[c_10301,c_24])).

tff(c_6592,plain,(
    ! [D_272,C_273,A_274] :
      ( v1_tops_2(D_272,C_273)
      | ~ m1_subset_1(D_272,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_273))))
      | ~ v1_tops_2(D_272,A_274)
      | ~ m1_pre_topc(C_273,A_274)
      | ~ m1_subset_1(D_272,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_274))))
      | ~ l1_pre_topc(A_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_7684,plain,(
    ! [A_303,C_304,A_305] :
      ( v1_tops_2(A_303,C_304)
      | ~ v1_tops_2(A_303,A_305)
      | ~ m1_pre_topc(C_304,A_305)
      | ~ m1_subset_1(A_303,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_305))))
      | ~ l1_pre_topc(A_305)
      | ~ r1_tarski(A_303,k1_zfmisc_1(u1_struct_0(C_304))) ) ),
    inference(resolution,[status(thm)],[c_12,c_6592])).

tff(c_7704,plain,(
    ! [A_303] :
      ( v1_tops_2(A_303,'#skF_2')
      | ~ v1_tops_2(A_303,'#skF_1')
      | ~ m1_subset_1(A_303,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_303,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_306,c_7684])).

tff(c_13862,plain,(
    ! [A_452] :
      ( v1_tops_2(A_452,'#skF_2')
      | ~ v1_tops_2(A_452,'#skF_1')
      | ~ m1_subset_1(A_452,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ r1_tarski(A_452,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_650,c_58,c_7704])).

tff(c_13897,plain,
    ( v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2')
    | ~ v1_tops_2(u1_pre_topc('#skF_1'),'#skF_1')
    | ~ r1_tarski(u1_pre_topc('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10359,c_13862])).

tff(c_13968,plain,(
    v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_677,c_9259,c_8444,c_13897])).

tff(c_13970,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7348,c_13968])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:01:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.95/3.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.95/3.18  
% 8.95/3.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.95/3.18  %$ v1_tops_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_tdlat_3 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k1_enumset1 > k2_tarski > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 8.95/3.18  
% 8.95/3.18  %Foreground sorts:
% 8.95/3.18  
% 8.95/3.18  
% 8.95/3.18  %Background operators:
% 8.95/3.18  
% 8.95/3.18  
% 8.95/3.18  %Foreground operators:
% 8.95/3.18  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 8.95/3.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.95/3.18  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 8.95/3.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.95/3.18  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 8.95/3.18  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.95/3.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.95/3.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.95/3.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.95/3.18  tff('#skF_2', type, '#skF_2': $i).
% 8.95/3.18  tff('#skF_1', type, '#skF_1': $i).
% 8.95/3.18  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 8.95/3.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.95/3.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.95/3.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.95/3.18  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 8.95/3.18  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.95/3.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.95/3.18  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 8.95/3.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.95/3.18  
% 9.18/3.21  tff(f_158, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & v2_tdlat_3(A)) => v2_tdlat_3(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_tex_2)).
% 9.18/3.21  tff(f_146, axiom, (![A]: (l1_pre_topc(A) => (v2_tdlat_3(A) <=> (u1_pre_topc(A) = k2_tarski(k1_xboole_0, u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tdlat_3)).
% 9.18/3.21  tff(f_113, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 9.18/3.21  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 9.18/3.21  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 9.18/3.21  tff(f_120, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 9.18/3.21  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.18/3.21  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 9.18/3.21  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.18/3.21  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> r1_tarski(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_tops_2)).
% 9.18/3.21  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_pre_topc(C, A) => (v1_tops_2(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C)))) => ((D = B) => v1_tops_2(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tops_2)).
% 9.18/3.21  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tmap_1)).
% 9.18/3.21  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 9.18/3.21  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_tops_2)).
% 9.18/3.21  tff(c_58, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 9.18/3.21  tff(c_52, plain, (v2_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 9.18/3.21  tff(c_48, plain, (![A_57]: (k2_tarski(k1_xboole_0, u1_struct_0(A_57))=u1_pre_topc(A_57) | ~v2_tdlat_3(A_57) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_146])).
% 9.18/3.21  tff(c_50, plain, (~v2_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 9.18/3.21  tff(c_56, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 9.18/3.21  tff(c_36, plain, (![A_45]: (m1_pre_topc(A_45, A_45) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.18/3.21  tff(c_175, plain, (![A_86, B_87]: (m1_pre_topc(A_86, g1_pre_topc(u1_struct_0(B_87), u1_pre_topc(B_87))) | ~m1_pre_topc(A_86, B_87) | ~l1_pre_topc(B_87) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.18/3.21  tff(c_54, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 9.18/3.21  tff(c_137, plain, (![B_81, A_82]: (m1_pre_topc(B_81, A_82) | ~m1_pre_topc(B_81, g1_pre_topc(u1_struct_0(A_82), u1_pre_topc(A_82))) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.18/3.21  tff(c_140, plain, (![B_81]: (m1_pre_topc(B_81, '#skF_2') | ~m1_pre_topc(B_81, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_54, c_137])).
% 9.18/3.21  tff(c_146, plain, (![B_81]: (m1_pre_topc(B_81, '#skF_2') | ~m1_pre_topc(B_81, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_140])).
% 9.18/3.21  tff(c_179, plain, (![A_86]: (m1_pre_topc(A_86, '#skF_2') | ~m1_pre_topc(A_86, '#skF_1') | ~l1_pre_topc('#skF_1') | ~l1_pre_topc(A_86))), inference(resolution, [status(thm)], [c_175, c_146])).
% 9.18/3.21  tff(c_193, plain, (![A_86]: (m1_pre_topc(A_86, '#skF_2') | ~m1_pre_topc(A_86, '#skF_1') | ~l1_pre_topc(A_86))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_179])).
% 9.18/3.21  tff(c_190, plain, (![A_86]: (m1_pre_topc(A_86, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_pre_topc(A_86, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_86))), inference(superposition, [status(thm), theory('equality')], [c_54, c_175])).
% 9.18/3.21  tff(c_254, plain, (![A_93]: (m1_pre_topc(A_93, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_pre_topc(A_93, '#skF_2') | ~l1_pre_topc(A_93))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_190])).
% 9.18/3.21  tff(c_18, plain, (![B_13, A_11]: (m1_pre_topc(B_13, A_11) | ~m1_pre_topc(B_13, g1_pre_topc(u1_struct_0(A_11), u1_pre_topc(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.18/3.21  tff(c_262, plain, (![A_93]: (m1_pre_topc(A_93, '#skF_1') | ~l1_pre_topc('#skF_1') | ~m1_pre_topc(A_93, '#skF_2') | ~l1_pre_topc(A_93))), inference(resolution, [status(thm)], [c_254, c_18])).
% 9.18/3.21  tff(c_281, plain, (![A_94]: (m1_pre_topc(A_94, '#skF_1') | ~m1_pre_topc(A_94, '#skF_2') | ~l1_pre_topc(A_94))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_262])).
% 9.18/3.21  tff(c_296, plain, (m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_36, c_281])).
% 9.18/3.21  tff(c_306, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_296])).
% 9.18/3.21  tff(c_38, plain, (![B_48, A_46]: (r1_tarski(u1_struct_0(B_48), u1_struct_0(A_46)) | ~m1_pre_topc(B_48, A_46) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.18/3.21  tff(c_123, plain, (![B_76, A_77]: (r1_tarski(u1_struct_0(B_76), u1_struct_0(A_77)) | ~m1_pre_topc(B_76, A_77) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.18/3.21  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.18/3.21  tff(c_474, plain, (![B_102, A_103]: (u1_struct_0(B_102)=u1_struct_0(A_103) | ~r1_tarski(u1_struct_0(A_103), u1_struct_0(B_102)) | ~m1_pre_topc(B_102, A_103) | ~l1_pre_topc(A_103))), inference(resolution, [status(thm)], [c_123, c_2])).
% 9.18/3.21  tff(c_589, plain, (![B_119, A_120]: (u1_struct_0(B_119)=u1_struct_0(A_120) | ~m1_pre_topc(A_120, B_119) | ~l1_pre_topc(B_119) | ~m1_pre_topc(B_119, A_120) | ~l1_pre_topc(A_120))), inference(resolution, [status(thm)], [c_38, c_474])).
% 9.18/3.21  tff(c_597, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1') | ~m1_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_306, c_589])).
% 9.18/3.21  tff(c_622, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1') | ~m1_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_597])).
% 9.18/3.21  tff(c_636, plain, (~m1_pre_topc('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_622])).
% 9.18/3.21  tff(c_639, plain, (~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_193, c_636])).
% 9.18/3.21  tff(c_642, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_639])).
% 9.18/3.21  tff(c_645, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_642])).
% 9.18/3.21  tff(c_649, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_645])).
% 9.18/3.21  tff(c_650, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_622])).
% 9.18/3.21  tff(c_46, plain, (![A_57]: (v2_tdlat_3(A_57) | k2_tarski(k1_xboole_0, u1_struct_0(A_57))!=u1_pre_topc(A_57) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_146])).
% 9.18/3.21  tff(c_776, plain, (v2_tdlat_3('#skF_2') | k2_tarski(k1_xboole_0, u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_650, c_46])).
% 9.18/3.21  tff(c_822, plain, (v2_tdlat_3('#skF_2') | k2_tarski(k1_xboole_0, u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_776])).
% 9.18/3.21  tff(c_823, plain, (k2_tarski(k1_xboole_0, u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_822])).
% 9.18/3.21  tff(c_833, plain, (u1_pre_topc('#skF_2')!=u1_pre_topc('#skF_1') | ~v2_tdlat_3('#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_48, c_823])).
% 9.18/3.21  tff(c_835, plain, (u1_pre_topc('#skF_2')!=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_52, c_833])).
% 9.18/3.21  tff(c_16, plain, (![A_10]: (m1_subset_1(u1_pre_topc(A_10), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_10)))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.18/3.21  tff(c_785, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_650, c_16])).
% 9.18/3.21  tff(c_829, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_785])).
% 9.18/3.21  tff(c_651, plain, (m1_pre_topc('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_622])).
% 9.18/3.21  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.18/3.21  tff(c_100, plain, (![A_72]: (m1_subset_1(u1_pre_topc(A_72), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_72)))) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.18/3.21  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.18/3.21  tff(c_104, plain, (![A_72]: (r1_tarski(u1_pre_topc(A_72), k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72))), inference(resolution, [status(thm)], [c_100, c_10])).
% 9.18/3.21  tff(c_779, plain, (r1_tarski(u1_pre_topc('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_650, c_104])).
% 9.18/3.21  tff(c_825, plain, (r1_tarski(u1_pre_topc('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_779])).
% 9.18/3.21  tff(c_12, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.18/3.21  tff(c_437, plain, (![B_99, A_100]: (v1_tops_2(B_99, A_100) | ~r1_tarski(B_99, u1_pre_topc(A_100)) | ~m1_subset_1(B_99, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_100)))) | ~l1_pre_topc(A_100))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.18/3.21  tff(c_448, plain, (![A_5, A_100]: (v1_tops_2(A_5, A_100) | ~r1_tarski(A_5, u1_pre_topc(A_100)) | ~l1_pre_topc(A_100) | ~r1_tarski(A_5, k1_zfmisc_1(u1_struct_0(A_100))))), inference(resolution, [status(thm)], [c_12, c_437])).
% 9.18/3.21  tff(c_728, plain, (![A_5]: (v1_tops_2(A_5, '#skF_2') | ~r1_tarski(A_5, u1_pre_topc('#skF_2')) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_5, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_650, c_448])).
% 9.18/3.21  tff(c_1659, plain, (![A_149]: (v1_tops_2(A_149, '#skF_2') | ~r1_tarski(A_149, u1_pre_topc('#skF_2')) | ~r1_tarski(A_149, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_728])).
% 9.18/3.21  tff(c_1668, plain, (v1_tops_2(u1_pre_topc('#skF_2'), '#skF_2') | ~r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_825, c_1659])).
% 9.18/3.21  tff(c_1685, plain, (v1_tops_2(u1_pre_topc('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1668])).
% 9.18/3.21  tff(c_30, plain, (![B_41, A_39]: (r1_tarski(B_41, u1_pre_topc(A_39)) | ~v1_tops_2(B_41, A_39) | ~m1_subset_1(B_41, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_39)))) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.18/3.21  tff(c_912, plain, (r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_1')) | ~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_829, c_30])).
% 9.18/3.21  tff(c_922, plain, (r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_1')) | ~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_912])).
% 9.18/3.21  tff(c_965, plain, (~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_922])).
% 9.18/3.21  tff(c_969, plain, (![D_129, C_130, A_131]: (v1_tops_2(D_129, C_130) | ~m1_subset_1(D_129, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_130)))) | ~v1_tops_2(D_129, A_131) | ~m1_pre_topc(C_130, A_131) | ~m1_subset_1(D_129, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_131)))) | ~l1_pre_topc(A_131))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.18/3.21  tff(c_971, plain, (![A_131]: (v1_tops_2(u1_pre_topc('#skF_2'), '#skF_1') | ~v1_tops_2(u1_pre_topc('#skF_2'), A_131) | ~m1_pre_topc('#skF_1', A_131) | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_131)))) | ~l1_pre_topc(A_131))), inference(resolution, [status(thm)], [c_829, c_969])).
% 9.18/3.21  tff(c_6515, plain, (![A_271]: (~v1_tops_2(u1_pre_topc('#skF_2'), A_271) | ~m1_pre_topc('#skF_1', A_271) | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_271)))) | ~l1_pre_topc(A_271))), inference(negUnitSimplification, [status(thm)], [c_965, c_971])).
% 9.18/3.21  tff(c_6547, plain, (~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_2') | ~m1_pre_topc('#skF_1', '#skF_2') | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_650, c_6515])).
% 9.18/3.21  tff(c_6582, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_829, c_651, c_1685, c_6547])).
% 9.18/3.21  tff(c_6583, plain, (r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_1'))), inference(splitRight, [status(thm)], [c_922])).
% 9.18/3.21  tff(c_6586, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_1') | ~r1_tarski(u1_pre_topc('#skF_1'), u1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_6583, c_2])).
% 9.18/3.21  tff(c_6589, plain, (~r1_tarski(u1_pre_topc('#skF_1'), u1_pre_topc('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_835, c_6586])).
% 9.18/3.21  tff(c_307, plain, (![B_95, A_96]: (r1_tarski(B_95, u1_pre_topc(A_96)) | ~v1_tops_2(B_95, A_96) | ~m1_subset_1(B_95, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_96)))) | ~l1_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.18/3.21  tff(c_317, plain, (![A_5, A_96]: (r1_tarski(A_5, u1_pre_topc(A_96)) | ~v1_tops_2(A_5, A_96) | ~l1_pre_topc(A_96) | ~r1_tarski(A_5, k1_zfmisc_1(u1_struct_0(A_96))))), inference(resolution, [status(thm)], [c_12, c_307])).
% 9.18/3.21  tff(c_737, plain, (![A_5]: (r1_tarski(A_5, u1_pre_topc('#skF_2')) | ~v1_tops_2(A_5, '#skF_2') | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_5, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_650, c_317])).
% 9.18/3.21  tff(c_7315, plain, (![A_294]: (r1_tarski(A_294, u1_pre_topc('#skF_2')) | ~v1_tops_2(A_294, '#skF_2') | ~r1_tarski(A_294, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_737])).
% 9.18/3.21  tff(c_7332, plain, (r1_tarski(u1_pre_topc('#skF_1'), u1_pre_topc('#skF_2')) | ~v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_104, c_7315])).
% 9.18/3.21  tff(c_7347, plain, (r1_tarski(u1_pre_topc('#skF_1'), u1_pre_topc('#skF_2')) | ~v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_7332])).
% 9.18/3.21  tff(c_7348, plain, (~v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_6589, c_7347])).
% 9.18/3.21  tff(c_274, plain, (![A_93]: (m1_pre_topc(A_93, '#skF_1') | ~m1_pre_topc(A_93, '#skF_2') | ~l1_pre_topc(A_93))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_262])).
% 9.18/3.21  tff(c_664, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_651, c_274])).
% 9.18/3.21  tff(c_677, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_664])).
% 9.18/3.21  tff(c_154, plain, (![B_84, A_85]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_84), u1_pre_topc(B_84)), A_85) | ~m1_pre_topc(B_84, A_85) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.18/3.21  tff(c_14, plain, (![B_9, A_7]: (l1_pre_topc(B_9) | ~m1_pre_topc(B_9, A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.18/3.21  tff(c_211, plain, (![B_89, A_90]: (l1_pre_topc(g1_pre_topc(u1_struct_0(B_89), u1_pre_topc(B_89))) | ~m1_pre_topc(B_89, A_90) | ~l1_pre_topc(A_90))), inference(resolution, [status(thm)], [c_154, c_14])).
% 9.18/3.21  tff(c_226, plain, (![A_91]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_91), u1_pre_topc(A_91))) | ~l1_pre_topc(A_91))), inference(resolution, [status(thm)], [c_36, c_211])).
% 9.18/3.21  tff(c_229, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_54, c_226])).
% 9.18/3.21  tff(c_231, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_229])).
% 9.18/3.21  tff(c_170, plain, (![A_85]: (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), A_85) | ~m1_pre_topc('#skF_2', A_85) | ~l1_pre_topc(A_85))), inference(superposition, [status(thm), theory('equality')], [c_54, c_154])).
% 9.18/3.21  tff(c_285, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_1') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_170, c_281])).
% 9.18/3.21  tff(c_299, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_1') | ~m1_pre_topc('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_231, c_285])).
% 9.18/3.21  tff(c_334, plain, (~m1_pre_topc('#skF_2', '#skF_2')), inference(splitLeft, [status(thm)], [c_299])).
% 9.18/3.21  tff(c_337, plain, (~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_193, c_334])).
% 9.18/3.21  tff(c_344, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_306, c_337])).
% 9.18/3.21  tff(c_346, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(splitRight, [status(thm)], [c_299])).
% 9.18/3.21  tff(c_345, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_1')), inference(splitRight, [status(thm)], [c_299])).
% 9.18/3.21  tff(c_198, plain, (![A_86]: (m1_pre_topc(A_86, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_pre_topc(A_86, '#skF_2') | ~l1_pre_topc(A_86))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_190])).
% 9.18/3.21  tff(c_603, plain, (![A_86]: (u1_struct_0(A_86)=u1_struct_0('#skF_2') | ~l1_pre_topc('#skF_2') | ~m1_pre_topc('#skF_2', A_86) | ~m1_pre_topc(A_86, '#skF_1') | ~l1_pre_topc(A_86))), inference(resolution, [status(thm)], [c_193, c_589])).
% 9.18/3.21  tff(c_631, plain, (![A_86]: (u1_struct_0(A_86)=u1_struct_0('#skF_2') | ~m1_pre_topc('#skF_2', A_86) | ~m1_pre_topc(A_86, '#skF_1') | ~l1_pre_topc(A_86))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_603])).
% 9.18/3.21  tff(c_6903, plain, (![A_285]: (u1_struct_0(A_285)=u1_struct_0('#skF_1') | ~m1_pre_topc('#skF_2', A_285) | ~m1_pre_topc(A_285, '#skF_1') | ~l1_pre_topc(A_285))), inference(demodulation, [status(thm), theory('equality')], [c_650, c_631])).
% 9.18/3.21  tff(c_6910, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1') | ~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_1') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_198, c_6903])).
% 9.18/3.21  tff(c_6929, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_346, c_231, c_345, c_6910])).
% 9.18/3.21  tff(c_546, plain, (![C_111, A_112, B_113]: (m1_subset_1(C_111, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_112)))) | ~m1_subset_1(C_111, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_113)))) | ~m1_pre_topc(B_113, A_112) | ~l1_pre_topc(A_112))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.18/3.21  tff(c_6841, plain, (![A_282, A_283, B_284]: (m1_subset_1(A_282, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_283)))) | ~m1_pre_topc(B_284, A_283) | ~l1_pre_topc(A_283) | ~r1_tarski(A_282, k1_zfmisc_1(u1_struct_0(B_284))))), inference(resolution, [status(thm)], [c_12, c_546])).
% 9.18/3.21  tff(c_6895, plain, (![A_282, A_85]: (m1_subset_1(A_282, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_85)))) | ~r1_tarski(A_282, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~m1_pre_topc('#skF_2', A_85) | ~l1_pre_topc(A_85))), inference(resolution, [status(thm)], [c_170, c_6841])).
% 9.18/3.21  tff(c_7087, plain, (![A_286, A_287]: (m1_subset_1(A_286, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_287)))) | ~r1_tarski(A_286, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_pre_topc('#skF_2', A_287) | ~l1_pre_topc(A_287))), inference(demodulation, [status(thm), theory('equality')], [c_6929, c_6895])).
% 9.18/3.21  tff(c_9054, plain, (![A_341, A_342]: (r1_tarski(A_341, k1_zfmisc_1(u1_struct_0(A_342))) | ~r1_tarski(A_341, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_pre_topc('#skF_2', A_342) | ~l1_pre_topc(A_342))), inference(resolution, [status(thm)], [c_7087, c_10])).
% 9.18/3.21  tff(c_9069, plain, (![A_342]: (r1_tarski(u1_pre_topc('#skF_1'), k1_zfmisc_1(u1_struct_0(A_342))) | ~m1_pre_topc('#skF_2', A_342) | ~l1_pre_topc(A_342) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_104, c_9054])).
% 9.18/3.21  tff(c_9216, plain, (![A_346]: (r1_tarski(u1_pre_topc('#skF_1'), k1_zfmisc_1(u1_struct_0(A_346))) | ~m1_pre_topc('#skF_2', A_346) | ~l1_pre_topc(A_346))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_9069])).
% 9.18/3.21  tff(c_9241, plain, (r1_tarski(u1_pre_topc('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_650, c_9216])).
% 9.18/3.21  tff(c_9259, plain, (r1_tarski(u1_pre_topc('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_346, c_9241])).
% 9.18/3.21  tff(c_559, plain, (![A_115, A_116]: (m1_subset_1(u1_pre_topc(A_115), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_116)))) | ~m1_pre_topc(A_115, A_116) | ~l1_pre_topc(A_116) | ~l1_pre_topc(A_115))), inference(resolution, [status(thm)], [c_16, c_546])).
% 9.18/3.21  tff(c_574, plain, (![A_115, A_116]: (r1_tarski(u1_pre_topc(A_115), k1_zfmisc_1(u1_struct_0(A_116))) | ~m1_pre_topc(A_115, A_116) | ~l1_pre_topc(A_116) | ~l1_pre_topc(A_115))), inference(resolution, [status(thm)], [c_559, c_10])).
% 9.18/3.21  tff(c_717, plain, (![A_115]: (r1_tarski(u1_pre_topc(A_115), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_pre_topc(A_115, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_115))), inference(superposition, [status(thm), theory('equality')], [c_650, c_574])).
% 9.18/3.21  tff(c_6825, plain, (![A_281]: (r1_tarski(u1_pre_topc(A_281), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_pre_topc(A_281, '#skF_2') | ~l1_pre_topc(A_281))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_717])).
% 9.18/3.21  tff(c_6828, plain, (![A_281]: (v1_tops_2(u1_pre_topc(A_281), '#skF_1') | ~r1_tarski(u1_pre_topc(A_281), u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1') | ~m1_pre_topc(A_281, '#skF_2') | ~l1_pre_topc(A_281))), inference(resolution, [status(thm)], [c_6825, c_448])).
% 9.18/3.21  tff(c_8431, plain, (![A_324]: (v1_tops_2(u1_pre_topc(A_324), '#skF_1') | ~r1_tarski(u1_pre_topc(A_324), u1_pre_topc('#skF_1')) | ~m1_pre_topc(A_324, '#skF_2') | ~l1_pre_topc(A_324))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_6828])).
% 9.18/3.21  tff(c_8438, plain, (v1_tops_2(u1_pre_topc('#skF_1'), '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_8431])).
% 9.18/3.21  tff(c_8444, plain, (v1_tops_2(u1_pre_topc('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_651, c_8438])).
% 9.18/3.21  tff(c_24, plain, (![C_23, A_17, B_21]: (m1_subset_1(C_23, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_17)))) | ~m1_subset_1(C_23, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_21)))) | ~m1_pre_topc(B_21, A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.18/3.21  tff(c_9368, plain, (![A_349, A_350, A_351]: (m1_subset_1(u1_pre_topc(A_349), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_350)))) | ~m1_pre_topc(A_351, A_350) | ~l1_pre_topc(A_350) | ~m1_pre_topc(A_349, A_351) | ~l1_pre_topc(A_351) | ~l1_pre_topc(A_349))), inference(resolution, [status(thm)], [c_559, c_24])).
% 9.18/3.21  tff(c_9398, plain, (![A_349, A_86]: (m1_subset_1(u1_pre_topc(A_349), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_pre_topc(A_349, A_86) | ~l1_pre_topc(A_349) | ~m1_pre_topc(A_86, '#skF_2') | ~l1_pre_topc(A_86))), inference(resolution, [status(thm)], [c_198, c_9368])).
% 9.18/3.21  tff(c_10232, plain, (![A_373, A_374]: (m1_subset_1(u1_pre_topc(A_373), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_pre_topc(A_373, A_374) | ~l1_pre_topc(A_373) | ~m1_pre_topc(A_374, '#skF_2') | ~l1_pre_topc(A_374))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_6929, c_9398])).
% 9.18/3.21  tff(c_10254, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_677, c_10232])).
% 9.18/3.21  tff(c_10301, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_651, c_10254])).
% 9.18/3.21  tff(c_10359, plain, (![A_17]: (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_17)))) | ~m1_pre_topc('#skF_1', A_17) | ~l1_pre_topc(A_17))), inference(resolution, [status(thm)], [c_10301, c_24])).
% 9.18/3.21  tff(c_6592, plain, (![D_272, C_273, A_274]: (v1_tops_2(D_272, C_273) | ~m1_subset_1(D_272, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_273)))) | ~v1_tops_2(D_272, A_274) | ~m1_pre_topc(C_273, A_274) | ~m1_subset_1(D_272, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_274)))) | ~l1_pre_topc(A_274))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.18/3.21  tff(c_7684, plain, (![A_303, C_304, A_305]: (v1_tops_2(A_303, C_304) | ~v1_tops_2(A_303, A_305) | ~m1_pre_topc(C_304, A_305) | ~m1_subset_1(A_303, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_305)))) | ~l1_pre_topc(A_305) | ~r1_tarski(A_303, k1_zfmisc_1(u1_struct_0(C_304))))), inference(resolution, [status(thm)], [c_12, c_6592])).
% 9.18/3.21  tff(c_7704, plain, (![A_303]: (v1_tops_2(A_303, '#skF_2') | ~v1_tops_2(A_303, '#skF_1') | ~m1_subset_1(A_303, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_303, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_306, c_7684])).
% 9.18/3.21  tff(c_13862, plain, (![A_452]: (v1_tops_2(A_452, '#skF_2') | ~v1_tops_2(A_452, '#skF_1') | ~m1_subset_1(A_452, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~r1_tarski(A_452, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_650, c_58, c_7704])).
% 9.18/3.21  tff(c_13897, plain, (v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2') | ~v1_tops_2(u1_pre_topc('#skF_1'), '#skF_1') | ~r1_tarski(u1_pre_topc('#skF_1'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_10359, c_13862])).
% 9.18/3.21  tff(c_13968, plain, (v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_677, c_9259, c_8444, c_13897])).
% 9.18/3.21  tff(c_13970, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7348, c_13968])).
% 9.18/3.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.18/3.21  
% 9.18/3.21  Inference rules
% 9.18/3.21  ----------------------
% 9.18/3.21  #Ref     : 0
% 9.18/3.21  #Sup     : 2798
% 9.18/3.21  #Fact    : 0
% 9.18/3.21  #Define  : 0
% 9.18/3.21  #Split   : 24
% 9.18/3.21  #Chain   : 0
% 9.18/3.21  #Close   : 0
% 9.18/3.21  
% 9.18/3.21  Ordering : KBO
% 9.18/3.21  
% 9.18/3.21  Simplification rules
% 9.18/3.21  ----------------------
% 9.18/3.21  #Subsume      : 664
% 9.18/3.21  #Demod        : 4228
% 9.18/3.21  #Tautology    : 747
% 9.18/3.21  #SimpNegUnit  : 129
% 9.18/3.21  #BackRed      : 5
% 9.18/3.21  
% 9.18/3.21  #Partial instantiations: 0
% 9.18/3.21  #Strategies tried      : 1
% 9.18/3.21  
% 9.18/3.21  Timing (in seconds)
% 9.18/3.21  ----------------------
% 9.18/3.21  Preprocessing        : 0.33
% 9.18/3.21  Parsing              : 0.17
% 9.18/3.21  CNF conversion       : 0.02
% 9.18/3.21  Main loop            : 2.05
% 9.18/3.21  Inferencing          : 0.55
% 9.18/3.21  Reduction            : 0.77
% 9.18/3.21  Demodulation         : 0.57
% 9.18/3.21  BG Simplification    : 0.06
% 9.18/3.21  Subsumption          : 0.53
% 9.18/3.21  Abstraction          : 0.09
% 9.18/3.21  MUC search           : 0.00
% 9.18/3.21  Cooper               : 0.00
% 9.18/3.21  Total                : 2.43
% 9.18/3.21  Index Insertion      : 0.00
% 9.18/3.21  Index Deletion       : 0.00
% 9.18/3.21  Index Matching       : 0.00
% 9.18/3.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
