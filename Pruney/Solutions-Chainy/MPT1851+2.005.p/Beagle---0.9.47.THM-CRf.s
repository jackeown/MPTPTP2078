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
% DateTime   : Thu Dec  3 10:28:58 EST 2020

% Result     : Theorem 4.13s
% Output     : CNFRefutation 4.13s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 936 expanded)
%              Number of leaves         :   28 ( 326 expanded)
%              Depth                    :   21
%              Number of atoms          :  295 (2724 expanded)
%              Number of equality atoms :   19 ( 326 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tops_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_tdlat_3 > l1_pre_topc > k2_tarski > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_127,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                & v2_tdlat_3(A) )
             => v2_tdlat_3(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tex_2)).

tff(f_102,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_109,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
             => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_2)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> r1_tarski(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_tdlat_3(A)
      <=> u1_pre_topc(A) = k2_tarski(k1_xboole_0,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tdlat_3)).

tff(f_85,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_2)).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_42,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_28,plain,(
    ! [A_39] :
      ( m1_pre_topc(A_39,A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_40,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_95,plain,(
    ! [A_59,B_60] :
      ( m1_pre_topc(A_59,g1_pre_topc(u1_struct_0(B_60),u1_pre_topc(B_60)))
      | ~ m1_pre_topc(A_59,B_60)
      | ~ l1_pre_topc(B_60)
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_104,plain,(
    ! [A_59] :
      ( m1_pre_topc(A_59,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_pre_topc(A_59,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_95])).

tff(c_129,plain,(
    ! [A_63] :
      ( m1_pre_topc(A_63,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_pre_topc(A_63,'#skF_2')
      | ~ l1_pre_topc(A_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_104])).

tff(c_12,plain,(
    ! [B_9,A_7] :
      ( m1_pre_topc(B_9,A_7)
      | ~ m1_pre_topc(B_9,g1_pre_topc(u1_struct_0(A_7),u1_pre_topc(A_7)))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_135,plain,(
    ! [A_63] :
      ( m1_pre_topc(A_63,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_pre_topc(A_63,'#skF_2')
      | ~ l1_pre_topc(A_63) ) ),
    inference(resolution,[status(thm)],[c_129,c_12])).

tff(c_145,plain,(
    ! [A_64] :
      ( m1_pre_topc(A_64,'#skF_1')
      | ~ m1_pre_topc(A_64,'#skF_2')
      | ~ l1_pre_topc(A_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_135])).

tff(c_152,plain,
    ( m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_145])).

tff(c_156,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_152])).

tff(c_16,plain,(
    ! [A_10,B_12] :
      ( m1_pre_topc(A_10,g1_pre_topc(u1_struct_0(B_12),u1_pre_topc(B_12)))
      | ~ m1_pre_topc(A_10,B_12)
      | ~ l1_pre_topc(B_12)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_84,plain,(
    ! [B_57,A_58] :
      ( m1_pre_topc(B_57,A_58)
      | ~ m1_pre_topc(B_57,g1_pre_topc(u1_struct_0(A_58),u1_pre_topc(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_87,plain,(
    ! [B_57] :
      ( m1_pre_topc(B_57,'#skF_2')
      | ~ m1_pre_topc(B_57,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_84])).

tff(c_109,plain,(
    ! [B_61] :
      ( m1_pre_topc(B_61,'#skF_2')
      | ~ m1_pre_topc(B_61,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_87])).

tff(c_113,plain,(
    ! [A_10] :
      ( m1_pre_topc(A_10,'#skF_2')
      | ~ m1_pre_topc(A_10,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ l1_pre_topc(A_10) ) ),
    inference(resolution,[status(thm)],[c_16,c_109])).

tff(c_120,plain,(
    ! [A_10] :
      ( m1_pre_topc(A_10,'#skF_2')
      | ~ m1_pre_topc(A_10,'#skF_1')
      | ~ l1_pre_topc(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_113])).

tff(c_30,plain,(
    ! [B_42,A_40] :
      ( r1_tarski(u1_struct_0(B_42),u1_struct_0(A_40))
      | ~ m1_pre_topc(B_42,A_40)
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_80,plain,(
    ! [B_55,A_56] :
      ( r1_tarski(u1_struct_0(B_55),u1_struct_0(A_56))
      | ~ m1_pre_topc(B_55,A_56)
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_163,plain,(
    ! [B_65,A_66] :
      ( u1_struct_0(B_65) = u1_struct_0(A_66)
      | ~ r1_tarski(u1_struct_0(A_66),u1_struct_0(B_65))
      | ~ m1_pre_topc(B_65,A_66)
      | ~ l1_pre_topc(A_66) ) ),
    inference(resolution,[status(thm)],[c_80,c_2])).

tff(c_174,plain,(
    ! [B_67,A_68] :
      ( u1_struct_0(B_67) = u1_struct_0(A_68)
      | ~ m1_pre_topc(A_68,B_67)
      | ~ l1_pre_topc(B_67)
      | ~ m1_pre_topc(B_67,A_68)
      | ~ l1_pre_topc(A_68) ) ),
    inference(resolution,[status(thm)],[c_30,c_163])).

tff(c_176,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_156,c_174])).

tff(c_187,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_176])).

tff(c_201,plain,(
    ~ m1_pre_topc('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_187])).

tff(c_204,plain,
    ( ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_120,c_201])).

tff(c_207,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_204])).

tff(c_210,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_207])).

tff(c_214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_210])).

tff(c_216,plain,(
    m1_pre_topc('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_215,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_10,plain,(
    ! [A_6] :
      ( m1_subset_1(u1_pre_topc(A_6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_6))))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1630,plain,(
    ! [C_125,A_126,B_127] :
      ( m1_subset_1(C_125,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_126))))
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_127))))
      | ~ m1_pre_topc(B_127,A_126)
      | ~ l1_pre_topc(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1854,plain,(
    ! [A_140,A_141] :
      ( m1_subset_1(u1_pre_topc(A_140),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_141))))
      | ~ m1_pre_topc(A_140,A_141)
      | ~ l1_pre_topc(A_141)
      | ~ l1_pre_topc(A_140) ) ),
    inference(resolution,[status(thm)],[c_10,c_1630])).

tff(c_1875,plain,(
    ! [A_140] :
      ( m1_subset_1(u1_pre_topc(A_140),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_pre_topc(A_140,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_140) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_1854])).

tff(c_1888,plain,(
    ! [A_142] :
      ( m1_subset_1(u1_pre_topc(A_142),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_pre_topc(A_142,'#skF_2')
      | ~ l1_pre_topc(A_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1875])).

tff(c_22,plain,(
    ! [B_37,A_35] :
      ( v1_tops_2(B_37,A_35)
      | ~ r1_tarski(B_37,u1_pre_topc(A_35))
      | ~ m1_subset_1(B_37,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_35))))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1901,plain,(
    ! [A_142] :
      ( v1_tops_2(u1_pre_topc(A_142),'#skF_1')
      | ~ r1_tarski(u1_pre_topc(A_142),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_pre_topc(A_142,'#skF_2')
      | ~ l1_pre_topc(A_142) ) ),
    inference(resolution,[status(thm)],[c_1888,c_22])).

tff(c_2047,plain,(
    ! [A_150] :
      ( v1_tops_2(u1_pre_topc(A_150),'#skF_1')
      | ~ r1_tarski(u1_pre_topc(A_150),u1_pre_topc('#skF_1'))
      | ~ m1_pre_topc(A_150,'#skF_2')
      | ~ l1_pre_topc(A_150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1901])).

tff(c_2057,plain,
    ( v1_tops_2(u1_pre_topc('#skF_1'),'#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_2047])).

tff(c_2064,plain,(
    v1_tops_2(u1_pre_topc('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_216,c_2057])).

tff(c_2100,plain,(
    ! [C_152,A_153] :
      ( m1_subset_1(C_152,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_153))))
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_pre_topc('#skF_2',A_153)
      | ~ l1_pre_topc(A_153) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_1630])).

tff(c_2113,plain,(
    ! [A_153] :
      ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_153))))
      | ~ m1_pre_topc('#skF_2',A_153)
      | ~ l1_pre_topc(A_153)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_10,c_2100])).

tff(c_2165,plain,(
    ! [A_155] :
      ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_155))))
      | ~ m1_pre_topc('#skF_2',A_155)
      | ~ l1_pre_topc(A_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2113])).

tff(c_2189,plain,
    ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_2165])).

tff(c_2206,plain,
    ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2189])).

tff(c_2207,plain,(
    ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2206])).

tff(c_2210,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_120,c_2207])).

tff(c_2217,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_156,c_2210])).

tff(c_2218,plain,(
    m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_2206])).

tff(c_38,plain,(
    v2_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_34,plain,(
    ! [A_43] :
      ( k2_tarski(k1_xboole_0,u1_struct_0(A_43)) = u1_pre_topc(A_43)
      | ~ v2_tdlat_3(A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_36,plain,(
    ~ v2_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_32,plain,(
    ! [A_43] :
      ( v2_tdlat_3(A_43)
      | k2_tarski(k1_xboole_0,u1_struct_0(A_43)) != u1_pre_topc(A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_304,plain,
    ( v2_tdlat_3('#skF_2')
    | k2_tarski(k1_xboole_0,u1_struct_0('#skF_1')) != u1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_32])).

tff(c_325,plain,
    ( v2_tdlat_3('#skF_2')
    | k2_tarski(k1_xboole_0,u1_struct_0('#skF_1')) != u1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_304])).

tff(c_326,plain,(
    k2_tarski(k1_xboole_0,u1_struct_0('#skF_1')) != u1_pre_topc('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_325])).

tff(c_335,plain,
    ( u1_pre_topc('#skF_2') != u1_pre_topc('#skF_1')
    | ~ v2_tdlat_3('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_326])).

tff(c_337,plain,(
    u1_pre_topc('#skF_2') != u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_335])).

tff(c_310,plain,
    ( m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_10])).

tff(c_330,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_310])).

tff(c_338,plain,(
    ! [B_72,A_73] :
      ( v1_tops_2(B_72,A_73)
      | ~ r1_tarski(B_72,u1_pre_topc(A_73))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_73))))
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_341,plain,(
    ! [B_72] :
      ( v1_tops_2(B_72,'#skF_2')
      | ~ r1_tarski(B_72,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_338])).

tff(c_583,plain,(
    ! [B_90] :
      ( v1_tops_2(B_90,'#skF_2')
      | ~ r1_tarski(B_90,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_341])).

tff(c_590,plain,
    ( v1_tops_2(u1_pre_topc('#skF_2'),'#skF_2')
    | ~ r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_2')) ),
    inference(resolution,[status(thm)],[c_330,c_583])).

tff(c_600,plain,(
    v1_tops_2(u1_pre_topc('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_590])).

tff(c_354,plain,
    ( v1_tops_2(u1_pre_topc('#skF_2'),'#skF_1')
    | ~ r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_330,c_22])).

tff(c_360,plain,
    ( v1_tops_2(u1_pre_topc('#skF_2'),'#skF_1')
    | ~ r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_354])).

tff(c_380,plain,(
    ~ r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_360])).

tff(c_24,plain,(
    ! [B_37,A_35] :
      ( r1_tarski(B_37,u1_pre_topc(A_35))
      | ~ v1_tops_2(B_37,A_35)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_35))))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_357,plain,
    ( r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_1'))
    | ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_330,c_24])).

tff(c_363,plain,
    ( r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_1'))
    | ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_357])).

tff(c_381,plain,(
    ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_380,c_363])).

tff(c_526,plain,(
    ! [D_85,C_86,A_87] :
      ( v1_tops_2(D_85,C_86)
      | ~ m1_subset_1(D_85,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_86))))
      | ~ v1_tops_2(D_85,A_87)
      | ~ m1_pre_topc(C_86,A_87)
      | ~ m1_subset_1(D_85,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_87))))
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_530,plain,(
    ! [A_87] :
      ( v1_tops_2(u1_pre_topc('#skF_2'),'#skF_1')
      | ~ v1_tops_2(u1_pre_topc('#skF_2'),A_87)
      | ~ m1_pre_topc('#skF_1',A_87)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_87))))
      | ~ l1_pre_topc(A_87) ) ),
    inference(resolution,[status(thm)],[c_330,c_526])).

tff(c_1577,plain,(
    ! [A_124] :
      ( ~ v1_tops_2(u1_pre_topc('#skF_2'),A_124)
      | ~ m1_pre_topc('#skF_1',A_124)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_124))))
      | ~ l1_pre_topc(A_124) ) ),
    inference(negUnitSimplification,[status(thm)],[c_381,c_530])).

tff(c_1601,plain,
    ( ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_2')
    | ~ m1_pre_topc('#skF_1','#skF_2')
    | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_1577])).

tff(c_1622,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_330,c_216,c_600,c_1601])).

tff(c_1624,plain,(
    r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_360])).

tff(c_1626,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_1')
    | ~ r1_tarski(u1_pre_topc('#skF_1'),u1_pre_topc('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1624,c_2])).

tff(c_1629,plain,(
    ~ r1_tarski(u1_pre_topc('#skF_1'),u1_pre_topc('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_337,c_1626])).

tff(c_283,plain,(
    ! [B_37] :
      ( r1_tarski(B_37,u1_pre_topc('#skF_2'))
      | ~ v1_tops_2(B_37,'#skF_2')
      | ~ m1_subset_1(B_37,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_24])).

tff(c_1832,plain,(
    ! [B_139] :
      ( r1_tarski(B_139,u1_pre_topc('#skF_2'))
      | ~ v1_tops_2(B_139,'#skF_2')
      | ~ m1_subset_1(B_139,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_283])).

tff(c_1843,plain,
    ( r1_tarski(u1_pre_topc('#skF_1'),u1_pre_topc('#skF_2'))
    | ~ v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_1832])).

tff(c_1852,plain,
    ( r1_tarski(u1_pre_topc('#skF_1'),u1_pre_topc('#skF_2'))
    | ~ v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1843])).

tff(c_1853,plain,(
    ~ v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_1629,c_1852])).

tff(c_1773,plain,(
    ! [D_133,C_134,A_135] :
      ( v1_tops_2(D_133,C_134)
      | ~ m1_subset_1(D_133,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_134))))
      | ~ v1_tops_2(D_133,A_135)
      | ~ m1_pre_topc(C_134,A_135)
      | ~ m1_subset_1(D_133,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_135))))
      | ~ l1_pre_topc(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2359,plain,(
    ! [D_159,A_160] :
      ( v1_tops_2(D_159,'#skF_2')
      | ~ m1_subset_1(D_159,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ v1_tops_2(D_159,A_160)
      | ~ m1_pre_topc('#skF_2',A_160)
      | ~ m1_subset_1(D_159,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_160))))
      | ~ l1_pre_topc(A_160) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_1773])).

tff(c_2383,plain,(
    ! [A_160] :
      ( v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2')
      | ~ v1_tops_2(u1_pre_topc('#skF_1'),A_160)
      | ~ m1_pre_topc('#skF_2',A_160)
      | ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_160))))
      | ~ l1_pre_topc(A_160)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_10,c_2359])).

tff(c_2409,plain,(
    ! [A_160] :
      ( v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2')
      | ~ v1_tops_2(u1_pre_topc('#skF_1'),A_160)
      | ~ m1_pre_topc('#skF_2',A_160)
      | ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_160))))
      | ~ l1_pre_topc(A_160) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2383])).

tff(c_2735,plain,(
    ! [A_170] :
      ( ~ v1_tops_2(u1_pre_topc('#skF_1'),A_170)
      | ~ m1_pre_topc('#skF_2',A_170)
      | ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_170))))
      | ~ l1_pre_topc(A_170) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1853,c_2409])).

tff(c_2741,plain,
    ( ~ v1_tops_2(u1_pre_topc('#skF_1'),'#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2218,c_2735])).

tff(c_2764,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_156,c_2064,c_2741])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:06:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.13/1.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.13/1.72  
% 4.13/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.13/1.73  %$ v1_tops_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_tdlat_3 > l1_pre_topc > k2_tarski > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 4.13/1.73  
% 4.13/1.73  %Foreground sorts:
% 4.13/1.73  
% 4.13/1.73  
% 4.13/1.73  %Background operators:
% 4.13/1.73  
% 4.13/1.73  
% 4.13/1.73  %Foreground operators:
% 4.13/1.73  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.13/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.13/1.73  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.13/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.13/1.73  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 4.13/1.73  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.13/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.13/1.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.13/1.73  tff('#skF_2', type, '#skF_2': $i).
% 4.13/1.73  tff('#skF_1', type, '#skF_1': $i).
% 4.13/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.13/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.13/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.13/1.73  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.13/1.73  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.13/1.73  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 4.13/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.13/1.73  
% 4.13/1.76  tff(f_127, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & v2_tdlat_3(A)) => v2_tdlat_3(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_tex_2)).
% 4.13/1.76  tff(f_102, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 4.13/1.76  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 4.13/1.76  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 4.13/1.76  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_borsuk_1)).
% 4.13/1.76  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.13/1.76  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 4.13/1.76  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tops_2)).
% 4.13/1.76  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> r1_tarski(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_tops_2)).
% 4.13/1.76  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (v2_tdlat_3(A) <=> (u1_pre_topc(A) = k2_tarski(k1_xboole_0, u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tdlat_3)).
% 4.13/1.76  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_pre_topc(C, A) => (v1_tops_2(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C)))) => ((D = B) => v1_tops_2(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tops_2)).
% 4.13/1.76  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.13/1.76  tff(c_42, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.13/1.76  tff(c_28, plain, (![A_39]: (m1_pre_topc(A_39, A_39) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.13/1.76  tff(c_40, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.13/1.76  tff(c_95, plain, (![A_59, B_60]: (m1_pre_topc(A_59, g1_pre_topc(u1_struct_0(B_60), u1_pre_topc(B_60))) | ~m1_pre_topc(A_59, B_60) | ~l1_pre_topc(B_60) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.13/1.76  tff(c_104, plain, (![A_59]: (m1_pre_topc(A_59, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_pre_topc(A_59, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_59))), inference(superposition, [status(thm), theory('equality')], [c_40, c_95])).
% 4.13/1.76  tff(c_129, plain, (![A_63]: (m1_pre_topc(A_63, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_pre_topc(A_63, '#skF_2') | ~l1_pre_topc(A_63))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_104])).
% 4.13/1.76  tff(c_12, plain, (![B_9, A_7]: (m1_pre_topc(B_9, A_7) | ~m1_pre_topc(B_9, g1_pre_topc(u1_struct_0(A_7), u1_pre_topc(A_7))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.13/1.76  tff(c_135, plain, (![A_63]: (m1_pre_topc(A_63, '#skF_1') | ~l1_pre_topc('#skF_1') | ~m1_pre_topc(A_63, '#skF_2') | ~l1_pre_topc(A_63))), inference(resolution, [status(thm)], [c_129, c_12])).
% 4.13/1.76  tff(c_145, plain, (![A_64]: (m1_pre_topc(A_64, '#skF_1') | ~m1_pre_topc(A_64, '#skF_2') | ~l1_pre_topc(A_64))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_135])).
% 4.13/1.76  tff(c_152, plain, (m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_145])).
% 4.13/1.76  tff(c_156, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_152])).
% 4.13/1.76  tff(c_16, plain, (![A_10, B_12]: (m1_pre_topc(A_10, g1_pre_topc(u1_struct_0(B_12), u1_pre_topc(B_12))) | ~m1_pre_topc(A_10, B_12) | ~l1_pre_topc(B_12) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.13/1.76  tff(c_84, plain, (![B_57, A_58]: (m1_pre_topc(B_57, A_58) | ~m1_pre_topc(B_57, g1_pre_topc(u1_struct_0(A_58), u1_pre_topc(A_58))) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.13/1.76  tff(c_87, plain, (![B_57]: (m1_pre_topc(B_57, '#skF_2') | ~m1_pre_topc(B_57, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_84])).
% 4.13/1.76  tff(c_109, plain, (![B_61]: (m1_pre_topc(B_61, '#skF_2') | ~m1_pre_topc(B_61, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_87])).
% 4.13/1.76  tff(c_113, plain, (![A_10]: (m1_pre_topc(A_10, '#skF_2') | ~m1_pre_topc(A_10, '#skF_1') | ~l1_pre_topc('#skF_1') | ~l1_pre_topc(A_10))), inference(resolution, [status(thm)], [c_16, c_109])).
% 4.13/1.76  tff(c_120, plain, (![A_10]: (m1_pre_topc(A_10, '#skF_2') | ~m1_pre_topc(A_10, '#skF_1') | ~l1_pre_topc(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_113])).
% 4.13/1.76  tff(c_30, plain, (![B_42, A_40]: (r1_tarski(u1_struct_0(B_42), u1_struct_0(A_40)) | ~m1_pre_topc(B_42, A_40) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.13/1.76  tff(c_80, plain, (![B_55, A_56]: (r1_tarski(u1_struct_0(B_55), u1_struct_0(A_56)) | ~m1_pre_topc(B_55, A_56) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.13/1.76  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.13/1.76  tff(c_163, plain, (![B_65, A_66]: (u1_struct_0(B_65)=u1_struct_0(A_66) | ~r1_tarski(u1_struct_0(A_66), u1_struct_0(B_65)) | ~m1_pre_topc(B_65, A_66) | ~l1_pre_topc(A_66))), inference(resolution, [status(thm)], [c_80, c_2])).
% 4.13/1.76  tff(c_174, plain, (![B_67, A_68]: (u1_struct_0(B_67)=u1_struct_0(A_68) | ~m1_pre_topc(A_68, B_67) | ~l1_pre_topc(B_67) | ~m1_pre_topc(B_67, A_68) | ~l1_pre_topc(A_68))), inference(resolution, [status(thm)], [c_30, c_163])).
% 4.13/1.76  tff(c_176, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1') | ~m1_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_156, c_174])).
% 4.13/1.76  tff(c_187, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1') | ~m1_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_176])).
% 4.13/1.76  tff(c_201, plain, (~m1_pre_topc('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_187])).
% 4.13/1.76  tff(c_204, plain, (~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_120, c_201])).
% 4.13/1.76  tff(c_207, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_204])).
% 4.13/1.76  tff(c_210, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_207])).
% 4.13/1.76  tff(c_214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_210])).
% 4.13/1.76  tff(c_216, plain, (m1_pre_topc('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_187])).
% 4.13/1.76  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.13/1.76  tff(c_215, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_187])).
% 4.13/1.76  tff(c_10, plain, (![A_6]: (m1_subset_1(u1_pre_topc(A_6), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_6)))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.13/1.76  tff(c_1630, plain, (![C_125, A_126, B_127]: (m1_subset_1(C_125, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_126)))) | ~m1_subset_1(C_125, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_127)))) | ~m1_pre_topc(B_127, A_126) | ~l1_pre_topc(A_126))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.13/1.76  tff(c_1854, plain, (![A_140, A_141]: (m1_subset_1(u1_pre_topc(A_140), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_141)))) | ~m1_pre_topc(A_140, A_141) | ~l1_pre_topc(A_141) | ~l1_pre_topc(A_140))), inference(resolution, [status(thm)], [c_10, c_1630])).
% 4.13/1.76  tff(c_1875, plain, (![A_140]: (m1_subset_1(u1_pre_topc(A_140), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_pre_topc(A_140, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_140))), inference(superposition, [status(thm), theory('equality')], [c_215, c_1854])).
% 4.13/1.76  tff(c_1888, plain, (![A_142]: (m1_subset_1(u1_pre_topc(A_142), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_pre_topc(A_142, '#skF_2') | ~l1_pre_topc(A_142))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1875])).
% 4.13/1.76  tff(c_22, plain, (![B_37, A_35]: (v1_tops_2(B_37, A_35) | ~r1_tarski(B_37, u1_pre_topc(A_35)) | ~m1_subset_1(B_37, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_35)))) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.13/1.76  tff(c_1901, plain, (![A_142]: (v1_tops_2(u1_pre_topc(A_142), '#skF_1') | ~r1_tarski(u1_pre_topc(A_142), u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1') | ~m1_pre_topc(A_142, '#skF_2') | ~l1_pre_topc(A_142))), inference(resolution, [status(thm)], [c_1888, c_22])).
% 4.13/1.76  tff(c_2047, plain, (![A_150]: (v1_tops_2(u1_pre_topc(A_150), '#skF_1') | ~r1_tarski(u1_pre_topc(A_150), u1_pre_topc('#skF_1')) | ~m1_pre_topc(A_150, '#skF_2') | ~l1_pre_topc(A_150))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1901])).
% 4.13/1.76  tff(c_2057, plain, (v1_tops_2(u1_pre_topc('#skF_1'), '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_2047])).
% 4.13/1.76  tff(c_2064, plain, (v1_tops_2(u1_pre_topc('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_216, c_2057])).
% 4.13/1.76  tff(c_2100, plain, (![C_152, A_153]: (m1_subset_1(C_152, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_153)))) | ~m1_subset_1(C_152, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_pre_topc('#skF_2', A_153) | ~l1_pre_topc(A_153))), inference(superposition, [status(thm), theory('equality')], [c_215, c_1630])).
% 4.13/1.76  tff(c_2113, plain, (![A_153]: (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_153)))) | ~m1_pre_topc('#skF_2', A_153) | ~l1_pre_topc(A_153) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_2100])).
% 4.13/1.76  tff(c_2165, plain, (![A_155]: (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_155)))) | ~m1_pre_topc('#skF_2', A_155) | ~l1_pre_topc(A_155))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2113])).
% 4.13/1.76  tff(c_2189, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_215, c_2165])).
% 4.13/1.76  tff(c_2206, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_pre_topc('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2189])).
% 4.13/1.76  tff(c_2207, plain, (~m1_pre_topc('#skF_2', '#skF_2')), inference(splitLeft, [status(thm)], [c_2206])).
% 4.13/1.76  tff(c_2210, plain, (~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_120, c_2207])).
% 4.13/1.76  tff(c_2217, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_156, c_2210])).
% 4.13/1.76  tff(c_2218, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_2206])).
% 4.13/1.76  tff(c_38, plain, (v2_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.13/1.76  tff(c_34, plain, (![A_43]: (k2_tarski(k1_xboole_0, u1_struct_0(A_43))=u1_pre_topc(A_43) | ~v2_tdlat_3(A_43) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.13/1.76  tff(c_36, plain, (~v2_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.13/1.76  tff(c_32, plain, (![A_43]: (v2_tdlat_3(A_43) | k2_tarski(k1_xboole_0, u1_struct_0(A_43))!=u1_pre_topc(A_43) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.13/1.76  tff(c_304, plain, (v2_tdlat_3('#skF_2') | k2_tarski(k1_xboole_0, u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_215, c_32])).
% 4.13/1.76  tff(c_325, plain, (v2_tdlat_3('#skF_2') | k2_tarski(k1_xboole_0, u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_304])).
% 4.13/1.76  tff(c_326, plain, (k2_tarski(k1_xboole_0, u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_36, c_325])).
% 4.13/1.76  tff(c_335, plain, (u1_pre_topc('#skF_2')!=u1_pre_topc('#skF_1') | ~v2_tdlat_3('#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_34, c_326])).
% 4.13/1.76  tff(c_337, plain, (u1_pre_topc('#skF_2')!=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_335])).
% 4.13/1.76  tff(c_310, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_215, c_10])).
% 4.13/1.76  tff(c_330, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_310])).
% 4.13/1.76  tff(c_338, plain, (![B_72, A_73]: (v1_tops_2(B_72, A_73) | ~r1_tarski(B_72, u1_pre_topc(A_73)) | ~m1_subset_1(B_72, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_73)))) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.13/1.76  tff(c_341, plain, (![B_72]: (v1_tops_2(B_72, '#skF_2') | ~r1_tarski(B_72, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_72, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_215, c_338])).
% 4.13/1.76  tff(c_583, plain, (![B_90]: (v1_tops_2(B_90, '#skF_2') | ~r1_tarski(B_90, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_90, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_341])).
% 4.13/1.76  tff(c_590, plain, (v1_tops_2(u1_pre_topc('#skF_2'), '#skF_2') | ~r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_330, c_583])).
% 4.13/1.76  tff(c_600, plain, (v1_tops_2(u1_pre_topc('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_590])).
% 4.13/1.76  tff(c_354, plain, (v1_tops_2(u1_pre_topc('#skF_2'), '#skF_1') | ~r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_330, c_22])).
% 4.13/1.76  tff(c_360, plain, (v1_tops_2(u1_pre_topc('#skF_2'), '#skF_1') | ~r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_354])).
% 4.13/1.76  tff(c_380, plain, (~r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_1'))), inference(splitLeft, [status(thm)], [c_360])).
% 4.13/1.76  tff(c_24, plain, (![B_37, A_35]: (r1_tarski(B_37, u1_pre_topc(A_35)) | ~v1_tops_2(B_37, A_35) | ~m1_subset_1(B_37, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_35)))) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.13/1.76  tff(c_357, plain, (r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_1')) | ~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_330, c_24])).
% 4.13/1.76  tff(c_363, plain, (r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_1')) | ~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_357])).
% 4.13/1.76  tff(c_381, plain, (~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_380, c_363])).
% 4.13/1.76  tff(c_526, plain, (![D_85, C_86, A_87]: (v1_tops_2(D_85, C_86) | ~m1_subset_1(D_85, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_86)))) | ~v1_tops_2(D_85, A_87) | ~m1_pre_topc(C_86, A_87) | ~m1_subset_1(D_85, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_87)))) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.13/1.76  tff(c_530, plain, (![A_87]: (v1_tops_2(u1_pre_topc('#skF_2'), '#skF_1') | ~v1_tops_2(u1_pre_topc('#skF_2'), A_87) | ~m1_pre_topc('#skF_1', A_87) | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_87)))) | ~l1_pre_topc(A_87))), inference(resolution, [status(thm)], [c_330, c_526])).
% 4.13/1.76  tff(c_1577, plain, (![A_124]: (~v1_tops_2(u1_pre_topc('#skF_2'), A_124) | ~m1_pre_topc('#skF_1', A_124) | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_124)))) | ~l1_pre_topc(A_124))), inference(negUnitSimplification, [status(thm)], [c_381, c_530])).
% 4.13/1.76  tff(c_1601, plain, (~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_2') | ~m1_pre_topc('#skF_1', '#skF_2') | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_215, c_1577])).
% 4.13/1.76  tff(c_1622, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_330, c_216, c_600, c_1601])).
% 4.13/1.76  tff(c_1624, plain, (r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_1'))), inference(splitRight, [status(thm)], [c_360])).
% 4.13/1.76  tff(c_1626, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_1') | ~r1_tarski(u1_pre_topc('#skF_1'), u1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_1624, c_2])).
% 4.13/1.76  tff(c_1629, plain, (~r1_tarski(u1_pre_topc('#skF_1'), u1_pre_topc('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_337, c_1626])).
% 4.13/1.76  tff(c_283, plain, (![B_37]: (r1_tarski(B_37, u1_pre_topc('#skF_2')) | ~v1_tops_2(B_37, '#skF_2') | ~m1_subset_1(B_37, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_215, c_24])).
% 4.13/1.76  tff(c_1832, plain, (![B_139]: (r1_tarski(B_139, u1_pre_topc('#skF_2')) | ~v1_tops_2(B_139, '#skF_2') | ~m1_subset_1(B_139, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_283])).
% 4.13/1.76  tff(c_1843, plain, (r1_tarski(u1_pre_topc('#skF_1'), u1_pre_topc('#skF_2')) | ~v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_10, c_1832])).
% 4.13/1.76  tff(c_1852, plain, (r1_tarski(u1_pre_topc('#skF_1'), u1_pre_topc('#skF_2')) | ~v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1843])).
% 4.13/1.76  tff(c_1853, plain, (~v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_1629, c_1852])).
% 4.13/1.76  tff(c_1773, plain, (![D_133, C_134, A_135]: (v1_tops_2(D_133, C_134) | ~m1_subset_1(D_133, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_134)))) | ~v1_tops_2(D_133, A_135) | ~m1_pre_topc(C_134, A_135) | ~m1_subset_1(D_133, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_135)))) | ~l1_pre_topc(A_135))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.13/1.76  tff(c_2359, plain, (![D_159, A_160]: (v1_tops_2(D_159, '#skF_2') | ~m1_subset_1(D_159, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~v1_tops_2(D_159, A_160) | ~m1_pre_topc('#skF_2', A_160) | ~m1_subset_1(D_159, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_160)))) | ~l1_pre_topc(A_160))), inference(superposition, [status(thm), theory('equality')], [c_215, c_1773])).
% 4.13/1.76  tff(c_2383, plain, (![A_160]: (v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2') | ~v1_tops_2(u1_pre_topc('#skF_1'), A_160) | ~m1_pre_topc('#skF_2', A_160) | ~m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_160)))) | ~l1_pre_topc(A_160) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_2359])).
% 4.13/1.76  tff(c_2409, plain, (![A_160]: (v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2') | ~v1_tops_2(u1_pre_topc('#skF_1'), A_160) | ~m1_pre_topc('#skF_2', A_160) | ~m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_160)))) | ~l1_pre_topc(A_160))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2383])).
% 4.13/1.76  tff(c_2735, plain, (![A_170]: (~v1_tops_2(u1_pre_topc('#skF_1'), A_170) | ~m1_pre_topc('#skF_2', A_170) | ~m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_170)))) | ~l1_pre_topc(A_170))), inference(negUnitSimplification, [status(thm)], [c_1853, c_2409])).
% 4.13/1.76  tff(c_2741, plain, (~v1_tops_2(u1_pre_topc('#skF_1'), '#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2218, c_2735])).
% 4.13/1.76  tff(c_2764, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_156, c_2064, c_2741])).
% 4.13/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.13/1.76  
% 4.13/1.76  Inference rules
% 4.13/1.76  ----------------------
% 4.13/1.76  #Ref     : 0
% 4.13/1.76  #Sup     : 486
% 4.13/1.76  #Fact    : 0
% 4.13/1.76  #Define  : 0
% 4.13/1.76  #Split   : 6
% 4.13/1.76  #Chain   : 0
% 4.13/1.76  #Close   : 0
% 4.13/1.76  
% 4.13/1.76  Ordering : KBO
% 4.13/1.76  
% 4.13/1.76  Simplification rules
% 4.13/1.76  ----------------------
% 4.13/1.76  #Subsume      : 112
% 4.13/1.76  #Demod        : 749
% 4.13/1.76  #Tautology    : 206
% 4.13/1.76  #SimpNegUnit  : 46
% 4.13/1.76  #BackRed      : 2
% 4.13/1.76  
% 4.13/1.76  #Partial instantiations: 0
% 4.13/1.76  #Strategies tried      : 1
% 4.13/1.76  
% 4.13/1.76  Timing (in seconds)
% 4.13/1.76  ----------------------
% 4.13/1.77  Preprocessing        : 0.32
% 4.13/1.77  Parsing              : 0.18
% 4.13/1.77  CNF conversion       : 0.02
% 4.13/1.77  Main loop            : 0.64
% 4.13/1.77  Inferencing          : 0.22
% 4.13/1.77  Reduction            : 0.21
% 4.13/1.77  Demodulation         : 0.14
% 4.13/1.77  BG Simplification    : 0.02
% 4.13/1.77  Subsumption          : 0.15
% 4.13/1.77  Abstraction          : 0.03
% 4.13/1.77  MUC search           : 0.00
% 4.13/1.77  Cooper               : 0.00
% 4.13/1.77  Total                : 1.03
% 4.13/1.77  Index Insertion      : 0.00
% 4.13/1.77  Index Deletion       : 0.00
% 4.13/1.77  Index Matching       : 0.00
% 4.13/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
