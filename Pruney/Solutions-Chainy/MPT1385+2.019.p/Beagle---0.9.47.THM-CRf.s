%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:17 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 289 expanded)
%              Number of leaves         :   38 ( 115 expanded)
%              Depth                    :   12
%              Number of atoms          :  211 ( 799 expanded)
%              Number of equality atoms :    9 (  44 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_148,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( m2_connsp_2(C,A,k6_domain_1(u1_struct_0(A),B))
                <=> m1_connsp_2(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_connsp_2)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_91,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> r2_hidden(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_105,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m2_connsp_2(C,A,B)
              <=> r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_85,plain,(
    ! [A_73,B_74] :
      ( r1_tarski(A_73,B_74)
      | ~ m1_subset_1(A_73,k1_zfmisc_1(B_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_93,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_46,c_85])).

tff(c_52,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_48,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_56,plain,
    ( ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m2_connsp_2('#skF_3','#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_75,plain,(
    ~ m2_connsp_2('#skF_3','#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_62,plain,
    ( m2_connsp_2('#skF_3','#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'))
    | m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_113,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_62])).

tff(c_26,plain,(
    ! [A_34,B_35] :
      ( m1_subset_1(A_34,k1_zfmisc_1(B_35))
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_352,plain,(
    ! [B_154,A_155,C_156] :
      ( r2_hidden(B_154,k1_tops_1(A_155,C_156))
      | ~ m1_connsp_2(C_156,A_155,B_154)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(u1_struct_0(A_155)))
      | ~ m1_subset_1(B_154,u1_struct_0(A_155))
      | ~ l1_pre_topc(A_155)
      | ~ v2_pre_topc(A_155)
      | v2_struct_0(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_358,plain,(
    ! [B_154,A_155,A_34] :
      ( r2_hidden(B_154,k1_tops_1(A_155,A_34))
      | ~ m1_connsp_2(A_34,A_155,B_154)
      | ~ m1_subset_1(B_154,u1_struct_0(A_155))
      | ~ l1_pre_topc(A_155)
      | ~ v2_pre_topc(A_155)
      | v2_struct_0(A_155)
      | ~ r1_tarski(A_34,u1_struct_0(A_155)) ) ),
    inference(resolution,[status(thm)],[c_26,c_352])).

tff(c_28,plain,(
    ! [A_36] :
      ( l1_struct_0(A_36)
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_114,plain,(
    ! [A_88,B_89] :
      ( k6_domain_1(A_88,B_89) = k1_tarski(B_89)
      | ~ m1_subset_1(B_89,A_88)
      | v1_xboole_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_126,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_48,c_114])).

tff(c_127,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_30,plain,(
    ! [A_37] :
      ( ~ v1_xboole_0(u1_struct_0(A_37))
      | ~ l1_struct_0(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_130,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_127,c_30])).

tff(c_133,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_130])).

tff(c_136,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_133])).

tff(c_140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_136])).

tff(c_142,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_22,plain,(
    ! [A_32,B_33] :
      ( r2_hidden(A_32,B_33)
      | v1_xboole_0(B_33)
      | ~ m1_subset_1(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_143,plain,(
    ! [A_90,B_91,C_92] :
      ( r1_tarski(k2_tarski(A_90,B_91),C_92)
      | ~ r2_hidden(B_91,C_92)
      | ~ r2_hidden(A_90,C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_152,plain,(
    ! [A_1,C_92] :
      ( r1_tarski(k1_tarski(A_1),C_92)
      | ~ r2_hidden(A_1,C_92)
      | ~ r2_hidden(A_1,C_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_143])).

tff(c_219,plain,(
    ! [C_125,A_126,B_127] :
      ( m2_connsp_2(C_125,A_126,B_127)
      | ~ r1_tarski(B_127,k1_tops_1(A_126,C_125))
      | ~ m1_subset_1(C_125,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_pre_topc(A_126)
      | ~ v2_pre_topc(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_384,plain,(
    ! [C_163,A_164,A_165] :
      ( m2_connsp_2(C_163,A_164,k1_tarski(A_165))
      | ~ m1_subset_1(C_163,k1_zfmisc_1(u1_struct_0(A_164)))
      | ~ m1_subset_1(k1_tarski(A_165),k1_zfmisc_1(u1_struct_0(A_164)))
      | ~ l1_pre_topc(A_164)
      | ~ v2_pre_topc(A_164)
      | ~ r2_hidden(A_165,k1_tops_1(A_164,C_163)) ) ),
    inference(resolution,[status(thm)],[c_152,c_219])).

tff(c_389,plain,(
    ! [A_165] :
      ( m2_connsp_2('#skF_3','#skF_1',k1_tarski(A_165))
      | ~ m1_subset_1(k1_tarski(A_165),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r2_hidden(A_165,k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_46,c_384])).

tff(c_394,plain,(
    ! [A_166] :
      ( m2_connsp_2('#skF_3','#skF_1',k1_tarski(A_166))
      | ~ m1_subset_1(k1_tarski(A_166),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r2_hidden(A_166,k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_389])).

tff(c_399,plain,(
    ! [A_167] :
      ( m2_connsp_2('#skF_3','#skF_1',k1_tarski(A_167))
      | ~ r2_hidden(A_167,k1_tops_1('#skF_1','#skF_3'))
      | ~ r1_tarski(k1_tarski(A_167),u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_26,c_394])).

tff(c_405,plain,(
    ! [A_168] :
      ( m2_connsp_2('#skF_3','#skF_1',k1_tarski(A_168))
      | ~ r2_hidden(A_168,k1_tops_1('#skF_1','#skF_3'))
      | ~ r2_hidden(A_168,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_152,c_399])).

tff(c_141,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2') ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_155,plain,(
    ~ m2_connsp_2('#skF_3','#skF_1',k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_75])).

tff(c_418,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r2_hidden('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_405,c_155])).

tff(c_419,plain,(
    ~ r2_hidden('#skF_2',u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_418])).

tff(c_422,plain,
    ( v1_xboole_0(u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_22,c_419])).

tff(c_425,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_422])).

tff(c_427,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_425])).

tff(c_428,plain,(
    ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_418])).

tff(c_443,plain,
    ( ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_358,c_428])).

tff(c_452,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_52,c_50,c_48,c_113,c_443])).

tff(c_454,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_452])).

tff(c_455,plain,(
    ~ m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_496,plain,(
    ! [A_189,B_190] :
      ( k6_domain_1(A_189,B_190) = k1_tarski(B_190)
      | ~ m1_subset_1(B_190,A_189)
      | v1_xboole_0(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_508,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_48,c_496])).

tff(c_509,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_508])).

tff(c_512,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_509,c_30])).

tff(c_515,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_512])).

tff(c_518,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_515])).

tff(c_522,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_518])).

tff(c_524,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_508])).

tff(c_523,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2') ),
    inference(splitRight,[status(thm)],[c_508])).

tff(c_457,plain,(
    m2_connsp_2('#skF_3','#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_455,c_62])).

tff(c_534,plain,(
    m2_connsp_2('#skF_3','#skF_1',k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_457])).

tff(c_539,plain,(
    ! [A_195,B_196,C_197] :
      ( r1_tarski(k2_tarski(A_195,B_196),C_197)
      | ~ r2_hidden(B_196,C_197)
      | ~ r2_hidden(A_195,C_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_548,plain,(
    ! [A_1,C_197] :
      ( r1_tarski(k1_tarski(A_1),C_197)
      | ~ r2_hidden(A_1,C_197)
      | ~ r2_hidden(A_1,C_197) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_539])).

tff(c_609,plain,(
    ! [B_229,A_230,C_231] :
      ( r1_tarski(B_229,k1_tops_1(A_230,C_231))
      | ~ m2_connsp_2(C_231,A_230,B_229)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(u1_struct_0(A_230)))
      | ~ m1_subset_1(B_229,k1_zfmisc_1(u1_struct_0(A_230)))
      | ~ l1_pre_topc(A_230)
      | ~ v2_pre_topc(A_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_614,plain,(
    ! [B_229] :
      ( r1_tarski(B_229,k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',B_229)
      | ~ m1_subset_1(B_229,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_46,c_609])).

tff(c_619,plain,(
    ! [B_232] :
      ( r1_tarski(B_232,k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',B_232)
      | ~ m1_subset_1(B_232,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_614])).

tff(c_630,plain,(
    ! [A_233] :
      ( r1_tarski(A_233,k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',A_233)
      | ~ r1_tarski(A_233,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_26,c_619])).

tff(c_477,plain,(
    ! [A_176,C_177,B_178] :
      ( r2_hidden(A_176,C_177)
      | ~ r1_tarski(k2_tarski(A_176,B_178),C_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_480,plain,(
    ! [A_1,C_177] :
      ( r2_hidden(A_1,C_177)
      | ~ r1_tarski(k1_tarski(A_1),C_177) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_477])).

tff(c_651,plain,(
    ! [A_234] :
      ( r2_hidden(A_234,k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',k1_tarski(A_234))
      | ~ r1_tarski(k1_tarski(A_234),u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_630,c_480])).

tff(c_669,plain,(
    ! [A_239] :
      ( r2_hidden(A_239,k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',k1_tarski(A_239))
      | ~ r2_hidden(A_239,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_548,c_651])).

tff(c_673,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r2_hidden('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_534,c_669])).

tff(c_674,plain,(
    ~ r2_hidden('#skF_2',u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_673])).

tff(c_677,plain,
    ( v1_xboole_0(u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_22,c_674])).

tff(c_680,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_677])).

tff(c_682,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_524,c_680])).

tff(c_683,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_673])).

tff(c_709,plain,(
    ! [C_246,A_247,B_248] :
      ( m1_connsp_2(C_246,A_247,B_248)
      | ~ r2_hidden(B_248,k1_tops_1(A_247,C_246))
      | ~ m1_subset_1(C_246,k1_zfmisc_1(u1_struct_0(A_247)))
      | ~ m1_subset_1(B_248,u1_struct_0(A_247))
      | ~ l1_pre_topc(A_247)
      | ~ v2_pre_topc(A_247)
      | v2_struct_0(A_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_711,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_683,c_709])).

tff(c_719,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_711])).

tff(c_721,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_455,c_719])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:47:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.05/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.54  
% 3.05/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.54  %$ m2_connsp_2 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 3.05/1.54  
% 3.05/1.54  %Foreground sorts:
% 3.05/1.54  
% 3.05/1.54  
% 3.05/1.54  %Background operators:
% 3.05/1.54  
% 3.05/1.54  
% 3.05/1.54  %Foreground operators:
% 3.05/1.54  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.05/1.54  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.05/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.05/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.05/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.05/1.54  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.05/1.54  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.05/1.54  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.05/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.05/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.05/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.05/1.54  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.05/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.05/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.05/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.05/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.05/1.54  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.05/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.05/1.54  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.05/1.54  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.05/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.05/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.05/1.54  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.05/1.54  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.05/1.54  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.05/1.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.05/1.54  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 3.05/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.05/1.54  
% 3.34/1.56  tff(f_148, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, k6_domain_1(u1_struct_0(A), B)) <=> m1_connsp_2(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_connsp_2)).
% 3.34/1.56  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.34/1.56  tff(f_91, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 3.34/1.56  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.34/1.56  tff(f_74, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.34/1.56  tff(f_67, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.34/1.56  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.34/1.56  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.34/1.56  tff(f_45, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.34/1.56  tff(f_105, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_connsp_2)).
% 3.34/1.56  tff(c_54, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.34/1.56  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.34/1.56  tff(c_85, plain, (![A_73, B_74]: (r1_tarski(A_73, B_74) | ~m1_subset_1(A_73, k1_zfmisc_1(B_74)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.34/1.56  tff(c_93, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_85])).
% 3.34/1.56  tff(c_52, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.34/1.56  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.34/1.56  tff(c_48, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.34/1.56  tff(c_56, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m2_connsp_2('#skF_3', '#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.34/1.56  tff(c_75, plain, (~m2_connsp_2('#skF_3', '#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_56])).
% 3.34/1.56  tff(c_62, plain, (m2_connsp_2('#skF_3', '#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')) | m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.34/1.56  tff(c_113, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_75, c_62])).
% 3.34/1.56  tff(c_26, plain, (![A_34, B_35]: (m1_subset_1(A_34, k1_zfmisc_1(B_35)) | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.34/1.56  tff(c_352, plain, (![B_154, A_155, C_156]: (r2_hidden(B_154, k1_tops_1(A_155, C_156)) | ~m1_connsp_2(C_156, A_155, B_154) | ~m1_subset_1(C_156, k1_zfmisc_1(u1_struct_0(A_155))) | ~m1_subset_1(B_154, u1_struct_0(A_155)) | ~l1_pre_topc(A_155) | ~v2_pre_topc(A_155) | v2_struct_0(A_155))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.34/1.56  tff(c_358, plain, (![B_154, A_155, A_34]: (r2_hidden(B_154, k1_tops_1(A_155, A_34)) | ~m1_connsp_2(A_34, A_155, B_154) | ~m1_subset_1(B_154, u1_struct_0(A_155)) | ~l1_pre_topc(A_155) | ~v2_pre_topc(A_155) | v2_struct_0(A_155) | ~r1_tarski(A_34, u1_struct_0(A_155)))), inference(resolution, [status(thm)], [c_26, c_352])).
% 3.34/1.56  tff(c_28, plain, (![A_36]: (l1_struct_0(A_36) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.34/1.56  tff(c_114, plain, (![A_88, B_89]: (k6_domain_1(A_88, B_89)=k1_tarski(B_89) | ~m1_subset_1(B_89, A_88) | v1_xboole_0(A_88))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.34/1.56  tff(c_126, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_114])).
% 3.34/1.56  tff(c_127, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_126])).
% 3.34/1.56  tff(c_30, plain, (![A_37]: (~v1_xboole_0(u1_struct_0(A_37)) | ~l1_struct_0(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.34/1.56  tff(c_130, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_127, c_30])).
% 3.34/1.56  tff(c_133, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_54, c_130])).
% 3.34/1.56  tff(c_136, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_133])).
% 3.34/1.56  tff(c_140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_136])).
% 3.34/1.56  tff(c_142, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_126])).
% 3.34/1.56  tff(c_22, plain, (![A_32, B_33]: (r2_hidden(A_32, B_33) | v1_xboole_0(B_33) | ~m1_subset_1(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.34/1.56  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.34/1.56  tff(c_143, plain, (![A_90, B_91, C_92]: (r1_tarski(k2_tarski(A_90, B_91), C_92) | ~r2_hidden(B_91, C_92) | ~r2_hidden(A_90, C_92))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.34/1.56  tff(c_152, plain, (![A_1, C_92]: (r1_tarski(k1_tarski(A_1), C_92) | ~r2_hidden(A_1, C_92) | ~r2_hidden(A_1, C_92))), inference(superposition, [status(thm), theory('equality')], [c_2, c_143])).
% 3.34/1.56  tff(c_219, plain, (![C_125, A_126, B_127]: (m2_connsp_2(C_125, A_126, B_127) | ~r1_tarski(B_127, k1_tops_1(A_126, C_125)) | ~m1_subset_1(C_125, k1_zfmisc_1(u1_struct_0(A_126))) | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_pre_topc(A_126) | ~v2_pre_topc(A_126))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.34/1.56  tff(c_384, plain, (![C_163, A_164, A_165]: (m2_connsp_2(C_163, A_164, k1_tarski(A_165)) | ~m1_subset_1(C_163, k1_zfmisc_1(u1_struct_0(A_164))) | ~m1_subset_1(k1_tarski(A_165), k1_zfmisc_1(u1_struct_0(A_164))) | ~l1_pre_topc(A_164) | ~v2_pre_topc(A_164) | ~r2_hidden(A_165, k1_tops_1(A_164, C_163)))), inference(resolution, [status(thm)], [c_152, c_219])).
% 3.34/1.56  tff(c_389, plain, (![A_165]: (m2_connsp_2('#skF_3', '#skF_1', k1_tarski(A_165)) | ~m1_subset_1(k1_tarski(A_165), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r2_hidden(A_165, k1_tops_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_46, c_384])).
% 3.34/1.56  tff(c_394, plain, (![A_166]: (m2_connsp_2('#skF_3', '#skF_1', k1_tarski(A_166)) | ~m1_subset_1(k1_tarski(A_166), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r2_hidden(A_166, k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_389])).
% 3.34/1.56  tff(c_399, plain, (![A_167]: (m2_connsp_2('#skF_3', '#skF_1', k1_tarski(A_167)) | ~r2_hidden(A_167, k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tarski(A_167), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_26, c_394])).
% 3.34/1.56  tff(c_405, plain, (![A_168]: (m2_connsp_2('#skF_3', '#skF_1', k1_tarski(A_168)) | ~r2_hidden(A_168, k1_tops_1('#skF_1', '#skF_3')) | ~r2_hidden(A_168, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_152, c_399])).
% 3.34/1.56  tff(c_141, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2')), inference(splitRight, [status(thm)], [c_126])).
% 3.34/1.56  tff(c_155, plain, (~m2_connsp_2('#skF_3', '#skF_1', k1_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_75])).
% 3.34/1.56  tff(c_418, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r2_hidden('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_405, c_155])).
% 3.34/1.56  tff(c_419, plain, (~r2_hidden('#skF_2', u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_418])).
% 3.34/1.56  tff(c_422, plain, (v1_xboole_0(u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_419])).
% 3.34/1.56  tff(c_425, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_422])).
% 3.34/1.56  tff(c_427, plain, $false, inference(negUnitSimplification, [status(thm)], [c_142, c_425])).
% 3.34/1.56  tff(c_428, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_418])).
% 3.34/1.56  tff(c_443, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_358, c_428])).
% 3.34/1.56  tff(c_452, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_52, c_50, c_48, c_113, c_443])).
% 3.34/1.56  tff(c_454, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_452])).
% 3.34/1.56  tff(c_455, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_56])).
% 3.34/1.56  tff(c_496, plain, (![A_189, B_190]: (k6_domain_1(A_189, B_190)=k1_tarski(B_190) | ~m1_subset_1(B_190, A_189) | v1_xboole_0(A_189))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.34/1.56  tff(c_508, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_496])).
% 3.34/1.56  tff(c_509, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_508])).
% 3.34/1.56  tff(c_512, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_509, c_30])).
% 3.34/1.56  tff(c_515, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_54, c_512])).
% 3.34/1.56  tff(c_518, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_515])).
% 3.34/1.56  tff(c_522, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_518])).
% 3.34/1.56  tff(c_524, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_508])).
% 3.34/1.56  tff(c_523, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2')), inference(splitRight, [status(thm)], [c_508])).
% 3.34/1.56  tff(c_457, plain, (m2_connsp_2('#skF_3', '#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_455, c_62])).
% 3.34/1.56  tff(c_534, plain, (m2_connsp_2('#skF_3', '#skF_1', k1_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_523, c_457])).
% 3.34/1.56  tff(c_539, plain, (![A_195, B_196, C_197]: (r1_tarski(k2_tarski(A_195, B_196), C_197) | ~r2_hidden(B_196, C_197) | ~r2_hidden(A_195, C_197))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.34/1.56  tff(c_548, plain, (![A_1, C_197]: (r1_tarski(k1_tarski(A_1), C_197) | ~r2_hidden(A_1, C_197) | ~r2_hidden(A_1, C_197))), inference(superposition, [status(thm), theory('equality')], [c_2, c_539])).
% 3.34/1.56  tff(c_609, plain, (![B_229, A_230, C_231]: (r1_tarski(B_229, k1_tops_1(A_230, C_231)) | ~m2_connsp_2(C_231, A_230, B_229) | ~m1_subset_1(C_231, k1_zfmisc_1(u1_struct_0(A_230))) | ~m1_subset_1(B_229, k1_zfmisc_1(u1_struct_0(A_230))) | ~l1_pre_topc(A_230) | ~v2_pre_topc(A_230))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.34/1.56  tff(c_614, plain, (![B_229]: (r1_tarski(B_229, k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', B_229) | ~m1_subset_1(B_229, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_609])).
% 3.34/1.56  tff(c_619, plain, (![B_232]: (r1_tarski(B_232, k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', B_232) | ~m1_subset_1(B_232, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_614])).
% 3.34/1.56  tff(c_630, plain, (![A_233]: (r1_tarski(A_233, k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', A_233) | ~r1_tarski(A_233, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_26, c_619])).
% 3.34/1.56  tff(c_477, plain, (![A_176, C_177, B_178]: (r2_hidden(A_176, C_177) | ~r1_tarski(k2_tarski(A_176, B_178), C_177))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.34/1.56  tff(c_480, plain, (![A_1, C_177]: (r2_hidden(A_1, C_177) | ~r1_tarski(k1_tarski(A_1), C_177))), inference(superposition, [status(thm), theory('equality')], [c_2, c_477])).
% 3.34/1.56  tff(c_651, plain, (![A_234]: (r2_hidden(A_234, k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', k1_tarski(A_234)) | ~r1_tarski(k1_tarski(A_234), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_630, c_480])).
% 3.34/1.56  tff(c_669, plain, (![A_239]: (r2_hidden(A_239, k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', k1_tarski(A_239)) | ~r2_hidden(A_239, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_548, c_651])).
% 3.34/1.56  tff(c_673, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r2_hidden('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_534, c_669])).
% 3.34/1.56  tff(c_674, plain, (~r2_hidden('#skF_2', u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_673])).
% 3.34/1.56  tff(c_677, plain, (v1_xboole_0(u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_674])).
% 3.34/1.56  tff(c_680, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_677])).
% 3.34/1.56  tff(c_682, plain, $false, inference(negUnitSimplification, [status(thm)], [c_524, c_680])).
% 3.34/1.56  tff(c_683, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_673])).
% 3.34/1.56  tff(c_709, plain, (![C_246, A_247, B_248]: (m1_connsp_2(C_246, A_247, B_248) | ~r2_hidden(B_248, k1_tops_1(A_247, C_246)) | ~m1_subset_1(C_246, k1_zfmisc_1(u1_struct_0(A_247))) | ~m1_subset_1(B_248, u1_struct_0(A_247)) | ~l1_pre_topc(A_247) | ~v2_pre_topc(A_247) | v2_struct_0(A_247))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.34/1.56  tff(c_711, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_683, c_709])).
% 3.34/1.56  tff(c_719, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_711])).
% 3.34/1.56  tff(c_721, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_455, c_719])).
% 3.34/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.56  
% 3.34/1.56  Inference rules
% 3.34/1.56  ----------------------
% 3.34/1.56  #Ref     : 0
% 3.34/1.56  #Sup     : 131
% 3.34/1.56  #Fact    : 0
% 3.34/1.56  #Define  : 0
% 3.34/1.56  #Split   : 9
% 3.34/1.56  #Chain   : 0
% 3.34/1.56  #Close   : 0
% 3.34/1.56  
% 3.34/1.56  Ordering : KBO
% 3.34/1.56  
% 3.34/1.56  Simplification rules
% 3.34/1.56  ----------------------
% 3.34/1.56  #Subsume      : 12
% 3.34/1.56  #Demod        : 62
% 3.34/1.56  #Tautology    : 55
% 3.34/1.56  #SimpNegUnit  : 13
% 3.34/1.56  #BackRed      : 2
% 3.34/1.56  
% 3.34/1.56  #Partial instantiations: 0
% 3.34/1.56  #Strategies tried      : 1
% 3.34/1.56  
% 3.34/1.56  Timing (in seconds)
% 3.34/1.56  ----------------------
% 3.34/1.56  Preprocessing        : 0.36
% 3.34/1.56  Parsing              : 0.20
% 3.34/1.56  CNF conversion       : 0.02
% 3.34/1.56  Main loop            : 0.36
% 3.34/1.56  Inferencing          : 0.15
% 3.34/1.56  Reduction            : 0.10
% 3.34/1.57  Demodulation         : 0.06
% 3.34/1.57  BG Simplification    : 0.02
% 3.34/1.57  Subsumption          : 0.06
% 3.34/1.57  Abstraction          : 0.02
% 3.34/1.57  MUC search           : 0.00
% 3.34/1.57  Cooper               : 0.00
% 3.34/1.57  Total                : 0.76
% 3.34/1.57  Index Insertion      : 0.00
% 3.34/1.57  Index Deletion       : 0.00
% 3.34/1.57  Index Matching       : 0.00
% 3.34/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
