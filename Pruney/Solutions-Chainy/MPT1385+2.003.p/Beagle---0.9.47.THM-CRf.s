%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:15 EST 2020

% Result     : Theorem 11.01s
% Output     : CNFRefutation 11.26s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 201 expanded)
%              Number of leaves         :   33 (  83 expanded)
%              Depth                    :   12
%              Number of atoms          :  204 ( 562 expanded)
%              Number of equality atoms :    9 (  34 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k1_enumset1 > k6_domain_1 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_151,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_connsp_2)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_94,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_108,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m2_connsp_2(C,A,B)
              <=> r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_76,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(A_52,B_53)
      | ~ m1_subset_1(A_52,k1_zfmisc_1(B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_84,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_44,c_76])).

tff(c_50,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_46,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_54,plain,
    ( ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m2_connsp_2('#skF_3','#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_74,plain,(
    ~ m2_connsp_2('#skF_3','#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_60,plain,
    ( m2_connsp_2('#skF_3','#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'))
    | m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_115,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_60])).

tff(c_22,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_881,plain,(
    ! [B_171,A_172,C_173] :
      ( r2_hidden(B_171,k1_tops_1(A_172,C_173))
      | ~ m1_connsp_2(C_173,A_172,B_171)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ m1_subset_1(B_171,u1_struct_0(A_172))
      | ~ l1_pre_topc(A_172)
      | ~ v2_pre_topc(A_172)
      | v2_struct_0(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_897,plain,(
    ! [B_171,A_172,A_12] :
      ( r2_hidden(B_171,k1_tops_1(A_172,A_12))
      | ~ m1_connsp_2(A_12,A_172,B_171)
      | ~ m1_subset_1(B_171,u1_struct_0(A_172))
      | ~ l1_pre_topc(A_172)
      | ~ v2_pre_topc(A_172)
      | v2_struct_0(A_172)
      | ~ r1_tarski(A_12,u1_struct_0(A_172)) ) ),
    inference(resolution,[status(thm)],[c_22,c_881])).

tff(c_24,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_177,plain,(
    ! [A_80,B_81] :
      ( k6_domain_1(A_80,B_81) = k1_tarski(B_81)
      | ~ m1_subset_1(B_81,A_80)
      | v1_xboole_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_189,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_46,c_177])).

tff(c_190,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_189])).

tff(c_26,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0(u1_struct_0(A_15))
      | ~ l1_struct_0(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_193,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_190,c_26])).

tff(c_196,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_193])).

tff(c_199,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_196])).

tff(c_203,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_199])).

tff(c_204,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2') ),
    inference(splitRight,[status(thm)],[c_189])).

tff(c_232,plain,(
    ~ m2_connsp_2('#skF_3','#skF_1',k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_74])).

tff(c_205,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_189])).

tff(c_313,plain,(
    ! [A_96,B_97] :
      ( m1_subset_1(k6_domain_1(A_96,B_97),k1_zfmisc_1(A_96))
      | ~ m1_subset_1(B_97,A_96)
      | v1_xboole_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_322,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_313])).

tff(c_326,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_322])).

tff(c_327,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_205,c_326])).

tff(c_10,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] :
      ( r1_tarski(k2_tarski(A_9,B_10),C_11)
      | ~ r2_hidden(B_10,C_11)
      | ~ r2_hidden(A_9,C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_756,plain,(
    ! [C_155,A_156,B_157] :
      ( m2_connsp_2(C_155,A_156,B_157)
      | ~ r1_tarski(B_157,k1_tops_1(A_156,C_155))
      | ~ m1_subset_1(C_155,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ m1_subset_1(B_157,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ l1_pre_topc(A_156)
      | ~ v2_pre_topc(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1967,plain,(
    ! [C_296,A_297,A_298,B_299] :
      ( m2_connsp_2(C_296,A_297,k2_tarski(A_298,B_299))
      | ~ m1_subset_1(C_296,k1_zfmisc_1(u1_struct_0(A_297)))
      | ~ m1_subset_1(k2_tarski(A_298,B_299),k1_zfmisc_1(u1_struct_0(A_297)))
      | ~ l1_pre_topc(A_297)
      | ~ v2_pre_topc(A_297)
      | ~ r2_hidden(B_299,k1_tops_1(A_297,C_296))
      | ~ r2_hidden(A_298,k1_tops_1(A_297,C_296)) ) ),
    inference(resolution,[status(thm)],[c_14,c_756])).

tff(c_1977,plain,(
    ! [A_298,B_299] :
      ( m2_connsp_2('#skF_3','#skF_1',k2_tarski(A_298,B_299))
      | ~ m1_subset_1(k2_tarski(A_298,B_299),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r2_hidden(B_299,k1_tops_1('#skF_1','#skF_3'))
      | ~ r2_hidden(A_298,k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_44,c_1967])).

tff(c_1986,plain,(
    ! [A_300,B_301] :
      ( m2_connsp_2('#skF_3','#skF_1',k2_tarski(A_300,B_301))
      | ~ m1_subset_1(k2_tarski(A_300,B_301),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r2_hidden(B_301,k1_tops_1('#skF_1','#skF_3'))
      | ~ r2_hidden(A_300,k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_1977])).

tff(c_1992,plain,(
    ! [A_6] :
      ( m2_connsp_2('#skF_3','#skF_1',k2_tarski(A_6,A_6))
      | ~ m1_subset_1(k1_tarski(A_6),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r2_hidden(A_6,k1_tops_1('#skF_1','#skF_3'))
      | ~ r2_hidden(A_6,k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1986])).

tff(c_10230,plain,(
    ! [A_1175] :
      ( m2_connsp_2('#skF_3','#skF_1',k1_tarski(A_1175))
      | ~ m1_subset_1(k1_tarski(A_1175),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r2_hidden(A_1175,k1_tops_1('#skF_1','#skF_3'))
      | ~ r2_hidden(A_1175,k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1992])).

tff(c_10233,plain,
    ( m2_connsp_2('#skF_3','#skF_1',k1_tarski('#skF_2'))
    | ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_327,c_10230])).

tff(c_10239,plain,(
    ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_232,c_10233])).

tff(c_10246,plain,
    ( ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_897,c_10239])).

tff(c_10255,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_50,c_48,c_46,c_115,c_10246])).

tff(c_10257,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_10255])).

tff(c_10258,plain,(
    ~ m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_10356,plain,(
    ! [A_1200,B_1201] :
      ( k6_domain_1(A_1200,B_1201) = k1_tarski(B_1201)
      | ~ m1_subset_1(B_1201,A_1200)
      | v1_xboole_0(A_1200) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_10368,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_46,c_10356])).

tff(c_10370,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_10368])).

tff(c_10373,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_10370,c_26])).

tff(c_10376,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_10373])).

tff(c_10379,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_10376])).

tff(c_10383,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_10379])).

tff(c_10384,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2') ),
    inference(splitRight,[status(thm)],[c_10368])).

tff(c_10259,plain,(
    m2_connsp_2('#skF_3','#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_10386,plain,(
    m2_connsp_2('#skF_3','#skF_1',k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10384,c_10259])).

tff(c_10385,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_10368])).

tff(c_10397,plain,(
    ! [A_1207,B_1208] :
      ( m1_subset_1(k6_domain_1(A_1207,B_1208),k1_zfmisc_1(A_1207))
      | ~ m1_subset_1(B_1208,A_1207)
      | v1_xboole_0(A_1207) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10406,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10384,c_10397])).

tff(c_10410,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_10406])).

tff(c_10411,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_10385,c_10410])).

tff(c_10979,plain,(
    ! [B_1290,A_1291,C_1292] :
      ( r1_tarski(B_1290,k1_tops_1(A_1291,C_1292))
      | ~ m2_connsp_2(C_1292,A_1291,B_1290)
      | ~ m1_subset_1(C_1292,k1_zfmisc_1(u1_struct_0(A_1291)))
      | ~ m1_subset_1(B_1290,k1_zfmisc_1(u1_struct_0(A_1291)))
      | ~ l1_pre_topc(A_1291)
      | ~ v2_pre_topc(A_1291) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_10989,plain,(
    ! [B_1290] :
      ( r1_tarski(B_1290,k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',B_1290)
      | ~ m1_subset_1(B_1290,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_10979])).

tff(c_11003,plain,(
    ! [B_1295] :
      ( r1_tarski(B_1295,k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',B_1295)
      | ~ m1_subset_1(B_1295,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_10989])).

tff(c_11006,plain,
    ( r1_tarski(k1_tarski('#skF_2'),k1_tops_1('#skF_1','#skF_3'))
    | ~ m2_connsp_2('#skF_3','#skF_1',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_10411,c_11003])).

tff(c_11020,plain,(
    r1_tarski(k1_tarski('#skF_2'),k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10386,c_11006])).

tff(c_10291,plain,(
    ! [A_1183,C_1184,B_1185] :
      ( r2_hidden(A_1183,C_1184)
      | ~ r1_tarski(k2_tarski(A_1183,B_1185),C_1184) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10294,plain,(
    ! [A_6,C_1184] :
      ( r2_hidden(A_6,C_1184)
      | ~ r1_tarski(k1_tarski(A_6),C_1184) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_10291])).

tff(c_11047,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_11020,c_10294])).

tff(c_11099,plain,(
    ! [C_1297,A_1298,B_1299] :
      ( m1_connsp_2(C_1297,A_1298,B_1299)
      | ~ r2_hidden(B_1299,k1_tops_1(A_1298,C_1297))
      | ~ m1_subset_1(C_1297,k1_zfmisc_1(u1_struct_0(A_1298)))
      | ~ m1_subset_1(B_1299,u1_struct_0(A_1298))
      | ~ l1_pre_topc(A_1298)
      | ~ v2_pre_topc(A_1298)
      | v2_struct_0(A_1298) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_11101,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_11047,c_11099])).

tff(c_11104,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_11101])).

tff(c_11106,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_10258,c_11104])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:45:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.01/4.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.26/4.43  
% 11.26/4.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.26/4.44  %$ m2_connsp_2 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k1_enumset1 > k6_domain_1 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 11.26/4.44  
% 11.26/4.44  %Foreground sorts:
% 11.26/4.44  
% 11.26/4.44  
% 11.26/4.44  %Background operators:
% 11.26/4.44  
% 11.26/4.44  
% 11.26/4.44  %Foreground operators:
% 11.26/4.44  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 11.26/4.44  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 11.26/4.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.26/4.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.26/4.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.26/4.44  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.26/4.44  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 11.26/4.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.26/4.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.26/4.44  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 11.26/4.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.26/4.44  tff('#skF_2', type, '#skF_2': $i).
% 11.26/4.44  tff('#skF_3', type, '#skF_3': $i).
% 11.26/4.44  tff('#skF_1', type, '#skF_1': $i).
% 11.26/4.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.26/4.44  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 11.26/4.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.26/4.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.26/4.44  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.26/4.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.26/4.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.26/4.44  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 11.26/4.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.26/4.44  
% 11.26/4.45  tff(f_151, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, k6_domain_1(u1_struct_0(A), B)) <=> m1_connsp_2(C, A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_connsp_2)).
% 11.26/4.45  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 11.26/4.45  tff(f_94, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 11.26/4.45  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 11.26/4.45  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 11.26/4.45  tff(f_63, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 11.26/4.45  tff(f_70, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 11.26/4.45  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 11.26/4.45  tff(f_47, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 11.26/4.45  tff(f_108, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_connsp_2)).
% 11.26/4.45  tff(c_52, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_151])).
% 11.26/4.45  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 11.26/4.45  tff(c_76, plain, (![A_52, B_53]: (r1_tarski(A_52, B_53) | ~m1_subset_1(A_52, k1_zfmisc_1(B_53)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.26/4.45  tff(c_84, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_76])).
% 11.26/4.45  tff(c_50, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_151])).
% 11.26/4.45  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_151])).
% 11.26/4.45  tff(c_46, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 11.26/4.45  tff(c_54, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m2_connsp_2('#skF_3', '#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 11.26/4.45  tff(c_74, plain, (~m2_connsp_2('#skF_3', '#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_54])).
% 11.26/4.45  tff(c_60, plain, (m2_connsp_2('#skF_3', '#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')) | m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 11.26/4.45  tff(c_115, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_74, c_60])).
% 11.26/4.45  tff(c_22, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.26/4.45  tff(c_881, plain, (![B_171, A_172, C_173]: (r2_hidden(B_171, k1_tops_1(A_172, C_173)) | ~m1_connsp_2(C_173, A_172, B_171) | ~m1_subset_1(C_173, k1_zfmisc_1(u1_struct_0(A_172))) | ~m1_subset_1(B_171, u1_struct_0(A_172)) | ~l1_pre_topc(A_172) | ~v2_pre_topc(A_172) | v2_struct_0(A_172))), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.26/4.45  tff(c_897, plain, (![B_171, A_172, A_12]: (r2_hidden(B_171, k1_tops_1(A_172, A_12)) | ~m1_connsp_2(A_12, A_172, B_171) | ~m1_subset_1(B_171, u1_struct_0(A_172)) | ~l1_pre_topc(A_172) | ~v2_pre_topc(A_172) | v2_struct_0(A_172) | ~r1_tarski(A_12, u1_struct_0(A_172)))), inference(resolution, [status(thm)], [c_22, c_881])).
% 11.26/4.45  tff(c_24, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.26/4.45  tff(c_177, plain, (![A_80, B_81]: (k6_domain_1(A_80, B_81)=k1_tarski(B_81) | ~m1_subset_1(B_81, A_80) | v1_xboole_0(A_80))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.26/4.45  tff(c_189, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_177])).
% 11.26/4.45  tff(c_190, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_189])).
% 11.26/4.45  tff(c_26, plain, (![A_15]: (~v1_xboole_0(u1_struct_0(A_15)) | ~l1_struct_0(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.26/4.45  tff(c_193, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_190, c_26])).
% 11.26/4.45  tff(c_196, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_52, c_193])).
% 11.26/4.45  tff(c_199, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_196])).
% 11.26/4.45  tff(c_203, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_199])).
% 11.26/4.45  tff(c_204, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2')), inference(splitRight, [status(thm)], [c_189])).
% 11.26/4.45  tff(c_232, plain, (~m2_connsp_2('#skF_3', '#skF_1', k1_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_74])).
% 11.26/4.45  tff(c_205, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_189])).
% 11.26/4.45  tff(c_313, plain, (![A_96, B_97]: (m1_subset_1(k6_domain_1(A_96, B_97), k1_zfmisc_1(A_96)) | ~m1_subset_1(B_97, A_96) | v1_xboole_0(A_96))), inference(cnfTransformation, [status(thm)], [f_70])).
% 11.26/4.45  tff(c_322, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_204, c_313])).
% 11.26/4.45  tff(c_326, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_322])).
% 11.26/4.45  tff(c_327, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_205, c_326])).
% 11.26/4.45  tff(c_10, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.26/4.45  tff(c_14, plain, (![A_9, B_10, C_11]: (r1_tarski(k2_tarski(A_9, B_10), C_11) | ~r2_hidden(B_10, C_11) | ~r2_hidden(A_9, C_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.26/4.45  tff(c_756, plain, (![C_155, A_156, B_157]: (m2_connsp_2(C_155, A_156, B_157) | ~r1_tarski(B_157, k1_tops_1(A_156, C_155)) | ~m1_subset_1(C_155, k1_zfmisc_1(u1_struct_0(A_156))) | ~m1_subset_1(B_157, k1_zfmisc_1(u1_struct_0(A_156))) | ~l1_pre_topc(A_156) | ~v2_pre_topc(A_156))), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.26/4.45  tff(c_1967, plain, (![C_296, A_297, A_298, B_299]: (m2_connsp_2(C_296, A_297, k2_tarski(A_298, B_299)) | ~m1_subset_1(C_296, k1_zfmisc_1(u1_struct_0(A_297))) | ~m1_subset_1(k2_tarski(A_298, B_299), k1_zfmisc_1(u1_struct_0(A_297))) | ~l1_pre_topc(A_297) | ~v2_pre_topc(A_297) | ~r2_hidden(B_299, k1_tops_1(A_297, C_296)) | ~r2_hidden(A_298, k1_tops_1(A_297, C_296)))), inference(resolution, [status(thm)], [c_14, c_756])).
% 11.26/4.45  tff(c_1977, plain, (![A_298, B_299]: (m2_connsp_2('#skF_3', '#skF_1', k2_tarski(A_298, B_299)) | ~m1_subset_1(k2_tarski(A_298, B_299), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r2_hidden(B_299, k1_tops_1('#skF_1', '#skF_3')) | ~r2_hidden(A_298, k1_tops_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_44, c_1967])).
% 11.26/4.45  tff(c_1986, plain, (![A_300, B_301]: (m2_connsp_2('#skF_3', '#skF_1', k2_tarski(A_300, B_301)) | ~m1_subset_1(k2_tarski(A_300, B_301), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r2_hidden(B_301, k1_tops_1('#skF_1', '#skF_3')) | ~r2_hidden(A_300, k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_1977])).
% 11.26/4.45  tff(c_1992, plain, (![A_6]: (m2_connsp_2('#skF_3', '#skF_1', k2_tarski(A_6, A_6)) | ~m1_subset_1(k1_tarski(A_6), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r2_hidden(A_6, k1_tops_1('#skF_1', '#skF_3')) | ~r2_hidden(A_6, k1_tops_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1986])).
% 11.26/4.45  tff(c_10230, plain, (![A_1175]: (m2_connsp_2('#skF_3', '#skF_1', k1_tarski(A_1175)) | ~m1_subset_1(k1_tarski(A_1175), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r2_hidden(A_1175, k1_tops_1('#skF_1', '#skF_3')) | ~r2_hidden(A_1175, k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1992])).
% 11.26/4.45  tff(c_10233, plain, (m2_connsp_2('#skF_3', '#skF_1', k1_tarski('#skF_2')) | ~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_327, c_10230])).
% 11.26/4.45  tff(c_10239, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_232, c_10233])).
% 11.26/4.45  tff(c_10246, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_897, c_10239])).
% 11.26/4.45  tff(c_10255, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_50, c_48, c_46, c_115, c_10246])).
% 11.26/4.45  tff(c_10257, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_10255])).
% 11.26/4.45  tff(c_10258, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_54])).
% 11.26/4.45  tff(c_10356, plain, (![A_1200, B_1201]: (k6_domain_1(A_1200, B_1201)=k1_tarski(B_1201) | ~m1_subset_1(B_1201, A_1200) | v1_xboole_0(A_1200))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.26/4.45  tff(c_10368, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_10356])).
% 11.26/4.45  tff(c_10370, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_10368])).
% 11.26/4.45  tff(c_10373, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_10370, c_26])).
% 11.26/4.45  tff(c_10376, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_52, c_10373])).
% 11.26/4.45  tff(c_10379, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_10376])).
% 11.26/4.45  tff(c_10383, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_10379])).
% 11.26/4.45  tff(c_10384, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2')), inference(splitRight, [status(thm)], [c_10368])).
% 11.26/4.45  tff(c_10259, plain, (m2_connsp_2('#skF_3', '#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_54])).
% 11.26/4.45  tff(c_10386, plain, (m2_connsp_2('#skF_3', '#skF_1', k1_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10384, c_10259])).
% 11.26/4.45  tff(c_10385, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_10368])).
% 11.26/4.45  tff(c_10397, plain, (![A_1207, B_1208]: (m1_subset_1(k6_domain_1(A_1207, B_1208), k1_zfmisc_1(A_1207)) | ~m1_subset_1(B_1208, A_1207) | v1_xboole_0(A_1207))), inference(cnfTransformation, [status(thm)], [f_70])).
% 11.26/4.45  tff(c_10406, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_10384, c_10397])).
% 11.26/4.45  tff(c_10410, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_10406])).
% 11.26/4.45  tff(c_10411, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_10385, c_10410])).
% 11.26/4.45  tff(c_10979, plain, (![B_1290, A_1291, C_1292]: (r1_tarski(B_1290, k1_tops_1(A_1291, C_1292)) | ~m2_connsp_2(C_1292, A_1291, B_1290) | ~m1_subset_1(C_1292, k1_zfmisc_1(u1_struct_0(A_1291))) | ~m1_subset_1(B_1290, k1_zfmisc_1(u1_struct_0(A_1291))) | ~l1_pre_topc(A_1291) | ~v2_pre_topc(A_1291))), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.26/4.45  tff(c_10989, plain, (![B_1290]: (r1_tarski(B_1290, k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', B_1290) | ~m1_subset_1(B_1290, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_10979])).
% 11.26/4.45  tff(c_11003, plain, (![B_1295]: (r1_tarski(B_1295, k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', B_1295) | ~m1_subset_1(B_1295, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_10989])).
% 11.26/4.45  tff(c_11006, plain, (r1_tarski(k1_tarski('#skF_2'), k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_10411, c_11003])).
% 11.26/4.45  tff(c_11020, plain, (r1_tarski(k1_tarski('#skF_2'), k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_10386, c_11006])).
% 11.26/4.45  tff(c_10291, plain, (![A_1183, C_1184, B_1185]: (r2_hidden(A_1183, C_1184) | ~r1_tarski(k2_tarski(A_1183, B_1185), C_1184))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.26/4.45  tff(c_10294, plain, (![A_6, C_1184]: (r2_hidden(A_6, C_1184) | ~r1_tarski(k1_tarski(A_6), C_1184))), inference(superposition, [status(thm), theory('equality')], [c_10, c_10291])).
% 11.26/4.45  tff(c_11047, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_11020, c_10294])).
% 11.26/4.45  tff(c_11099, plain, (![C_1297, A_1298, B_1299]: (m1_connsp_2(C_1297, A_1298, B_1299) | ~r2_hidden(B_1299, k1_tops_1(A_1298, C_1297)) | ~m1_subset_1(C_1297, k1_zfmisc_1(u1_struct_0(A_1298))) | ~m1_subset_1(B_1299, u1_struct_0(A_1298)) | ~l1_pre_topc(A_1298) | ~v2_pre_topc(A_1298) | v2_struct_0(A_1298))), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.26/4.45  tff(c_11101, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_11047, c_11099])).
% 11.26/4.45  tff(c_11104, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_11101])).
% 11.26/4.45  tff(c_11106, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_10258, c_11104])).
% 11.26/4.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.26/4.45  
% 11.26/4.45  Inference rules
% 11.26/4.45  ----------------------
% 11.26/4.45  #Ref     : 0
% 11.26/4.45  #Sup     : 3026
% 11.26/4.45  #Fact    : 0
% 11.26/4.45  #Define  : 0
% 11.26/4.45  #Split   : 25
% 11.26/4.45  #Chain   : 0
% 11.26/4.45  #Close   : 0
% 11.26/4.45  
% 11.26/4.45  Ordering : KBO
% 11.26/4.45  
% 11.26/4.45  Simplification rules
% 11.26/4.45  ----------------------
% 11.26/4.45  #Subsume      : 1181
% 11.26/4.45  #Demod        : 598
% 11.26/4.45  #Tautology    : 178
% 11.26/4.45  #SimpNegUnit  : 61
% 11.26/4.45  #BackRed      : 2
% 11.26/4.45  
% 11.26/4.45  #Partial instantiations: 0
% 11.26/4.45  #Strategies tried      : 1
% 11.26/4.45  
% 11.26/4.45  Timing (in seconds)
% 11.26/4.45  ----------------------
% 11.26/4.46  Preprocessing        : 0.35
% 11.26/4.46  Parsing              : 0.19
% 11.26/4.46  CNF conversion       : 0.03
% 11.26/4.46  Main loop            : 3.33
% 11.26/4.46  Inferencing          : 0.78
% 11.26/4.46  Reduction            : 0.85
% 11.26/4.46  Demodulation         : 0.56
% 11.26/4.46  BG Simplification    : 0.07
% 11.26/4.46  Subsumption          : 1.42
% 11.26/4.46  Abstraction          : 0.10
% 11.26/4.46  MUC search           : 0.00
% 11.26/4.46  Cooper               : 0.00
% 11.26/4.46  Total                : 3.72
% 11.26/4.46  Index Insertion      : 0.00
% 11.26/4.46  Index Deletion       : 0.00
% 11.26/4.46  Index Matching       : 0.00
% 11.26/4.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
