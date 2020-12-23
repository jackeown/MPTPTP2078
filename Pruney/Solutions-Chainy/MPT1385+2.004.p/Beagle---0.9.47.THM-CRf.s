%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:15 EST 2020

% Result     : Theorem 10.74s
% Output     : CNFRefutation 10.74s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 204 expanded)
%              Number of leaves         :   33 (  84 expanded)
%              Depth                    :   12
%              Number of atoms          :  204 ( 572 expanded)
%              Number of equality atoms :    9 (  34 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k2_enumset1 > k6_domain_1 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

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

tff(c_75,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(A_50,B_51)
      | ~ m1_subset_1(A_50,k1_zfmisc_1(B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_79,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_44,c_75])).

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

tff(c_2069,plain,(
    ! [C_306,A_307,A_308,B_309] :
      ( m2_connsp_2(C_306,A_307,k2_tarski(A_308,B_309))
      | ~ m1_subset_1(C_306,k1_zfmisc_1(u1_struct_0(A_307)))
      | ~ m1_subset_1(k2_tarski(A_308,B_309),k1_zfmisc_1(u1_struct_0(A_307)))
      | ~ l1_pre_topc(A_307)
      | ~ v2_pre_topc(A_307)
      | ~ r2_hidden(B_309,k1_tops_1(A_307,C_306))
      | ~ r2_hidden(A_308,k1_tops_1(A_307,C_306)) ) ),
    inference(resolution,[status(thm)],[c_14,c_756])).

tff(c_2079,plain,(
    ! [A_308,B_309] :
      ( m2_connsp_2('#skF_3','#skF_1',k2_tarski(A_308,B_309))
      | ~ m1_subset_1(k2_tarski(A_308,B_309),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r2_hidden(B_309,k1_tops_1('#skF_1','#skF_3'))
      | ~ r2_hidden(A_308,k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_44,c_2069])).

tff(c_2174,plain,(
    ! [A_318,B_319] :
      ( m2_connsp_2('#skF_3','#skF_1',k2_tarski(A_318,B_319))
      | ~ m1_subset_1(k2_tarski(A_318,B_319),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r2_hidden(B_319,k1_tops_1('#skF_1','#skF_3'))
      | ~ r2_hidden(A_318,k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_2079])).

tff(c_2180,plain,(
    ! [A_6] :
      ( m2_connsp_2('#skF_3','#skF_1',k2_tarski(A_6,A_6))
      | ~ m1_subset_1(k1_tarski(A_6),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r2_hidden(A_6,k1_tops_1('#skF_1','#skF_3'))
      | ~ r2_hidden(A_6,k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2174])).

tff(c_10419,plain,(
    ! [A_1189] :
      ( m2_connsp_2('#skF_3','#skF_1',k1_tarski(A_1189))
      | ~ m1_subset_1(k1_tarski(A_1189),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r2_hidden(A_1189,k1_tops_1('#skF_1','#skF_3'))
      | ~ r2_hidden(A_1189,k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2180])).

tff(c_10422,plain,
    ( m2_connsp_2('#skF_3','#skF_1',k1_tarski('#skF_2'))
    | ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_327,c_10419])).

tff(c_10428,plain,(
    ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_232,c_10422])).

tff(c_10435,plain,
    ( ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_897,c_10428])).

tff(c_10444,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_50,c_48,c_46,c_115,c_10435])).

tff(c_10446,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_10444])).

tff(c_10447,plain,(
    ~ m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_10545,plain,(
    ! [A_1215,B_1216] :
      ( k6_domain_1(A_1215,B_1216) = k1_tarski(B_1216)
      | ~ m1_subset_1(B_1216,A_1215)
      | v1_xboole_0(A_1215) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_10557,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_46,c_10545])).

tff(c_10559,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_10557])).

tff(c_10562,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_10559,c_26])).

tff(c_10565,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_10562])).

tff(c_10568,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_10565])).

tff(c_10572,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_10568])).

tff(c_10573,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2') ),
    inference(splitRight,[status(thm)],[c_10557])).

tff(c_10454,plain,(
    m2_connsp_2('#skF_3','#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_10447,c_60])).

tff(c_10575,plain,(
    m2_connsp_2('#skF_3','#skF_1',k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10573,c_10454])).

tff(c_10574,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_10557])).

tff(c_10700,plain,(
    ! [A_1237,B_1238] :
      ( m1_subset_1(k6_domain_1(A_1237,B_1238),k1_zfmisc_1(A_1237))
      | ~ m1_subset_1(B_1238,A_1237)
      | v1_xboole_0(A_1237) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10709,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10573,c_10700])).

tff(c_10713,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_10709])).

tff(c_10714,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_10574,c_10713])).

tff(c_11022,plain,(
    ! [B_1282,A_1283,C_1284] :
      ( r1_tarski(B_1282,k1_tops_1(A_1283,C_1284))
      | ~ m2_connsp_2(C_1284,A_1283,B_1282)
      | ~ m1_subset_1(C_1284,k1_zfmisc_1(u1_struct_0(A_1283)))
      | ~ m1_subset_1(B_1282,k1_zfmisc_1(u1_struct_0(A_1283)))
      | ~ l1_pre_topc(A_1283)
      | ~ v2_pre_topc(A_1283) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_11032,plain,(
    ! [B_1282] :
      ( r1_tarski(B_1282,k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',B_1282)
      | ~ m1_subset_1(B_1282,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_11022])).

tff(c_11083,plain,(
    ! [B_1291] :
      ( r1_tarski(B_1291,k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',B_1291)
      | ~ m1_subset_1(B_1291,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_11032])).

tff(c_11086,plain,
    ( r1_tarski(k1_tarski('#skF_2'),k1_tops_1('#skF_1','#skF_3'))
    | ~ m2_connsp_2('#skF_3','#skF_1',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_10714,c_11083])).

tff(c_11100,plain,(
    r1_tarski(k1_tarski('#skF_2'),k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10575,c_11086])).

tff(c_10461,plain,(
    ! [B_1194,C_1195,A_1196] :
      ( r2_hidden(B_1194,C_1195)
      | ~ r1_tarski(k2_tarski(A_1196,B_1194),C_1195) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10464,plain,(
    ! [A_6,C_1195] :
      ( r2_hidden(A_6,C_1195)
      | ~ r1_tarski(k1_tarski(A_6),C_1195) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_10461])).

tff(c_11122,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_11100,c_10464])).

tff(c_11353,plain,(
    ! [C_1306,A_1307,B_1308] :
      ( m1_connsp_2(C_1306,A_1307,B_1308)
      | ~ r2_hidden(B_1308,k1_tops_1(A_1307,C_1306))
      | ~ m1_subset_1(C_1306,k1_zfmisc_1(u1_struct_0(A_1307)))
      | ~ m1_subset_1(B_1308,u1_struct_0(A_1307))
      | ~ l1_pre_topc(A_1307)
      | ~ v2_pre_topc(A_1307)
      | v2_struct_0(A_1307) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_11357,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_11122,c_11353])).

tff(c_11364,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_11357])).

tff(c_11366,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_10447,c_11364])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:11:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.74/4.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.74/4.19  
% 10.74/4.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.74/4.19  %$ m2_connsp_2 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k2_enumset1 > k6_domain_1 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 10.74/4.19  
% 10.74/4.19  %Foreground sorts:
% 10.74/4.19  
% 10.74/4.19  
% 10.74/4.19  %Background operators:
% 10.74/4.19  
% 10.74/4.19  
% 10.74/4.19  %Foreground operators:
% 10.74/4.19  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 10.74/4.19  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 10.74/4.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.74/4.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.74/4.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.74/4.19  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.74/4.19  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 10.74/4.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.74/4.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.74/4.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.74/4.19  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 10.74/4.19  tff('#skF_2', type, '#skF_2': $i).
% 10.74/4.19  tff('#skF_3', type, '#skF_3': $i).
% 10.74/4.19  tff('#skF_1', type, '#skF_1': $i).
% 10.74/4.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.74/4.19  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 10.74/4.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.74/4.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.74/4.19  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.74/4.19  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.74/4.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.74/4.19  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 10.74/4.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.74/4.19  
% 10.74/4.21  tff(f_151, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, k6_domain_1(u1_struct_0(A), B)) <=> m1_connsp_2(C, A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_connsp_2)).
% 10.74/4.21  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.74/4.21  tff(f_94, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 10.74/4.21  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 10.74/4.21  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 10.74/4.21  tff(f_63, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 10.74/4.21  tff(f_70, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 10.74/4.21  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 10.74/4.21  tff(f_47, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 10.74/4.21  tff(f_108, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_connsp_2)).
% 10.74/4.21  tff(c_52, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_151])).
% 10.74/4.21  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 10.74/4.21  tff(c_75, plain, (![A_50, B_51]: (r1_tarski(A_50, B_51) | ~m1_subset_1(A_50, k1_zfmisc_1(B_51)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.74/4.21  tff(c_79, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_75])).
% 10.74/4.21  tff(c_50, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_151])).
% 10.74/4.21  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_151])).
% 10.74/4.21  tff(c_46, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 10.74/4.21  tff(c_54, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m2_connsp_2('#skF_3', '#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 10.74/4.21  tff(c_74, plain, (~m2_connsp_2('#skF_3', '#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_54])).
% 10.74/4.21  tff(c_60, plain, (m2_connsp_2('#skF_3', '#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')) | m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 10.74/4.21  tff(c_115, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_74, c_60])).
% 10.74/4.21  tff(c_22, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.74/4.21  tff(c_881, plain, (![B_171, A_172, C_173]: (r2_hidden(B_171, k1_tops_1(A_172, C_173)) | ~m1_connsp_2(C_173, A_172, B_171) | ~m1_subset_1(C_173, k1_zfmisc_1(u1_struct_0(A_172))) | ~m1_subset_1(B_171, u1_struct_0(A_172)) | ~l1_pre_topc(A_172) | ~v2_pre_topc(A_172) | v2_struct_0(A_172))), inference(cnfTransformation, [status(thm)], [f_94])).
% 10.74/4.21  tff(c_897, plain, (![B_171, A_172, A_12]: (r2_hidden(B_171, k1_tops_1(A_172, A_12)) | ~m1_connsp_2(A_12, A_172, B_171) | ~m1_subset_1(B_171, u1_struct_0(A_172)) | ~l1_pre_topc(A_172) | ~v2_pre_topc(A_172) | v2_struct_0(A_172) | ~r1_tarski(A_12, u1_struct_0(A_172)))), inference(resolution, [status(thm)], [c_22, c_881])).
% 10.74/4.21  tff(c_24, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.74/4.21  tff(c_177, plain, (![A_80, B_81]: (k6_domain_1(A_80, B_81)=k1_tarski(B_81) | ~m1_subset_1(B_81, A_80) | v1_xboole_0(A_80))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.74/4.21  tff(c_189, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_177])).
% 10.74/4.21  tff(c_190, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_189])).
% 10.74/4.21  tff(c_26, plain, (![A_15]: (~v1_xboole_0(u1_struct_0(A_15)) | ~l1_struct_0(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.74/4.21  tff(c_193, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_190, c_26])).
% 10.74/4.21  tff(c_196, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_52, c_193])).
% 10.74/4.21  tff(c_199, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_196])).
% 10.74/4.21  tff(c_203, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_199])).
% 10.74/4.21  tff(c_204, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2')), inference(splitRight, [status(thm)], [c_189])).
% 10.74/4.21  tff(c_232, plain, (~m2_connsp_2('#skF_3', '#skF_1', k1_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_74])).
% 10.74/4.21  tff(c_205, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_189])).
% 10.74/4.21  tff(c_313, plain, (![A_96, B_97]: (m1_subset_1(k6_domain_1(A_96, B_97), k1_zfmisc_1(A_96)) | ~m1_subset_1(B_97, A_96) | v1_xboole_0(A_96))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.74/4.21  tff(c_322, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_204, c_313])).
% 10.74/4.21  tff(c_326, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_322])).
% 10.74/4.21  tff(c_327, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_205, c_326])).
% 10.74/4.21  tff(c_10, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.74/4.21  tff(c_14, plain, (![A_9, B_10, C_11]: (r1_tarski(k2_tarski(A_9, B_10), C_11) | ~r2_hidden(B_10, C_11) | ~r2_hidden(A_9, C_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.74/4.21  tff(c_756, plain, (![C_155, A_156, B_157]: (m2_connsp_2(C_155, A_156, B_157) | ~r1_tarski(B_157, k1_tops_1(A_156, C_155)) | ~m1_subset_1(C_155, k1_zfmisc_1(u1_struct_0(A_156))) | ~m1_subset_1(B_157, k1_zfmisc_1(u1_struct_0(A_156))) | ~l1_pre_topc(A_156) | ~v2_pre_topc(A_156))), inference(cnfTransformation, [status(thm)], [f_108])).
% 10.74/4.21  tff(c_2069, plain, (![C_306, A_307, A_308, B_309]: (m2_connsp_2(C_306, A_307, k2_tarski(A_308, B_309)) | ~m1_subset_1(C_306, k1_zfmisc_1(u1_struct_0(A_307))) | ~m1_subset_1(k2_tarski(A_308, B_309), k1_zfmisc_1(u1_struct_0(A_307))) | ~l1_pre_topc(A_307) | ~v2_pre_topc(A_307) | ~r2_hidden(B_309, k1_tops_1(A_307, C_306)) | ~r2_hidden(A_308, k1_tops_1(A_307, C_306)))), inference(resolution, [status(thm)], [c_14, c_756])).
% 10.74/4.21  tff(c_2079, plain, (![A_308, B_309]: (m2_connsp_2('#skF_3', '#skF_1', k2_tarski(A_308, B_309)) | ~m1_subset_1(k2_tarski(A_308, B_309), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r2_hidden(B_309, k1_tops_1('#skF_1', '#skF_3')) | ~r2_hidden(A_308, k1_tops_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_44, c_2069])).
% 10.74/4.21  tff(c_2174, plain, (![A_318, B_319]: (m2_connsp_2('#skF_3', '#skF_1', k2_tarski(A_318, B_319)) | ~m1_subset_1(k2_tarski(A_318, B_319), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r2_hidden(B_319, k1_tops_1('#skF_1', '#skF_3')) | ~r2_hidden(A_318, k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_2079])).
% 10.74/4.21  tff(c_2180, plain, (![A_6]: (m2_connsp_2('#skF_3', '#skF_1', k2_tarski(A_6, A_6)) | ~m1_subset_1(k1_tarski(A_6), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r2_hidden(A_6, k1_tops_1('#skF_1', '#skF_3')) | ~r2_hidden(A_6, k1_tops_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_10, c_2174])).
% 10.74/4.21  tff(c_10419, plain, (![A_1189]: (m2_connsp_2('#skF_3', '#skF_1', k1_tarski(A_1189)) | ~m1_subset_1(k1_tarski(A_1189), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r2_hidden(A_1189, k1_tops_1('#skF_1', '#skF_3')) | ~r2_hidden(A_1189, k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_2180])).
% 10.74/4.21  tff(c_10422, plain, (m2_connsp_2('#skF_3', '#skF_1', k1_tarski('#skF_2')) | ~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_327, c_10419])).
% 10.74/4.21  tff(c_10428, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_232, c_10422])).
% 10.74/4.21  tff(c_10435, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_897, c_10428])).
% 10.74/4.21  tff(c_10444, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_50, c_48, c_46, c_115, c_10435])).
% 10.74/4.21  tff(c_10446, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_10444])).
% 10.74/4.21  tff(c_10447, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_54])).
% 10.74/4.21  tff(c_10545, plain, (![A_1215, B_1216]: (k6_domain_1(A_1215, B_1216)=k1_tarski(B_1216) | ~m1_subset_1(B_1216, A_1215) | v1_xboole_0(A_1215))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.74/4.21  tff(c_10557, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_10545])).
% 10.74/4.21  tff(c_10559, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_10557])).
% 10.74/4.21  tff(c_10562, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_10559, c_26])).
% 10.74/4.21  tff(c_10565, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_52, c_10562])).
% 10.74/4.21  tff(c_10568, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_10565])).
% 10.74/4.21  tff(c_10572, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_10568])).
% 10.74/4.21  tff(c_10573, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2')), inference(splitRight, [status(thm)], [c_10557])).
% 10.74/4.21  tff(c_10454, plain, (m2_connsp_2('#skF_3', '#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_10447, c_60])).
% 10.74/4.21  tff(c_10575, plain, (m2_connsp_2('#skF_3', '#skF_1', k1_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10573, c_10454])).
% 10.74/4.21  tff(c_10574, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_10557])).
% 10.74/4.21  tff(c_10700, plain, (![A_1237, B_1238]: (m1_subset_1(k6_domain_1(A_1237, B_1238), k1_zfmisc_1(A_1237)) | ~m1_subset_1(B_1238, A_1237) | v1_xboole_0(A_1237))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.74/4.21  tff(c_10709, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_10573, c_10700])).
% 10.74/4.21  tff(c_10713, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_10709])).
% 10.74/4.21  tff(c_10714, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_10574, c_10713])).
% 10.74/4.21  tff(c_11022, plain, (![B_1282, A_1283, C_1284]: (r1_tarski(B_1282, k1_tops_1(A_1283, C_1284)) | ~m2_connsp_2(C_1284, A_1283, B_1282) | ~m1_subset_1(C_1284, k1_zfmisc_1(u1_struct_0(A_1283))) | ~m1_subset_1(B_1282, k1_zfmisc_1(u1_struct_0(A_1283))) | ~l1_pre_topc(A_1283) | ~v2_pre_topc(A_1283))), inference(cnfTransformation, [status(thm)], [f_108])).
% 10.74/4.21  tff(c_11032, plain, (![B_1282]: (r1_tarski(B_1282, k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', B_1282) | ~m1_subset_1(B_1282, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_11022])).
% 10.74/4.21  tff(c_11083, plain, (![B_1291]: (r1_tarski(B_1291, k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', B_1291) | ~m1_subset_1(B_1291, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_11032])).
% 10.74/4.21  tff(c_11086, plain, (r1_tarski(k1_tarski('#skF_2'), k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_10714, c_11083])).
% 10.74/4.21  tff(c_11100, plain, (r1_tarski(k1_tarski('#skF_2'), k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_10575, c_11086])).
% 10.74/4.21  tff(c_10461, plain, (![B_1194, C_1195, A_1196]: (r2_hidden(B_1194, C_1195) | ~r1_tarski(k2_tarski(A_1196, B_1194), C_1195))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.74/4.21  tff(c_10464, plain, (![A_6, C_1195]: (r2_hidden(A_6, C_1195) | ~r1_tarski(k1_tarski(A_6), C_1195))), inference(superposition, [status(thm), theory('equality')], [c_10, c_10461])).
% 10.74/4.21  tff(c_11122, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_11100, c_10464])).
% 10.74/4.21  tff(c_11353, plain, (![C_1306, A_1307, B_1308]: (m1_connsp_2(C_1306, A_1307, B_1308) | ~r2_hidden(B_1308, k1_tops_1(A_1307, C_1306)) | ~m1_subset_1(C_1306, k1_zfmisc_1(u1_struct_0(A_1307))) | ~m1_subset_1(B_1308, u1_struct_0(A_1307)) | ~l1_pre_topc(A_1307) | ~v2_pre_topc(A_1307) | v2_struct_0(A_1307))), inference(cnfTransformation, [status(thm)], [f_94])).
% 10.74/4.21  tff(c_11357, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_11122, c_11353])).
% 10.74/4.21  tff(c_11364, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_11357])).
% 10.74/4.21  tff(c_11366, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_10447, c_11364])).
% 10.74/4.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.74/4.21  
% 10.74/4.21  Inference rules
% 10.74/4.21  ----------------------
% 10.74/4.21  #Ref     : 0
% 10.74/4.21  #Sup     : 3106
% 10.74/4.21  #Fact    : 0
% 10.74/4.21  #Define  : 0
% 10.74/4.21  #Split   : 26
% 10.74/4.21  #Chain   : 0
% 10.74/4.21  #Close   : 0
% 10.74/4.21  
% 10.74/4.21  Ordering : KBO
% 10.74/4.21  
% 10.74/4.21  Simplification rules
% 10.74/4.21  ----------------------
% 10.74/4.21  #Subsume      : 1220
% 10.74/4.21  #Demod        : 621
% 10.74/4.21  #Tautology    : 182
% 10.74/4.21  #SimpNegUnit  : 60
% 10.74/4.21  #BackRed      : 2
% 10.74/4.21  
% 10.74/4.21  #Partial instantiations: 0
% 10.74/4.21  #Strategies tried      : 1
% 10.74/4.21  
% 10.74/4.21  Timing (in seconds)
% 10.74/4.21  ----------------------
% 10.74/4.21  Preprocessing        : 0.33
% 10.74/4.21  Parsing              : 0.17
% 10.74/4.21  CNF conversion       : 0.02
% 10.74/4.21  Main loop            : 3.10
% 10.74/4.21  Inferencing          : 0.70
% 10.74/4.21  Reduction            : 0.83
% 10.74/4.21  Demodulation         : 0.56
% 10.74/4.21  BG Simplification    : 0.06
% 10.74/4.21  Subsumption          : 1.31
% 10.74/4.21  Abstraction          : 0.09
% 10.74/4.21  MUC search           : 0.00
% 10.74/4.21  Cooper               : 0.00
% 10.74/4.21  Total                : 3.46
% 10.74/4.21  Index Insertion      : 0.00
% 10.74/4.21  Index Deletion       : 0.00
% 10.74/4.21  Index Matching       : 0.00
% 10.74/4.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
