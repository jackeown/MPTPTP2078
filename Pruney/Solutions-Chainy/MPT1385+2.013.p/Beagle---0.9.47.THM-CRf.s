%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:17 EST 2020

% Result     : Theorem 11.08s
% Output     : CNFRefutation 11.21s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 202 expanded)
%              Number of leaves         :   34 (  84 expanded)
%              Depth                    :   12
%              Number of atoms          :  204 ( 562 expanded)
%              Number of equality atoms :    9 (  34 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k1_enumset1 > k6_domain_1 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_149,negated_conjecture,(
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

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_92,axiom,(
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

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_106,axiom,(
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

tff(c_50,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_81,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(A_50,B_51)
      | ~ m1_subset_1(A_50,k1_zfmisc_1(B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_88,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_42,c_81])).

tff(c_48,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_44,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_58,plain,
    ( m2_connsp_2('#skF_3','#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'))
    | m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_80,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_960,plain,(
    ! [B_188,A_189,C_190] :
      ( r2_hidden(B_188,k1_tops_1(A_189,C_190))
      | ~ m1_connsp_2(C_190,A_189,B_188)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ m1_subset_1(B_188,u1_struct_0(A_189))
      | ~ l1_pre_topc(A_189)
      | ~ v2_pre_topc(A_189)
      | v2_struct_0(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_979,plain,(
    ! [B_188,A_189,A_12] :
      ( r2_hidden(B_188,k1_tops_1(A_189,A_12))
      | ~ m1_connsp_2(A_12,A_189,B_188)
      | ~ m1_subset_1(B_188,u1_struct_0(A_189))
      | ~ l1_pre_topc(A_189)
      | ~ v2_pre_topc(A_189)
      | v2_struct_0(A_189)
      | ~ r1_tarski(A_12,u1_struct_0(A_189)) ) ),
    inference(resolution,[status(thm)],[c_20,c_960])).

tff(c_22,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_150,plain,(
    ! [A_74,B_75] :
      ( k6_domain_1(A_74,B_75) = k1_tarski(B_75)
      | ~ m1_subset_1(B_75,A_74)
      | v1_xboole_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_165,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_44,c_150])).

tff(c_187,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_165])).

tff(c_24,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0(u1_struct_0(A_15))
      | ~ l1_struct_0(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_191,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_187,c_24])).

tff(c_194,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_191])).

tff(c_197,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_194])).

tff(c_201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_197])).

tff(c_202,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2') ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_52,plain,
    ( ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m2_connsp_2('#skF_3','#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_120,plain,(
    ~ m2_connsp_2('#skF_3','#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_52])).

tff(c_204,plain,(
    ~ m2_connsp_2('#skF_3','#skF_1',k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_120])).

tff(c_203,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_209,plain,(
    ! [A_78,B_79] :
      ( m1_subset_1(k6_domain_1(A_78,B_79),k1_zfmisc_1(A_78))
      | ~ m1_subset_1(B_79,A_78)
      | v1_xboole_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_218,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_209])).

tff(c_222,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_218])).

tff(c_223,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_203,c_222])).

tff(c_4,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] :
      ( r1_tarski(k2_tarski(A_7,B_8),C_9)
      | ~ r2_hidden(B_8,C_9)
      | ~ r2_hidden(A_7,C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_591,plain,(
    ! [C_140,A_141,B_142] :
      ( m2_connsp_2(C_140,A_141,B_142)
      | ~ r1_tarski(B_142,k1_tops_1(A_141,C_140))
      | ~ m1_subset_1(C_140,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1918,plain,(
    ! [C_300,A_301,A_302,B_303] :
      ( m2_connsp_2(C_300,A_301,k2_tarski(A_302,B_303))
      | ~ m1_subset_1(C_300,k1_zfmisc_1(u1_struct_0(A_301)))
      | ~ m1_subset_1(k2_tarski(A_302,B_303),k1_zfmisc_1(u1_struct_0(A_301)))
      | ~ l1_pre_topc(A_301)
      | ~ v2_pre_topc(A_301)
      | ~ r2_hidden(B_303,k1_tops_1(A_301,C_300))
      | ~ r2_hidden(A_302,k1_tops_1(A_301,C_300)) ) ),
    inference(resolution,[status(thm)],[c_8,c_591])).

tff(c_1928,plain,(
    ! [A_302,B_303] :
      ( m2_connsp_2('#skF_3','#skF_1',k2_tarski(A_302,B_303))
      | ~ m1_subset_1(k2_tarski(A_302,B_303),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r2_hidden(B_303,k1_tops_1('#skF_1','#skF_3'))
      | ~ r2_hidden(A_302,k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_42,c_1918])).

tff(c_2116,plain,(
    ! [A_309,B_310] :
      ( m2_connsp_2('#skF_3','#skF_1',k2_tarski(A_309,B_310))
      | ~ m1_subset_1(k2_tarski(A_309,B_310),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r2_hidden(B_310,k1_tops_1('#skF_1','#skF_3'))
      | ~ r2_hidden(A_309,k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1928])).

tff(c_2122,plain,(
    ! [A_4] :
      ( m2_connsp_2('#skF_3','#skF_1',k2_tarski(A_4,A_4))
      | ~ m1_subset_1(k1_tarski(A_4),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r2_hidden(A_4,k1_tops_1('#skF_1','#skF_3'))
      | ~ r2_hidden(A_4,k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2116])).

tff(c_11098,plain,(
    ! [A_1241] :
      ( m2_connsp_2('#skF_3','#skF_1',k1_tarski(A_1241))
      | ~ m1_subset_1(k1_tarski(A_1241),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r2_hidden(A_1241,k1_tops_1('#skF_1','#skF_3'))
      | ~ r2_hidden(A_1241,k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2122])).

tff(c_11104,plain,
    ( m2_connsp_2('#skF_3','#skF_1',k1_tarski('#skF_2'))
    | ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_223,c_11098])).

tff(c_11110,plain,(
    ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_204,c_11104])).

tff(c_11117,plain,
    ( ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_979,c_11110])).

tff(c_11126,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_48,c_46,c_44,c_80,c_11117])).

tff(c_11128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_11126])).

tff(c_11130,plain,(
    ~ m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_11219,plain,(
    ! [A_1267,B_1268] :
      ( k6_domain_1(A_1267,B_1268) = k1_tarski(B_1268)
      | ~ m1_subset_1(B_1268,A_1267)
      | v1_xboole_0(A_1267) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_11234,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_44,c_11219])).

tff(c_11246,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_11234])).

tff(c_11250,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_11246,c_24])).

tff(c_11253,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_11250])).

tff(c_11256,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_11253])).

tff(c_11260,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_11256])).

tff(c_11261,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2') ),
    inference(splitRight,[status(thm)],[c_11234])).

tff(c_11129,plain,(
    m2_connsp_2('#skF_3','#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_11263,plain,(
    m2_connsp_2('#skF_3','#skF_1',k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11261,c_11129])).

tff(c_11262,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_11234])).

tff(c_11349,plain,(
    ! [A_1287,B_1288] :
      ( m1_subset_1(k6_domain_1(A_1287,B_1288),k1_zfmisc_1(A_1287))
      | ~ m1_subset_1(B_1288,A_1287)
      | v1_xboole_0(A_1287) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_11358,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11261,c_11349])).

tff(c_11365,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_11358])).

tff(c_11366,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_11262,c_11365])).

tff(c_11689,plain,(
    ! [B_1335,A_1336,C_1337] :
      ( r1_tarski(B_1335,k1_tops_1(A_1336,C_1337))
      | ~ m2_connsp_2(C_1337,A_1336,B_1335)
      | ~ m1_subset_1(C_1337,k1_zfmisc_1(u1_struct_0(A_1336)))
      | ~ m1_subset_1(B_1335,k1_zfmisc_1(u1_struct_0(A_1336)))
      | ~ l1_pre_topc(A_1336)
      | ~ v2_pre_topc(A_1336) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_11699,plain,(
    ! [B_1335] :
      ( r1_tarski(B_1335,k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',B_1335)
      | ~ m1_subset_1(B_1335,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_11689])).

tff(c_11747,plain,(
    ! [B_1341] :
      ( r1_tarski(B_1341,k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',B_1341)
      | ~ m1_subset_1(B_1341,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_11699])).

tff(c_11750,plain,
    ( r1_tarski(k1_tarski('#skF_2'),k1_tops_1('#skF_1','#skF_3'))
    | ~ m2_connsp_2('#skF_3','#skF_1',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_11366,c_11747])).

tff(c_11768,plain,(
    r1_tarski(k1_tarski('#skF_2'),k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11263,c_11750])).

tff(c_11158,plain,(
    ! [A_1250,C_1251,B_1252] :
      ( r2_hidden(A_1250,C_1251)
      | ~ r1_tarski(k2_tarski(A_1250,B_1252),C_1251) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_11165,plain,(
    ! [A_4,C_1251] :
      ( r2_hidden(A_4,C_1251)
      | ~ r1_tarski(k1_tarski(A_4),C_1251) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_11158])).

tff(c_11789,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_11768,c_11165])).

tff(c_11925,plain,(
    ! [C_1357,A_1358,B_1359] :
      ( m1_connsp_2(C_1357,A_1358,B_1359)
      | ~ r2_hidden(B_1359,k1_tops_1(A_1358,C_1357))
      | ~ m1_subset_1(C_1357,k1_zfmisc_1(u1_struct_0(A_1358)))
      | ~ m1_subset_1(B_1359,u1_struct_0(A_1358))
      | ~ l1_pre_topc(A_1358)
      | ~ v2_pre_topc(A_1358)
      | v2_struct_0(A_1358) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_11929,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_11789,c_11925])).

tff(c_11936,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_11929])).

tff(c_11938,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_11130,c_11936])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:08:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.08/5.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.08/5.07  
% 11.08/5.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.08/5.07  %$ m2_connsp_2 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k1_enumset1 > k6_domain_1 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 11.08/5.07  
% 11.08/5.07  %Foreground sorts:
% 11.08/5.07  
% 11.08/5.07  
% 11.08/5.07  %Background operators:
% 11.08/5.07  
% 11.08/5.07  
% 11.08/5.07  %Foreground operators:
% 11.08/5.07  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 11.08/5.07  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 11.08/5.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.08/5.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.08/5.07  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.08/5.07  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.08/5.07  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 11.08/5.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.08/5.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.08/5.07  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 11.08/5.07  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.08/5.07  tff('#skF_2', type, '#skF_2': $i).
% 11.08/5.07  tff('#skF_3', type, '#skF_3': $i).
% 11.08/5.07  tff('#skF_1', type, '#skF_1': $i).
% 11.08/5.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.08/5.07  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 11.08/5.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.08/5.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.08/5.07  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.08/5.07  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.08/5.07  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 11.08/5.07  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.08/5.07  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 11.08/5.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.08/5.07  
% 11.21/5.11  tff(f_149, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, k6_domain_1(u1_struct_0(A), B)) <=> m1_connsp_2(C, A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_connsp_2)).
% 11.21/5.11  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 11.21/5.11  tff(f_92, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 11.21/5.11  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 11.21/5.11  tff(f_75, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 11.21/5.11  tff(f_61, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 11.21/5.11  tff(f_68, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 11.21/5.11  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 11.21/5.11  tff(f_41, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 11.21/5.11  tff(f_106, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_connsp_2)).
% 11.21/5.11  tff(c_50, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 11.21/5.11  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 11.21/5.11  tff(c_81, plain, (![A_50, B_51]: (r1_tarski(A_50, B_51) | ~m1_subset_1(A_50, k1_zfmisc_1(B_51)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.21/5.11  tff(c_88, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_81])).
% 11.21/5.11  tff(c_48, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 11.21/5.11  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 11.21/5.11  tff(c_44, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 11.21/5.11  tff(c_58, plain, (m2_connsp_2('#skF_3', '#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')) | m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 11.21/5.11  tff(c_80, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_58])).
% 11.21/5.11  tff(c_20, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.21/5.11  tff(c_960, plain, (![B_188, A_189, C_190]: (r2_hidden(B_188, k1_tops_1(A_189, C_190)) | ~m1_connsp_2(C_190, A_189, B_188) | ~m1_subset_1(C_190, k1_zfmisc_1(u1_struct_0(A_189))) | ~m1_subset_1(B_188, u1_struct_0(A_189)) | ~l1_pre_topc(A_189) | ~v2_pre_topc(A_189) | v2_struct_0(A_189))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.21/5.11  tff(c_979, plain, (![B_188, A_189, A_12]: (r2_hidden(B_188, k1_tops_1(A_189, A_12)) | ~m1_connsp_2(A_12, A_189, B_188) | ~m1_subset_1(B_188, u1_struct_0(A_189)) | ~l1_pre_topc(A_189) | ~v2_pre_topc(A_189) | v2_struct_0(A_189) | ~r1_tarski(A_12, u1_struct_0(A_189)))), inference(resolution, [status(thm)], [c_20, c_960])).
% 11.21/5.11  tff(c_22, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.21/5.11  tff(c_150, plain, (![A_74, B_75]: (k6_domain_1(A_74, B_75)=k1_tarski(B_75) | ~m1_subset_1(B_75, A_74) | v1_xboole_0(A_74))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.21/5.11  tff(c_165, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_150])).
% 11.21/5.11  tff(c_187, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_165])).
% 11.21/5.11  tff(c_24, plain, (![A_15]: (~v1_xboole_0(u1_struct_0(A_15)) | ~l1_struct_0(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.21/5.11  tff(c_191, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_187, c_24])).
% 11.21/5.11  tff(c_194, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_191])).
% 11.21/5.11  tff(c_197, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_194])).
% 11.21/5.11  tff(c_201, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_197])).
% 11.21/5.11  tff(c_202, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2')), inference(splitRight, [status(thm)], [c_165])).
% 11.21/5.11  tff(c_52, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m2_connsp_2('#skF_3', '#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 11.21/5.11  tff(c_120, plain, (~m2_connsp_2('#skF_3', '#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_52])).
% 11.21/5.11  tff(c_204, plain, (~m2_connsp_2('#skF_3', '#skF_1', k1_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_202, c_120])).
% 11.21/5.11  tff(c_203, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_165])).
% 11.21/5.11  tff(c_209, plain, (![A_78, B_79]: (m1_subset_1(k6_domain_1(A_78, B_79), k1_zfmisc_1(A_78)) | ~m1_subset_1(B_79, A_78) | v1_xboole_0(A_78))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.21/5.11  tff(c_218, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_202, c_209])).
% 11.21/5.11  tff(c_222, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_218])).
% 11.21/5.11  tff(c_223, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_203, c_222])).
% 11.21/5.11  tff(c_4, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.21/5.11  tff(c_8, plain, (![A_7, B_8, C_9]: (r1_tarski(k2_tarski(A_7, B_8), C_9) | ~r2_hidden(B_8, C_9) | ~r2_hidden(A_7, C_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.21/5.11  tff(c_591, plain, (![C_140, A_141, B_142]: (m2_connsp_2(C_140, A_141, B_142) | ~r1_tarski(B_142, k1_tops_1(A_141, C_140)) | ~m1_subset_1(C_140, k1_zfmisc_1(u1_struct_0(A_141))) | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0(A_141))) | ~l1_pre_topc(A_141) | ~v2_pre_topc(A_141))), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.21/5.11  tff(c_1918, plain, (![C_300, A_301, A_302, B_303]: (m2_connsp_2(C_300, A_301, k2_tarski(A_302, B_303)) | ~m1_subset_1(C_300, k1_zfmisc_1(u1_struct_0(A_301))) | ~m1_subset_1(k2_tarski(A_302, B_303), k1_zfmisc_1(u1_struct_0(A_301))) | ~l1_pre_topc(A_301) | ~v2_pre_topc(A_301) | ~r2_hidden(B_303, k1_tops_1(A_301, C_300)) | ~r2_hidden(A_302, k1_tops_1(A_301, C_300)))), inference(resolution, [status(thm)], [c_8, c_591])).
% 11.21/5.11  tff(c_1928, plain, (![A_302, B_303]: (m2_connsp_2('#skF_3', '#skF_1', k2_tarski(A_302, B_303)) | ~m1_subset_1(k2_tarski(A_302, B_303), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r2_hidden(B_303, k1_tops_1('#skF_1', '#skF_3')) | ~r2_hidden(A_302, k1_tops_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_42, c_1918])).
% 11.21/5.11  tff(c_2116, plain, (![A_309, B_310]: (m2_connsp_2('#skF_3', '#skF_1', k2_tarski(A_309, B_310)) | ~m1_subset_1(k2_tarski(A_309, B_310), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r2_hidden(B_310, k1_tops_1('#skF_1', '#skF_3')) | ~r2_hidden(A_309, k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1928])).
% 11.21/5.11  tff(c_2122, plain, (![A_4]: (m2_connsp_2('#skF_3', '#skF_1', k2_tarski(A_4, A_4)) | ~m1_subset_1(k1_tarski(A_4), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r2_hidden(A_4, k1_tops_1('#skF_1', '#skF_3')) | ~r2_hidden(A_4, k1_tops_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4, c_2116])).
% 11.21/5.11  tff(c_11098, plain, (![A_1241]: (m2_connsp_2('#skF_3', '#skF_1', k1_tarski(A_1241)) | ~m1_subset_1(k1_tarski(A_1241), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r2_hidden(A_1241, k1_tops_1('#skF_1', '#skF_3')) | ~r2_hidden(A_1241, k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_2122])).
% 11.21/5.11  tff(c_11104, plain, (m2_connsp_2('#skF_3', '#skF_1', k1_tarski('#skF_2')) | ~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_223, c_11098])).
% 11.21/5.11  tff(c_11110, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_204, c_11104])).
% 11.21/5.11  tff(c_11117, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_979, c_11110])).
% 11.21/5.11  tff(c_11126, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_48, c_46, c_44, c_80, c_11117])).
% 11.21/5.11  tff(c_11128, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_11126])).
% 11.21/5.11  tff(c_11130, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_58])).
% 11.21/5.11  tff(c_11219, plain, (![A_1267, B_1268]: (k6_domain_1(A_1267, B_1268)=k1_tarski(B_1268) | ~m1_subset_1(B_1268, A_1267) | v1_xboole_0(A_1267))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.21/5.11  tff(c_11234, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_11219])).
% 11.21/5.11  tff(c_11246, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_11234])).
% 11.21/5.11  tff(c_11250, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_11246, c_24])).
% 11.21/5.11  tff(c_11253, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_11250])).
% 11.21/5.11  tff(c_11256, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_11253])).
% 11.21/5.11  tff(c_11260, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_11256])).
% 11.21/5.11  tff(c_11261, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2')), inference(splitRight, [status(thm)], [c_11234])).
% 11.21/5.11  tff(c_11129, plain, (m2_connsp_2('#skF_3', '#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_58])).
% 11.21/5.11  tff(c_11263, plain, (m2_connsp_2('#skF_3', '#skF_1', k1_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_11261, c_11129])).
% 11.21/5.11  tff(c_11262, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_11234])).
% 11.21/5.11  tff(c_11349, plain, (![A_1287, B_1288]: (m1_subset_1(k6_domain_1(A_1287, B_1288), k1_zfmisc_1(A_1287)) | ~m1_subset_1(B_1288, A_1287) | v1_xboole_0(A_1287))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.21/5.11  tff(c_11358, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_11261, c_11349])).
% 11.21/5.11  tff(c_11365, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_11358])).
% 11.21/5.11  tff(c_11366, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_11262, c_11365])).
% 11.21/5.11  tff(c_11689, plain, (![B_1335, A_1336, C_1337]: (r1_tarski(B_1335, k1_tops_1(A_1336, C_1337)) | ~m2_connsp_2(C_1337, A_1336, B_1335) | ~m1_subset_1(C_1337, k1_zfmisc_1(u1_struct_0(A_1336))) | ~m1_subset_1(B_1335, k1_zfmisc_1(u1_struct_0(A_1336))) | ~l1_pre_topc(A_1336) | ~v2_pre_topc(A_1336))), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.21/5.11  tff(c_11699, plain, (![B_1335]: (r1_tarski(B_1335, k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', B_1335) | ~m1_subset_1(B_1335, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_11689])).
% 11.21/5.11  tff(c_11747, plain, (![B_1341]: (r1_tarski(B_1341, k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', B_1341) | ~m1_subset_1(B_1341, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_11699])).
% 11.21/5.11  tff(c_11750, plain, (r1_tarski(k1_tarski('#skF_2'), k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_11366, c_11747])).
% 11.21/5.11  tff(c_11768, plain, (r1_tarski(k1_tarski('#skF_2'), k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_11263, c_11750])).
% 11.21/5.11  tff(c_11158, plain, (![A_1250, C_1251, B_1252]: (r2_hidden(A_1250, C_1251) | ~r1_tarski(k2_tarski(A_1250, B_1252), C_1251))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.21/5.11  tff(c_11165, plain, (![A_4, C_1251]: (r2_hidden(A_4, C_1251) | ~r1_tarski(k1_tarski(A_4), C_1251))), inference(superposition, [status(thm), theory('equality')], [c_4, c_11158])).
% 11.21/5.11  tff(c_11789, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_11768, c_11165])).
% 11.21/5.11  tff(c_11925, plain, (![C_1357, A_1358, B_1359]: (m1_connsp_2(C_1357, A_1358, B_1359) | ~r2_hidden(B_1359, k1_tops_1(A_1358, C_1357)) | ~m1_subset_1(C_1357, k1_zfmisc_1(u1_struct_0(A_1358))) | ~m1_subset_1(B_1359, u1_struct_0(A_1358)) | ~l1_pre_topc(A_1358) | ~v2_pre_topc(A_1358) | v2_struct_0(A_1358))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.21/5.11  tff(c_11929, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_11789, c_11925])).
% 11.21/5.11  tff(c_11936, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_11929])).
% 11.21/5.11  tff(c_11938, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_11130, c_11936])).
% 11.21/5.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.21/5.11  
% 11.21/5.11  Inference rules
% 11.21/5.11  ----------------------
% 11.21/5.11  #Ref     : 0
% 11.21/5.11  #Sup     : 3306
% 11.21/5.11  #Fact    : 0
% 11.21/5.11  #Define  : 0
% 11.21/5.11  #Split   : 25
% 11.21/5.11  #Chain   : 0
% 11.21/5.11  #Close   : 0
% 11.21/5.11  
% 11.21/5.11  Ordering : KBO
% 11.21/5.11  
% 11.21/5.11  Simplification rules
% 11.21/5.11  ----------------------
% 11.21/5.11  #Subsume      : 816
% 11.21/5.11  #Demod        : 547
% 11.21/5.11  #Tautology    : 191
% 11.21/5.11  #SimpNegUnit  : 57
% 11.21/5.11  #BackRed      : 2
% 11.21/5.11  
% 11.21/5.11  #Partial instantiations: 0
% 11.21/5.11  #Strategies tried      : 1
% 11.21/5.11  
% 11.21/5.11  Timing (in seconds)
% 11.21/5.11  ----------------------
% 11.21/5.11  Preprocessing        : 0.78
% 11.21/5.11  Parsing              : 0.39
% 11.21/5.11  CNF conversion       : 0.07
% 11.21/5.11  Main loop            : 3.42
% 11.21/5.11  Inferencing          : 0.77
% 11.21/5.11  Reduction            : 0.83
% 11.21/5.11  Demodulation         : 0.53
% 11.21/5.11  BG Simplification    : 0.10
% 11.21/5.11  Subsumption          : 1.52
% 11.21/5.11  Abstraction          : 0.09
% 11.21/5.11  MUC search           : 0.00
% 11.21/5.11  Cooper               : 0.00
% 11.21/5.11  Total                : 4.26
% 11.21/5.11  Index Insertion      : 0.00
% 11.21/5.11  Index Deletion       : 0.00
% 11.21/5.11  Index Matching       : 0.00
% 11.21/5.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
