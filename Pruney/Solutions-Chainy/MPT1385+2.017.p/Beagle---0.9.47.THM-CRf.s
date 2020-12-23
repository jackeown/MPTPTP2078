%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:17 EST 2020

% Result     : Theorem 4.12s
% Output     : CNFRefutation 4.55s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 258 expanded)
%              Number of leaves         :   40 ( 107 expanded)
%              Depth                    :   13
%              Number of atoms          :  291 ( 795 expanded)
%              Number of equality atoms :    9 (  22 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_173,negated_conjecture,(
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

tff(f_87,axiom,(
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

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_101,axiom,(
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

tff(f_155,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( m1_connsp_2(B,A,C)
               => r2_hidden(C,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_connsp_2)).

tff(f_138,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ? [C] : m1_connsp_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).

tff(f_115,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_54,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_83,plain,(
    ! [A_80,B_81] :
      ( r1_tarski(A_80,B_81)
      | ~ m1_subset_1(A_80,k1_zfmisc_1(B_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_87,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_83])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_58,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m2_connsp_2('#skF_4','#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_88,plain,(
    ~ m2_connsp_2('#skF_4','#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_64,plain,
    ( m2_connsp_2('#skF_4','#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'))
    | m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_120,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_64])).

tff(c_24,plain,(
    ! [A_32,B_33] :
      ( m1_subset_1(A_32,k1_zfmisc_1(B_33))
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_567,plain,(
    ! [B_191,A_192,C_193] :
      ( r2_hidden(B_191,k1_tops_1(A_192,C_193))
      | ~ m1_connsp_2(C_193,A_192,B_191)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(u1_struct_0(A_192)))
      | ~ m1_subset_1(B_191,u1_struct_0(A_192))
      | ~ l1_pre_topc(A_192)
      | ~ v2_pre_topc(A_192)
      | v2_struct_0(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_586,plain,(
    ! [B_191,A_192,A_32] :
      ( r2_hidden(B_191,k1_tops_1(A_192,A_32))
      | ~ m1_connsp_2(A_32,A_192,B_191)
      | ~ m1_subset_1(B_191,u1_struct_0(A_192))
      | ~ l1_pre_topc(A_192)
      | ~ v2_pre_topc(A_192)
      | v2_struct_0(A_192)
      | ~ r1_tarski(A_32,u1_struct_0(A_192)) ) ),
    inference(resolution,[status(thm)],[c_24,c_567])).

tff(c_112,plain,(
    ! [C_95,B_96,A_97] :
      ( ~ v1_xboole_0(C_95)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(C_95))
      | ~ r2_hidden(A_97,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_118,plain,(
    ! [A_97] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_97,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_112])).

tff(c_119,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_122,plain,(
    ! [A_101,B_102] :
      ( k6_domain_1(A_101,B_102) = k1_tarski(B_102)
      | ~ m1_subset_1(B_102,A_101)
      | v1_xboole_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_131,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_122])).

tff(c_136,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_131])).

tff(c_137,plain,(
    ~ m2_connsp_2('#skF_4','#skF_2',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_88])).

tff(c_142,plain,(
    ! [A_103,B_104] :
      ( m1_subset_1(k6_domain_1(A_103,B_104),k1_zfmisc_1(A_103))
      | ~ m1_subset_1(B_104,A_103)
      | v1_xboole_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_153,plain,
    ( m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_142])).

tff(c_158,plain,
    ( m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_153])).

tff(c_159,plain,(
    m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_158])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_29,B_30,C_31] :
      ( r1_tarski(k2_tarski(A_29,B_30),C_31)
      | ~ r2_hidden(B_30,C_31)
      | ~ r2_hidden(A_29,C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_369,plain,(
    ! [C_169,A_170,B_171] :
      ( m2_connsp_2(C_169,A_170,B_171)
      | ~ r1_tarski(B_171,k1_tops_1(A_170,C_169))
      | ~ m1_subset_1(C_169,k1_zfmisc_1(u1_struct_0(A_170)))
      | ~ m1_subset_1(B_171,k1_zfmisc_1(u1_struct_0(A_170)))
      | ~ l1_pre_topc(A_170)
      | ~ v2_pre_topc(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_901,plain,(
    ! [C_240,A_241,A_242,B_243] :
      ( m2_connsp_2(C_240,A_241,k2_tarski(A_242,B_243))
      | ~ m1_subset_1(C_240,k1_zfmisc_1(u1_struct_0(A_241)))
      | ~ m1_subset_1(k2_tarski(A_242,B_243),k1_zfmisc_1(u1_struct_0(A_241)))
      | ~ l1_pre_topc(A_241)
      | ~ v2_pre_topc(A_241)
      | ~ r2_hidden(B_243,k1_tops_1(A_241,C_240))
      | ~ r2_hidden(A_242,k1_tops_1(A_241,C_240)) ) ),
    inference(resolution,[status(thm)],[c_16,c_369])).

tff(c_913,plain,(
    ! [A_242,B_243] :
      ( m2_connsp_2('#skF_4','#skF_2',k2_tarski(A_242,B_243))
      | ~ m1_subset_1(k2_tarski(A_242,B_243),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ r2_hidden(B_243,k1_tops_1('#skF_2','#skF_4'))
      | ~ r2_hidden(A_242,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_48,c_901])).

tff(c_996,plain,(
    ! [A_248,B_249] :
      ( m2_connsp_2('#skF_4','#skF_2',k2_tarski(A_248,B_249))
      | ~ m1_subset_1(k2_tarski(A_248,B_249),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(B_249,k1_tops_1('#skF_2','#skF_4'))
      | ~ r2_hidden(A_248,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_913])).

tff(c_1002,plain,(
    ! [A_1] :
      ( m2_connsp_2('#skF_4','#skF_2',k2_tarski(A_1,A_1))
      | ~ m1_subset_1(k1_tarski(A_1),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(A_1,k1_tops_1('#skF_2','#skF_4'))
      | ~ r2_hidden(A_1,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_996])).

tff(c_1005,plain,(
    ! [A_250] :
      ( m2_connsp_2('#skF_4','#skF_2',k1_tarski(A_250))
      | ~ m1_subset_1(k1_tarski(A_250),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(A_250,k1_tops_1('#skF_2','#skF_4'))
      | ~ r2_hidden(A_250,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1002])).

tff(c_1008,plain,
    ( m2_connsp_2('#skF_4','#skF_2',k1_tarski('#skF_3'))
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_159,c_1005])).

tff(c_1014,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_1008])).

tff(c_1018,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_586,c_1014])).

tff(c_1024,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_54,c_52,c_50,c_120,c_1018])).

tff(c_1026,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1024])).

tff(c_1027,plain,(
    ! [A_97] : ~ r2_hidden(A_97,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_1054,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_64])).

tff(c_1183,plain,(
    ! [C_307,B_308,A_309] :
      ( r2_hidden(C_307,B_308)
      | ~ m1_connsp_2(B_308,A_309,C_307)
      | ~ m1_subset_1(C_307,u1_struct_0(A_309))
      | ~ m1_subset_1(B_308,k1_zfmisc_1(u1_struct_0(A_309)))
      | ~ l1_pre_topc(A_309)
      | ~ v2_pre_topc(A_309)
      | v2_struct_0(A_309) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_1187,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1054,c_1183])).

tff(c_1191,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_50,c_1187])).

tff(c_1193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1027,c_1191])).

tff(c_1194,plain,(
    ~ m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1212,plain,(
    ! [C_320,B_321,A_322] :
      ( ~ v1_xboole_0(C_320)
      | ~ m1_subset_1(B_321,k1_zfmisc_1(C_320))
      | ~ r2_hidden(A_322,B_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1218,plain,(
    ! [A_322] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_322,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_1212])).

tff(c_1219,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1218])).

tff(c_1230,plain,(
    ! [A_329,B_330] :
      ( k6_domain_1(A_329,B_330) = k1_tarski(B_330)
      | ~ m1_subset_1(B_330,A_329)
      | v1_xboole_0(A_329) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1239,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_1230])).

tff(c_1244,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1219,c_1239])).

tff(c_1195,plain,(
    m2_connsp_2('#skF_4','#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1246,plain,(
    m2_connsp_2('#skF_4','#skF_2',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1244,c_1195])).

tff(c_1268,plain,(
    ! [A_336,B_337] :
      ( m1_subset_1(k6_domain_1(A_336,B_337),k1_zfmisc_1(A_336))
      | ~ m1_subset_1(B_337,A_336)
      | v1_xboole_0(A_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1279,plain,
    ( m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1244,c_1268])).

tff(c_1284,plain,
    ( m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1279])).

tff(c_1285,plain,(
    m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1219,c_1284])).

tff(c_1496,plain,(
    ! [B_406,A_407,C_408] :
      ( r1_tarski(B_406,k1_tops_1(A_407,C_408))
      | ~ m2_connsp_2(C_408,A_407,B_406)
      | ~ m1_subset_1(C_408,k1_zfmisc_1(u1_struct_0(A_407)))
      | ~ m1_subset_1(B_406,k1_zfmisc_1(u1_struct_0(A_407)))
      | ~ l1_pre_topc(A_407)
      | ~ v2_pre_topc(A_407) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1508,plain,(
    ! [B_406] :
      ( r1_tarski(B_406,k1_tops_1('#skF_2','#skF_4'))
      | ~ m2_connsp_2('#skF_4','#skF_2',B_406)
      | ~ m1_subset_1(B_406,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_48,c_1496])).

tff(c_1519,plain,(
    ! [B_412] :
      ( r1_tarski(B_412,k1_tops_1('#skF_2','#skF_4'))
      | ~ m2_connsp_2('#skF_4','#skF_2',B_412)
      | ~ m1_subset_1(B_412,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1508])).

tff(c_1526,plain,
    ( r1_tarski(k1_tarski('#skF_3'),k1_tops_1('#skF_2','#skF_4'))
    | ~ m2_connsp_2('#skF_4','#skF_2',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1285,c_1519])).

tff(c_1544,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1246,c_1526])).

tff(c_1203,plain,(
    ! [B_312,C_313,A_314] :
      ( r2_hidden(B_312,C_313)
      | ~ r1_tarski(k2_tarski(A_314,B_312),C_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1206,plain,(
    ! [A_1,C_313] :
      ( r2_hidden(A_1,C_313)
      | ~ r1_tarski(k1_tarski(A_1),C_313) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1203])).

tff(c_1558,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_1544,c_1206])).

tff(c_32,plain,(
    ! [C_47,A_41,B_45] :
      ( m1_connsp_2(C_47,A_41,B_45)
      | ~ r2_hidden(B_45,k1_tops_1(A_41,C_47))
      | ~ m1_subset_1(C_47,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ m1_subset_1(B_45,u1_struct_0(A_41))
      | ~ l1_pre_topc(A_41)
      | ~ v2_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1560,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1558,c_32])).

tff(c_1565,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_1560])).

tff(c_1567,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1194,c_1565])).

tff(c_1569,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1218])).

tff(c_44,plain,(
    ! [A_63,B_64] :
      ( m1_connsp_2('#skF_1'(A_63,B_64),A_63,B_64)
      | ~ m1_subset_1(B_64,u1_struct_0(A_63))
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1722,plain,(
    ! [C_464,A_465,B_466] :
      ( m1_subset_1(C_464,k1_zfmisc_1(u1_struct_0(A_465)))
      | ~ m1_connsp_2(C_464,A_465,B_466)
      | ~ m1_subset_1(B_466,u1_struct_0(A_465))
      | ~ l1_pre_topc(A_465)
      | ~ v2_pre_topc(A_465)
      | v2_struct_0(A_465) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1725,plain,(
    ! [A_63,B_64] :
      ( m1_subset_1('#skF_1'(A_63,B_64),k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ m1_subset_1(B_64,u1_struct_0(A_63))
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63)
      | v2_struct_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_44,c_1722])).

tff(c_1745,plain,(
    ! [C_479,B_480,A_481] :
      ( r2_hidden(C_479,B_480)
      | ~ m1_connsp_2(B_480,A_481,C_479)
      | ~ m1_subset_1(C_479,u1_struct_0(A_481))
      | ~ m1_subset_1(B_480,k1_zfmisc_1(u1_struct_0(A_481)))
      | ~ l1_pre_topc(A_481)
      | ~ v2_pre_topc(A_481)
      | v2_struct_0(A_481) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_1761,plain,(
    ! [B_484,A_485] :
      ( r2_hidden(B_484,'#skF_1'(A_485,B_484))
      | ~ m1_subset_1('#skF_1'(A_485,B_484),k1_zfmisc_1(u1_struct_0(A_485)))
      | ~ m1_subset_1(B_484,u1_struct_0(A_485))
      | ~ l1_pre_topc(A_485)
      | ~ v2_pre_topc(A_485)
      | v2_struct_0(A_485) ) ),
    inference(resolution,[status(thm)],[c_44,c_1745])).

tff(c_1769,plain,(
    ! [B_486,A_487] :
      ( r2_hidden(B_486,'#skF_1'(A_487,B_486))
      | ~ m1_subset_1(B_486,u1_struct_0(A_487))
      | ~ l1_pre_topc(A_487)
      | ~ v2_pre_topc(A_487)
      | v2_struct_0(A_487) ) ),
    inference(resolution,[status(thm)],[c_1725,c_1761])).

tff(c_1731,plain,(
    ! [A_472,B_473] :
      ( m1_subset_1('#skF_1'(A_472,B_473),k1_zfmisc_1(u1_struct_0(A_472)))
      | ~ m1_subset_1(B_473,u1_struct_0(A_472))
      | ~ l1_pre_topc(A_472)
      | ~ v2_pre_topc(A_472)
      | v2_struct_0(A_472) ) ),
    inference(resolution,[status(thm)],[c_44,c_1722])).

tff(c_26,plain,(
    ! [C_36,B_35,A_34] :
      ( ~ v1_xboole_0(C_36)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(C_36))
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1741,plain,(
    ! [A_472,A_34,B_473] :
      ( ~ v1_xboole_0(u1_struct_0(A_472))
      | ~ r2_hidden(A_34,'#skF_1'(A_472,B_473))
      | ~ m1_subset_1(B_473,u1_struct_0(A_472))
      | ~ l1_pre_topc(A_472)
      | ~ v2_pre_topc(A_472)
      | v2_struct_0(A_472) ) ),
    inference(resolution,[status(thm)],[c_1731,c_26])).

tff(c_1790,plain,(
    ! [A_491,B_492] :
      ( ~ v1_xboole_0(u1_struct_0(A_491))
      | ~ m1_subset_1(B_492,u1_struct_0(A_491))
      | ~ l1_pre_topc(A_491)
      | ~ v2_pre_topc(A_491)
      | v2_struct_0(A_491) ) ),
    inference(resolution,[status(thm)],[c_1769,c_1741])).

tff(c_1793,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1790])).

tff(c_1796,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1569,c_1793])).

tff(c_1798,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1796])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:24:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.12/1.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.12/1.76  
% 4.12/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.12/1.77  %$ m2_connsp_2 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.12/1.77  
% 4.12/1.77  %Foreground sorts:
% 4.12/1.77  
% 4.12/1.77  
% 4.12/1.77  %Background operators:
% 4.12/1.77  
% 4.12/1.77  
% 4.12/1.77  %Foreground operators:
% 4.12/1.77  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.12/1.77  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 4.12/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.12/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.12/1.77  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.12/1.77  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.12/1.77  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.12/1.77  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.12/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.12/1.77  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.12/1.77  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.12/1.77  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.12/1.77  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.12/1.77  tff('#skF_2', type, '#skF_2': $i).
% 4.12/1.77  tff('#skF_3', type, '#skF_3': $i).
% 4.12/1.77  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.12/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.12/1.77  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.12/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.12/1.77  tff('#skF_4', type, '#skF_4': $i).
% 4.12/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.12/1.77  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.12/1.77  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.12/1.77  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.12/1.77  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.12/1.77  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.12/1.77  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 4.12/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.12/1.77  
% 4.55/1.79  tff(f_173, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, k6_domain_1(u1_struct_0(A), B)) <=> m1_connsp_2(C, A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_connsp_2)).
% 4.55/1.79  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.55/1.79  tff(f_87, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 4.55/1.79  tff(f_56, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.55/1.79  tff(f_70, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.55/1.79  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 4.55/1.79  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.55/1.79  tff(f_45, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 4.55/1.79  tff(f_101, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_connsp_2)).
% 4.55/1.79  tff(f_155, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (m1_connsp_2(B, A, C) => r2_hidden(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_connsp_2)).
% 4.55/1.79  tff(f_138, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (?[C]: m1_connsp_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 4.55/1.79  tff(f_115, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 4.55/1.79  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.55/1.79  tff(c_54, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.55/1.79  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.55/1.79  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.55/1.79  tff(c_83, plain, (![A_80, B_81]: (r1_tarski(A_80, B_81) | ~m1_subset_1(A_80, k1_zfmisc_1(B_81)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.55/1.79  tff(c_87, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_83])).
% 4.55/1.79  tff(c_50, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.55/1.79  tff(c_58, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m2_connsp_2('#skF_4', '#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.55/1.79  tff(c_88, plain, (~m2_connsp_2('#skF_4', '#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_58])).
% 4.55/1.79  tff(c_64, plain, (m2_connsp_2('#skF_4', '#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')) | m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.55/1.79  tff(c_120, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_88, c_64])).
% 4.55/1.79  tff(c_24, plain, (![A_32, B_33]: (m1_subset_1(A_32, k1_zfmisc_1(B_33)) | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.55/1.79  tff(c_567, plain, (![B_191, A_192, C_193]: (r2_hidden(B_191, k1_tops_1(A_192, C_193)) | ~m1_connsp_2(C_193, A_192, B_191) | ~m1_subset_1(C_193, k1_zfmisc_1(u1_struct_0(A_192))) | ~m1_subset_1(B_191, u1_struct_0(A_192)) | ~l1_pre_topc(A_192) | ~v2_pre_topc(A_192) | v2_struct_0(A_192))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.55/1.79  tff(c_586, plain, (![B_191, A_192, A_32]: (r2_hidden(B_191, k1_tops_1(A_192, A_32)) | ~m1_connsp_2(A_32, A_192, B_191) | ~m1_subset_1(B_191, u1_struct_0(A_192)) | ~l1_pre_topc(A_192) | ~v2_pre_topc(A_192) | v2_struct_0(A_192) | ~r1_tarski(A_32, u1_struct_0(A_192)))), inference(resolution, [status(thm)], [c_24, c_567])).
% 4.55/1.79  tff(c_112, plain, (![C_95, B_96, A_97]: (~v1_xboole_0(C_95) | ~m1_subset_1(B_96, k1_zfmisc_1(C_95)) | ~r2_hidden(A_97, B_96))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.55/1.79  tff(c_118, plain, (![A_97]: (~v1_xboole_0(u1_struct_0('#skF_2')) | ~r2_hidden(A_97, '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_112])).
% 4.55/1.79  tff(c_119, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_118])).
% 4.55/1.79  tff(c_122, plain, (![A_101, B_102]: (k6_domain_1(A_101, B_102)=k1_tarski(B_102) | ~m1_subset_1(B_102, A_101) | v1_xboole_0(A_101))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.55/1.79  tff(c_131, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_50, c_122])).
% 4.55/1.79  tff(c_136, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_119, c_131])).
% 4.55/1.79  tff(c_137, plain, (~m2_connsp_2('#skF_4', '#skF_2', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_88])).
% 4.55/1.79  tff(c_142, plain, (![A_103, B_104]: (m1_subset_1(k6_domain_1(A_103, B_104), k1_zfmisc_1(A_103)) | ~m1_subset_1(B_104, A_103) | v1_xboole_0(A_103))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.55/1.79  tff(c_153, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_136, c_142])).
% 4.55/1.79  tff(c_158, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_153])).
% 4.55/1.79  tff(c_159, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_119, c_158])).
% 4.55/1.79  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.55/1.79  tff(c_16, plain, (![A_29, B_30, C_31]: (r1_tarski(k2_tarski(A_29, B_30), C_31) | ~r2_hidden(B_30, C_31) | ~r2_hidden(A_29, C_31))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.55/1.79  tff(c_369, plain, (![C_169, A_170, B_171]: (m2_connsp_2(C_169, A_170, B_171) | ~r1_tarski(B_171, k1_tops_1(A_170, C_169)) | ~m1_subset_1(C_169, k1_zfmisc_1(u1_struct_0(A_170))) | ~m1_subset_1(B_171, k1_zfmisc_1(u1_struct_0(A_170))) | ~l1_pre_topc(A_170) | ~v2_pre_topc(A_170))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.55/1.79  tff(c_901, plain, (![C_240, A_241, A_242, B_243]: (m2_connsp_2(C_240, A_241, k2_tarski(A_242, B_243)) | ~m1_subset_1(C_240, k1_zfmisc_1(u1_struct_0(A_241))) | ~m1_subset_1(k2_tarski(A_242, B_243), k1_zfmisc_1(u1_struct_0(A_241))) | ~l1_pre_topc(A_241) | ~v2_pre_topc(A_241) | ~r2_hidden(B_243, k1_tops_1(A_241, C_240)) | ~r2_hidden(A_242, k1_tops_1(A_241, C_240)))), inference(resolution, [status(thm)], [c_16, c_369])).
% 4.55/1.79  tff(c_913, plain, (![A_242, B_243]: (m2_connsp_2('#skF_4', '#skF_2', k2_tarski(A_242, B_243)) | ~m1_subset_1(k2_tarski(A_242, B_243), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~r2_hidden(B_243, k1_tops_1('#skF_2', '#skF_4')) | ~r2_hidden(A_242, k1_tops_1('#skF_2', '#skF_4')))), inference(resolution, [status(thm)], [c_48, c_901])).
% 4.55/1.79  tff(c_996, plain, (![A_248, B_249]: (m2_connsp_2('#skF_4', '#skF_2', k2_tarski(A_248, B_249)) | ~m1_subset_1(k2_tarski(A_248, B_249), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(B_249, k1_tops_1('#skF_2', '#skF_4')) | ~r2_hidden(A_248, k1_tops_1('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_913])).
% 4.55/1.79  tff(c_1002, plain, (![A_1]: (m2_connsp_2('#skF_4', '#skF_2', k2_tarski(A_1, A_1)) | ~m1_subset_1(k1_tarski(A_1), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(A_1, k1_tops_1('#skF_2', '#skF_4')) | ~r2_hidden(A_1, k1_tops_1('#skF_2', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_2, c_996])).
% 4.55/1.79  tff(c_1005, plain, (![A_250]: (m2_connsp_2('#skF_4', '#skF_2', k1_tarski(A_250)) | ~m1_subset_1(k1_tarski(A_250), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(A_250, k1_tops_1('#skF_2', '#skF_4')) | ~r2_hidden(A_250, k1_tops_1('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1002])).
% 4.55/1.79  tff(c_1008, plain, (m2_connsp_2('#skF_4', '#skF_2', k1_tarski('#skF_3')) | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_159, c_1005])).
% 4.55/1.79  tff(c_1014, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_137, c_1008])).
% 4.55/1.79  tff(c_1018, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_586, c_1014])).
% 4.55/1.79  tff(c_1024, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_54, c_52, c_50, c_120, c_1018])).
% 4.55/1.79  tff(c_1026, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_1024])).
% 4.55/1.79  tff(c_1027, plain, (![A_97]: (~r2_hidden(A_97, '#skF_4'))), inference(splitRight, [status(thm)], [c_118])).
% 4.55/1.79  tff(c_1054, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_88, c_64])).
% 4.55/1.79  tff(c_1183, plain, (![C_307, B_308, A_309]: (r2_hidden(C_307, B_308) | ~m1_connsp_2(B_308, A_309, C_307) | ~m1_subset_1(C_307, u1_struct_0(A_309)) | ~m1_subset_1(B_308, k1_zfmisc_1(u1_struct_0(A_309))) | ~l1_pre_topc(A_309) | ~v2_pre_topc(A_309) | v2_struct_0(A_309))), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.55/1.79  tff(c_1187, plain, (r2_hidden('#skF_3', '#skF_4') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_1054, c_1183])).
% 4.55/1.79  tff(c_1191, plain, (r2_hidden('#skF_3', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_48, c_50, c_1187])).
% 4.55/1.79  tff(c_1193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_1027, c_1191])).
% 4.55/1.79  tff(c_1194, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_58])).
% 4.55/1.79  tff(c_1212, plain, (![C_320, B_321, A_322]: (~v1_xboole_0(C_320) | ~m1_subset_1(B_321, k1_zfmisc_1(C_320)) | ~r2_hidden(A_322, B_321))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.55/1.79  tff(c_1218, plain, (![A_322]: (~v1_xboole_0(u1_struct_0('#skF_2')) | ~r2_hidden(A_322, '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_1212])).
% 4.55/1.79  tff(c_1219, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1218])).
% 4.55/1.79  tff(c_1230, plain, (![A_329, B_330]: (k6_domain_1(A_329, B_330)=k1_tarski(B_330) | ~m1_subset_1(B_330, A_329) | v1_xboole_0(A_329))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.55/1.79  tff(c_1239, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_50, c_1230])).
% 4.55/1.79  tff(c_1244, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_1219, c_1239])).
% 4.55/1.79  tff(c_1195, plain, (m2_connsp_2('#skF_4', '#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'))), inference(splitRight, [status(thm)], [c_58])).
% 4.55/1.79  tff(c_1246, plain, (m2_connsp_2('#skF_4', '#skF_2', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1244, c_1195])).
% 4.55/1.79  tff(c_1268, plain, (![A_336, B_337]: (m1_subset_1(k6_domain_1(A_336, B_337), k1_zfmisc_1(A_336)) | ~m1_subset_1(B_337, A_336) | v1_xboole_0(A_336))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.55/1.79  tff(c_1279, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1244, c_1268])).
% 4.55/1.79  tff(c_1284, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1279])).
% 4.55/1.79  tff(c_1285, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_1219, c_1284])).
% 4.55/1.79  tff(c_1496, plain, (![B_406, A_407, C_408]: (r1_tarski(B_406, k1_tops_1(A_407, C_408)) | ~m2_connsp_2(C_408, A_407, B_406) | ~m1_subset_1(C_408, k1_zfmisc_1(u1_struct_0(A_407))) | ~m1_subset_1(B_406, k1_zfmisc_1(u1_struct_0(A_407))) | ~l1_pre_topc(A_407) | ~v2_pre_topc(A_407))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.55/1.79  tff(c_1508, plain, (![B_406]: (r1_tarski(B_406, k1_tops_1('#skF_2', '#skF_4')) | ~m2_connsp_2('#skF_4', '#skF_2', B_406) | ~m1_subset_1(B_406, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_1496])).
% 4.55/1.79  tff(c_1519, plain, (![B_412]: (r1_tarski(B_412, k1_tops_1('#skF_2', '#skF_4')) | ~m2_connsp_2('#skF_4', '#skF_2', B_412) | ~m1_subset_1(B_412, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1508])).
% 4.55/1.79  tff(c_1526, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tops_1('#skF_2', '#skF_4')) | ~m2_connsp_2('#skF_4', '#skF_2', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_1285, c_1519])).
% 4.55/1.79  tff(c_1544, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1246, c_1526])).
% 4.55/1.79  tff(c_1203, plain, (![B_312, C_313, A_314]: (r2_hidden(B_312, C_313) | ~r1_tarski(k2_tarski(A_314, B_312), C_313))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.55/1.79  tff(c_1206, plain, (![A_1, C_313]: (r2_hidden(A_1, C_313) | ~r1_tarski(k1_tarski(A_1), C_313))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1203])).
% 4.55/1.79  tff(c_1558, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_1544, c_1206])).
% 4.55/1.79  tff(c_32, plain, (![C_47, A_41, B_45]: (m1_connsp_2(C_47, A_41, B_45) | ~r2_hidden(B_45, k1_tops_1(A_41, C_47)) | ~m1_subset_1(C_47, k1_zfmisc_1(u1_struct_0(A_41))) | ~m1_subset_1(B_45, u1_struct_0(A_41)) | ~l1_pre_topc(A_41) | ~v2_pre_topc(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.55/1.79  tff(c_1560, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_1558, c_32])).
% 4.55/1.79  tff(c_1565, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_1560])).
% 4.55/1.79  tff(c_1567, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_1194, c_1565])).
% 4.55/1.79  tff(c_1569, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_1218])).
% 4.55/1.79  tff(c_44, plain, (![A_63, B_64]: (m1_connsp_2('#skF_1'(A_63, B_64), A_63, B_64) | ~m1_subset_1(B_64, u1_struct_0(A_63)) | ~l1_pre_topc(A_63) | ~v2_pre_topc(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.55/1.79  tff(c_1722, plain, (![C_464, A_465, B_466]: (m1_subset_1(C_464, k1_zfmisc_1(u1_struct_0(A_465))) | ~m1_connsp_2(C_464, A_465, B_466) | ~m1_subset_1(B_466, u1_struct_0(A_465)) | ~l1_pre_topc(A_465) | ~v2_pre_topc(A_465) | v2_struct_0(A_465))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.55/1.79  tff(c_1725, plain, (![A_63, B_64]: (m1_subset_1('#skF_1'(A_63, B_64), k1_zfmisc_1(u1_struct_0(A_63))) | ~m1_subset_1(B_64, u1_struct_0(A_63)) | ~l1_pre_topc(A_63) | ~v2_pre_topc(A_63) | v2_struct_0(A_63))), inference(resolution, [status(thm)], [c_44, c_1722])).
% 4.55/1.79  tff(c_1745, plain, (![C_479, B_480, A_481]: (r2_hidden(C_479, B_480) | ~m1_connsp_2(B_480, A_481, C_479) | ~m1_subset_1(C_479, u1_struct_0(A_481)) | ~m1_subset_1(B_480, k1_zfmisc_1(u1_struct_0(A_481))) | ~l1_pre_topc(A_481) | ~v2_pre_topc(A_481) | v2_struct_0(A_481))), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.55/1.79  tff(c_1761, plain, (![B_484, A_485]: (r2_hidden(B_484, '#skF_1'(A_485, B_484)) | ~m1_subset_1('#skF_1'(A_485, B_484), k1_zfmisc_1(u1_struct_0(A_485))) | ~m1_subset_1(B_484, u1_struct_0(A_485)) | ~l1_pre_topc(A_485) | ~v2_pre_topc(A_485) | v2_struct_0(A_485))), inference(resolution, [status(thm)], [c_44, c_1745])).
% 4.55/1.79  tff(c_1769, plain, (![B_486, A_487]: (r2_hidden(B_486, '#skF_1'(A_487, B_486)) | ~m1_subset_1(B_486, u1_struct_0(A_487)) | ~l1_pre_topc(A_487) | ~v2_pre_topc(A_487) | v2_struct_0(A_487))), inference(resolution, [status(thm)], [c_1725, c_1761])).
% 4.55/1.79  tff(c_1731, plain, (![A_472, B_473]: (m1_subset_1('#skF_1'(A_472, B_473), k1_zfmisc_1(u1_struct_0(A_472))) | ~m1_subset_1(B_473, u1_struct_0(A_472)) | ~l1_pre_topc(A_472) | ~v2_pre_topc(A_472) | v2_struct_0(A_472))), inference(resolution, [status(thm)], [c_44, c_1722])).
% 4.55/1.79  tff(c_26, plain, (![C_36, B_35, A_34]: (~v1_xboole_0(C_36) | ~m1_subset_1(B_35, k1_zfmisc_1(C_36)) | ~r2_hidden(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.55/1.79  tff(c_1741, plain, (![A_472, A_34, B_473]: (~v1_xboole_0(u1_struct_0(A_472)) | ~r2_hidden(A_34, '#skF_1'(A_472, B_473)) | ~m1_subset_1(B_473, u1_struct_0(A_472)) | ~l1_pre_topc(A_472) | ~v2_pre_topc(A_472) | v2_struct_0(A_472))), inference(resolution, [status(thm)], [c_1731, c_26])).
% 4.55/1.79  tff(c_1790, plain, (![A_491, B_492]: (~v1_xboole_0(u1_struct_0(A_491)) | ~m1_subset_1(B_492, u1_struct_0(A_491)) | ~l1_pre_topc(A_491) | ~v2_pre_topc(A_491) | v2_struct_0(A_491))), inference(resolution, [status(thm)], [c_1769, c_1741])).
% 4.55/1.79  tff(c_1793, plain, (~v1_xboole_0(u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1790])).
% 4.55/1.79  tff(c_1796, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1569, c_1793])).
% 4.55/1.79  tff(c_1798, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_1796])).
% 4.55/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.55/1.79  
% 4.55/1.79  Inference rules
% 4.55/1.79  ----------------------
% 4.55/1.79  #Ref     : 0
% 4.55/1.79  #Sup     : 370
% 4.55/1.79  #Fact    : 0
% 4.55/1.79  #Define  : 0
% 4.55/1.79  #Split   : 16
% 4.55/1.79  #Chain   : 0
% 4.55/1.79  #Close   : 0
% 4.55/1.79  
% 4.55/1.79  Ordering : KBO
% 4.55/1.79  
% 4.55/1.79  Simplification rules
% 4.55/1.79  ----------------------
% 4.55/1.79  #Subsume      : 50
% 4.55/1.79  #Demod        : 155
% 4.55/1.79  #Tautology    : 121
% 4.55/1.79  #SimpNegUnit  : 33
% 4.55/1.79  #BackRed      : 2
% 4.55/1.79  
% 4.55/1.79  #Partial instantiations: 0
% 4.55/1.79  #Strategies tried      : 1
% 4.55/1.79  
% 4.55/1.79  Timing (in seconds)
% 4.55/1.79  ----------------------
% 4.55/1.79  Preprocessing        : 0.37
% 4.55/1.79  Parsing              : 0.19
% 4.55/1.79  CNF conversion       : 0.03
% 4.55/1.79  Main loop            : 0.64
% 4.55/1.79  Inferencing          : 0.26
% 4.55/1.79  Reduction            : 0.19
% 4.55/1.79  Demodulation         : 0.13
% 4.55/1.80  BG Simplification    : 0.03
% 4.55/1.80  Subsumption          : 0.11
% 4.55/1.80  Abstraction          : 0.03
% 4.55/1.80  MUC search           : 0.00
% 4.55/1.80  Cooper               : 0.00
% 4.55/1.80  Total                : 1.05
% 4.55/1.80  Index Insertion      : 0.00
% 4.55/1.80  Index Deletion       : 0.00
% 4.55/1.80  Index Matching       : 0.00
% 4.55/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
