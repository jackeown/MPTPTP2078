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
% DateTime   : Thu Dec  3 10:24:13 EST 2020

% Result     : Theorem 5.42s
% Output     : CNFRefutation 5.77s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 303 expanded)
%              Number of leaves         :   30 ( 117 expanded)
%              Depth                    :   10
%              Number of atoms          :  384 (1194 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_161,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( m1_connsp_2(C,A,B)
                <=> ? [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                      & v3_pre_topc(D,A)
                      & r1_tarski(D,C)
                      & r2_hidden(B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_connsp_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_136,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( v3_pre_topc(B,A)
                  & r2_hidden(C,B) )
               => m1_connsp_2(B,A,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_117,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( m1_connsp_2(C,A,B)
                      & m1_connsp_2(D,A,B) )
                  <=> m1_connsp_2(k9_subset_1(u1_struct_0(A),C,D),A,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_connsp_2)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_81,axiom,(
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

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_52,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | r1_tarski('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_63,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_74,plain,(
    ! [A_75,B_76] :
      ( r1_tarski(A_75,B_76)
      | ~ m1_subset_1(A_75,k1_zfmisc_1(B_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_82,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_74])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2429,plain,(
    ! [A_225] :
      ( r1_tarski(A_225,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_225,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_82,c_2])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_56,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | v3_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_61,plain,(
    v3_pre_topc('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_48,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | r2_hidden('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_62,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_60,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_106,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_42,plain,(
    ! [D_70] :
      ( ~ r2_hidden('#skF_2',D_70)
      | ~ r1_tarski(D_70,'#skF_3')
      | ~ v3_pre_topc(D_70,'#skF_1')
      | ~ m1_subset_1(D_70,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_connsp_2('#skF_3','#skF_1','#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_405,plain,(
    ~ m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_1238,plain,(
    ! [B_171,A_172,C_173] :
      ( m1_connsp_2(B_171,A_172,C_173)
      | ~ r2_hidden(C_173,B_171)
      | ~ v3_pre_topc(B_171,A_172)
      | ~ m1_subset_1(C_173,u1_struct_0(A_172))
      | ~ m1_subset_1(B_171,k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ l1_pre_topc(A_172)
      | ~ v2_pre_topc(A_172)
      | v2_struct_0(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1244,plain,(
    ! [B_171] :
      ( m1_connsp_2(B_171,'#skF_1','#skF_2')
      | ~ r2_hidden('#skF_2',B_171)
      | ~ v3_pre_topc(B_171,'#skF_1')
      | ~ m1_subset_1(B_171,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_1238])).

tff(c_1255,plain,(
    ! [B_171] :
      ( m1_connsp_2(B_171,'#skF_1','#skF_2')
      | ~ r2_hidden('#skF_2',B_171)
      | ~ v3_pre_topc(B_171,'#skF_1')
      | ~ m1_subset_1(B_171,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1244])).

tff(c_1257,plain,(
    ! [B_174] :
      ( m1_connsp_2(B_174,'#skF_1','#skF_2')
      | ~ r2_hidden('#skF_2',B_174)
      | ~ v3_pre_topc(B_174,'#skF_1')
      | ~ m1_subset_1(B_174,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1255])).

tff(c_1260,plain,
    ( m1_connsp_2('#skF_4','#skF_1','#skF_2')
    | ~ r2_hidden('#skF_2','#skF_4')
    | ~ v3_pre_topc('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_106,c_1257])).

tff(c_1270,plain,(
    m1_connsp_2('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_62,c_1260])).

tff(c_64,plain,(
    ! [A_71,B_72] :
      ( k3_xboole_0(A_71,B_72) = A_71
      | ~ r1_tarski(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_68,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_63,c_64])).

tff(c_246,plain,(
    ! [A_95,B_96,C_97] :
      ( k9_subset_1(A_95,B_96,C_97) = k3_xboole_0(B_96,C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(A_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_255,plain,(
    ! [B_96] : k9_subset_1(u1_struct_0('#skF_1'),B_96,'#skF_3') = k3_xboole_0(B_96,'#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_246])).

tff(c_1544,plain,(
    ! [D_184,A_185,B_186,C_187] :
      ( m1_connsp_2(D_184,A_185,B_186)
      | ~ m1_connsp_2(k9_subset_1(u1_struct_0(A_185),C_187,D_184),A_185,B_186)
      | ~ m1_subset_1(D_184,k1_zfmisc_1(u1_struct_0(A_185)))
      | ~ m1_subset_1(C_187,k1_zfmisc_1(u1_struct_0(A_185)))
      | ~ m1_subset_1(B_186,u1_struct_0(A_185))
      | ~ l1_pre_topc(A_185)
      | ~ v2_pre_topc(A_185)
      | v2_struct_0(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1567,plain,(
    ! [B_186,B_96] :
      ( m1_connsp_2('#skF_3','#skF_1',B_186)
      | ~ m1_connsp_2(k3_xboole_0(B_96,'#skF_3'),'#skF_1',B_186)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_186,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_1544])).

tff(c_1581,plain,(
    ! [B_186,B_96] :
      ( m1_connsp_2('#skF_3','#skF_1',B_186)
      | ~ m1_connsp_2(k3_xboole_0(B_96,'#skF_3'),'#skF_1',B_186)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_186,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_32,c_1567])).

tff(c_2304,plain,(
    ! [B_217,B_218] :
      ( m1_connsp_2('#skF_3','#skF_1',B_217)
      | ~ m1_connsp_2(k3_xboole_0(B_218,'#skF_3'),'#skF_1',B_217)
      | ~ m1_subset_1(B_218,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_217,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1581])).

tff(c_2324,plain,(
    ! [B_217] :
      ( m1_connsp_2('#skF_3','#skF_1',B_217)
      | ~ m1_connsp_2('#skF_4','#skF_1',B_217)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_217,u1_struct_0('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_2304])).

tff(c_2337,plain,(
    ! [B_219] :
      ( m1_connsp_2('#skF_3','#skF_1',B_219)
      | ~ m1_connsp_2('#skF_4','#skF_1',B_219)
      | ~ m1_subset_1(B_219,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_2324])).

tff(c_2346,plain,
    ( m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_connsp_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_2337])).

tff(c_2351,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1270,c_2346])).

tff(c_2353,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_405,c_2351])).

tff(c_2407,plain,(
    ! [D_224] :
      ( ~ r2_hidden('#skF_2',D_224)
      | ~ r1_tarski(D_224,'#skF_3')
      | ~ v3_pre_topc(D_224,'#skF_1')
      | ~ m1_subset_1(D_224,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_2410,plain,
    ( ~ r2_hidden('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_106,c_2407])).

tff(c_2421,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_63,c_62,c_2410])).

tff(c_2423,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_2427,plain,(
    ~ r1_tarski('#skF_4',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_10,c_2423])).

tff(c_2432,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_2429,c_2427])).

tff(c_2441,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_2432])).

tff(c_2442,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_2444,plain,(
    ! [A_226,B_227] :
      ( r1_tarski(A_226,B_227)
      | ~ m1_subset_1(A_226,k1_zfmisc_1(B_227)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2448,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_2444])).

tff(c_2563,plain,(
    ! [A_256,B_257] :
      ( r1_tarski(k1_tops_1(A_256,B_257),B_257)
      | ~ m1_subset_1(B_257,k1_zfmisc_1(u1_struct_0(A_256)))
      | ~ l1_pre_topc(A_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2568,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_2563])).

tff(c_2572,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2568])).

tff(c_2982,plain,(
    ! [B_309,A_310,C_311] :
      ( r2_hidden(B_309,k1_tops_1(A_310,C_311))
      | ~ m1_connsp_2(C_311,A_310,B_309)
      | ~ m1_subset_1(C_311,k1_zfmisc_1(u1_struct_0(A_310)))
      | ~ m1_subset_1(B_309,u1_struct_0(A_310))
      | ~ l1_pre_topc(A_310)
      | ~ v2_pre_topc(A_310)
      | v2_struct_0(A_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2987,plain,(
    ! [B_309] :
      ( r2_hidden(B_309,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_309)
      | ~ m1_subset_1(B_309,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_2982])).

tff(c_2991,plain,(
    ! [B_309] :
      ( r2_hidden(B_309,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_309)
      | ~ m1_subset_1(B_309,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_2987])).

tff(c_2993,plain,(
    ! [B_312] :
      ( r2_hidden(B_312,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_312)
      | ~ m1_subset_1(B_312,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_2991])).

tff(c_2587,plain,(
    ! [A_259,B_260] :
      ( v3_pre_topc(k1_tops_1(A_259,B_260),A_259)
      | ~ m1_subset_1(B_260,k1_zfmisc_1(u1_struct_0(A_259)))
      | ~ l1_pre_topc(A_259)
      | ~ v2_pre_topc(A_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2593,plain,(
    ! [A_259,A_9] :
      ( v3_pre_topc(k1_tops_1(A_259,A_9),A_259)
      | ~ l1_pre_topc(A_259)
      | ~ v2_pre_topc(A_259)
      | ~ r1_tarski(A_9,u1_struct_0(A_259)) ) ),
    inference(resolution,[status(thm)],[c_10,c_2587])).

tff(c_2463,plain,(
    ! [A_232,C_233,B_234] :
      ( r1_tarski(A_232,C_233)
      | ~ r1_tarski(B_234,C_233)
      | ~ r1_tarski(A_232,B_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2466,plain,(
    ! [A_232] :
      ( r1_tarski(A_232,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_232,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2448,c_2463])).

tff(c_2443,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_50,plain,(
    ! [D_70] :
      ( ~ r2_hidden('#skF_2',D_70)
      | ~ r1_tarski(D_70,'#skF_3')
      | ~ v3_pre_topc(D_70,'#skF_1')
      | ~ m1_subset_1(D_70,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | r1_tarski('#skF_4','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_2638,plain,(
    ! [D_269] :
      ( ~ r2_hidden('#skF_2',D_269)
      | ~ r1_tarski(D_269,'#skF_3')
      | ~ v3_pre_topc(D_269,'#skF_1')
      | ~ m1_subset_1(D_269,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2443,c_50])).

tff(c_2648,plain,(
    ! [A_270] :
      ( ~ r2_hidden('#skF_2',A_270)
      | ~ r1_tarski(A_270,'#skF_3')
      | ~ v3_pre_topc(A_270,'#skF_1')
      | ~ r1_tarski(A_270,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_10,c_2638])).

tff(c_2662,plain,(
    ! [A_271] :
      ( ~ r2_hidden('#skF_2',A_271)
      | ~ v3_pre_topc(A_271,'#skF_1')
      | ~ r1_tarski(A_271,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2466,c_2648])).

tff(c_2666,plain,(
    ! [A_9] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_9))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_9),'#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_9,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_2593,c_2662])).

tff(c_2675,plain,(
    ! [A_9] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_9))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_9),'#skF_3')
      | ~ r1_tarski(A_9,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_2666])).

tff(c_2999,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_2993,c_2675])).

tff(c_3012,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2442,c_2448,c_2572,c_2999])).

tff(c_3013,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_3018,plain,(
    ! [A_317,B_318] :
      ( r1_tarski(A_317,B_318)
      | ~ m1_subset_1(A_317,k1_zfmisc_1(B_318)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3026,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_3018])).

tff(c_3118,plain,(
    ! [A_341,B_342] :
      ( r1_tarski(k1_tops_1(A_341,B_342),B_342)
      | ~ m1_subset_1(B_342,k1_zfmisc_1(u1_struct_0(A_341)))
      | ~ l1_pre_topc(A_341) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3123,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_3118])).

tff(c_3127,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3123])).

tff(c_3539,plain,(
    ! [B_392,A_393,C_394] :
      ( r2_hidden(B_392,k1_tops_1(A_393,C_394))
      | ~ m1_connsp_2(C_394,A_393,B_392)
      | ~ m1_subset_1(C_394,k1_zfmisc_1(u1_struct_0(A_393)))
      | ~ m1_subset_1(B_392,u1_struct_0(A_393))
      | ~ l1_pre_topc(A_393)
      | ~ v2_pre_topc(A_393)
      | v2_struct_0(A_393) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3544,plain,(
    ! [B_392] :
      ( r2_hidden(B_392,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_392)
      | ~ m1_subset_1(B_392,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_3539])).

tff(c_3548,plain,(
    ! [B_392] :
      ( r2_hidden(B_392,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_392)
      | ~ m1_subset_1(B_392,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_3544])).

tff(c_3551,plain,(
    ! [B_398] :
      ( r2_hidden(B_398,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_398)
      | ~ m1_subset_1(B_398,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_3548])).

tff(c_3192,plain,(
    ! [A_349,B_350] :
      ( v3_pre_topc(k1_tops_1(A_349,B_350),A_349)
      | ~ m1_subset_1(B_350,k1_zfmisc_1(u1_struct_0(A_349)))
      | ~ l1_pre_topc(A_349)
      | ~ v2_pre_topc(A_349) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3198,plain,(
    ! [A_349,A_9] :
      ( v3_pre_topc(k1_tops_1(A_349,A_9),A_349)
      | ~ l1_pre_topc(A_349)
      | ~ v2_pre_topc(A_349)
      | ~ r1_tarski(A_9,u1_struct_0(A_349)) ) ),
    inference(resolution,[status(thm)],[c_10,c_3192])).

tff(c_3036,plain,(
    ! [A_319,C_320,B_321] :
      ( r1_tarski(A_319,C_320)
      | ~ r1_tarski(B_321,C_320)
      | ~ r1_tarski(A_319,B_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3039,plain,(
    ! [A_319] :
      ( r1_tarski(A_319,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_319,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3026,c_3036])).

tff(c_3014,plain,(
    ~ r2_hidden('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_46,plain,(
    ! [D_70] :
      ( ~ r2_hidden('#skF_2',D_70)
      | ~ r1_tarski(D_70,'#skF_3')
      | ~ v3_pre_topc(D_70,'#skF_1')
      | ~ m1_subset_1(D_70,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | r2_hidden('#skF_2','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_3083,plain,(
    ! [D_333] :
      ( ~ r2_hidden('#skF_2',D_333)
      | ~ r1_tarski(D_333,'#skF_3')
      | ~ v3_pre_topc(D_333,'#skF_1')
      | ~ m1_subset_1(D_333,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3014,c_46])).

tff(c_3203,plain,(
    ! [A_353] :
      ( ~ r2_hidden('#skF_2',A_353)
      | ~ r1_tarski(A_353,'#skF_3')
      | ~ v3_pre_topc(A_353,'#skF_1')
      | ~ r1_tarski(A_353,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_10,c_3083])).

tff(c_3217,plain,(
    ! [A_354] :
      ( ~ r2_hidden('#skF_2',A_354)
      | ~ v3_pre_topc(A_354,'#skF_1')
      | ~ r1_tarski(A_354,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3039,c_3203])).

tff(c_3221,plain,(
    ! [A_9] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_9))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_9),'#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_9,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_3198,c_3217])).

tff(c_3230,plain,(
    ! [A_9] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_9))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_9),'#skF_3')
      | ~ r1_tarski(A_9,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_3221])).

tff(c_3557,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_3551,c_3230])).

tff(c_3570,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_3013,c_3026,c_3127,c_3557])).

tff(c_3571,plain,(
    m1_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_3576,plain,(
    ! [A_401,B_402] :
      ( r1_tarski(A_401,B_402)
      | ~ m1_subset_1(A_401,k1_zfmisc_1(B_402)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3580,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_3576])).

tff(c_3695,plain,(
    ! [A_429,B_430] :
      ( r1_tarski(k1_tops_1(A_429,B_430),B_430)
      | ~ m1_subset_1(B_430,k1_zfmisc_1(u1_struct_0(A_429)))
      | ~ l1_pre_topc(A_429) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3700,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_3695])).

tff(c_3704,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3700])).

tff(c_4120,plain,(
    ! [B_484,A_485,C_486] :
      ( r2_hidden(B_484,k1_tops_1(A_485,C_486))
      | ~ m1_connsp_2(C_486,A_485,B_484)
      | ~ m1_subset_1(C_486,k1_zfmisc_1(u1_struct_0(A_485)))
      | ~ m1_subset_1(B_484,u1_struct_0(A_485))
      | ~ l1_pre_topc(A_485)
      | ~ v2_pre_topc(A_485)
      | v2_struct_0(A_485) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4125,plain,(
    ! [B_484] :
      ( r2_hidden(B_484,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_484)
      | ~ m1_subset_1(B_484,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_4120])).

tff(c_4129,plain,(
    ! [B_484] :
      ( r2_hidden(B_484,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_484)
      | ~ m1_subset_1(B_484,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_4125])).

tff(c_4131,plain,(
    ! [B_487] :
      ( r2_hidden(B_487,k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_connsp_2('#skF_3','#skF_1',B_487)
      | ~ m1_subset_1(B_487,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_4129])).

tff(c_3719,plain,(
    ! [A_432,B_433] :
      ( v3_pre_topc(k1_tops_1(A_432,B_433),A_432)
      | ~ m1_subset_1(B_433,k1_zfmisc_1(u1_struct_0(A_432)))
      | ~ l1_pre_topc(A_432)
      | ~ v2_pre_topc(A_432) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3785,plain,(
    ! [A_439,A_440] :
      ( v3_pre_topc(k1_tops_1(A_439,A_440),A_439)
      | ~ l1_pre_topc(A_439)
      | ~ v2_pre_topc(A_439)
      | ~ r1_tarski(A_440,u1_struct_0(A_439)) ) ),
    inference(resolution,[status(thm)],[c_10,c_3719])).

tff(c_3595,plain,(
    ! [A_405,C_406,B_407] :
      ( r1_tarski(A_405,C_406)
      | ~ r1_tarski(B_407,C_406)
      | ~ r1_tarski(A_405,B_407) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3598,plain,(
    ! [A_405] :
      ( r1_tarski(A_405,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_405,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3580,c_3595])).

tff(c_3572,plain,(
    ~ v3_pre_topc('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_54,plain,(
    ! [D_70] :
      ( ~ r2_hidden('#skF_2',D_70)
      | ~ r1_tarski(D_70,'#skF_3')
      | ~ v3_pre_topc(D_70,'#skF_1')
      | ~ m1_subset_1(D_70,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v3_pre_topc('#skF_4','#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_3608,plain,(
    ! [D_409] :
      ( ~ r2_hidden('#skF_2',D_409)
      | ~ r1_tarski(D_409,'#skF_3')
      | ~ v3_pre_topc(D_409,'#skF_1')
      | ~ m1_subset_1(D_409,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3572,c_54])).

tff(c_3762,plain,(
    ! [A_437] :
      ( ~ r2_hidden('#skF_2',A_437)
      | ~ r1_tarski(A_437,'#skF_3')
      | ~ v3_pre_topc(A_437,'#skF_1')
      | ~ r1_tarski(A_437,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_10,c_3608])).

tff(c_3774,plain,(
    ! [A_405] :
      ( ~ r2_hidden('#skF_2',A_405)
      | ~ v3_pre_topc(A_405,'#skF_1')
      | ~ r1_tarski(A_405,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3598,c_3762])).

tff(c_3789,plain,(
    ! [A_440] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_440))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_440),'#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_440,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_3785,c_3774])).

tff(c_3792,plain,(
    ! [A_440] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',A_440))
      | ~ r1_tarski(k1_tops_1('#skF_1',A_440),'#skF_3')
      | ~ r1_tarski(A_440,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_3789])).

tff(c_4137,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_connsp_2('#skF_3','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_4131,c_3792])).

tff(c_4150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_3571,c_3580,c_3704,c_4137])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:57:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.42/2.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.42/2.05  
% 5.42/2.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.42/2.05  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.42/2.05  
% 5.42/2.05  %Foreground sorts:
% 5.42/2.05  
% 5.42/2.05  
% 5.42/2.05  %Background operators:
% 5.42/2.05  
% 5.42/2.05  
% 5.42/2.05  %Foreground operators:
% 5.42/2.05  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.42/2.05  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 5.42/2.05  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.42/2.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.42/2.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.42/2.05  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.42/2.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.42/2.05  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.42/2.05  tff('#skF_2', type, '#skF_2': $i).
% 5.42/2.05  tff('#skF_3', type, '#skF_3': $i).
% 5.42/2.05  tff('#skF_1', type, '#skF_1': $i).
% 5.42/2.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.42/2.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.42/2.05  tff('#skF_4', type, '#skF_4': $i).
% 5.42/2.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.42/2.05  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.42/2.05  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.42/2.05  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.42/2.05  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 5.42/2.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.42/2.05  
% 5.77/2.08  tff(f_161, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_connsp_2)).
% 5.77/2.08  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.77/2.08  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.77/2.08  tff(f_136, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_connsp_2)).
% 5.77/2.08  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.77/2.08  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 5.77/2.08  tff(f_117, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((m1_connsp_2(C, A, B) & m1_connsp_2(D, A, B)) <=> m1_connsp_2(k9_subset_1(u1_struct_0(A), C, D), A, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_connsp_2)).
% 5.77/2.08  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 5.77/2.08  tff(f_81, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 5.77/2.08  tff(f_57, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 5.77/2.08  tff(c_34, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_161])).
% 5.77/2.08  tff(c_52, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | r1_tarski('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_161])).
% 5.77/2.08  tff(c_63, plain, (r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_52])).
% 5.77/2.08  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 5.77/2.08  tff(c_74, plain, (![A_75, B_76]: (r1_tarski(A_75, B_76) | ~m1_subset_1(A_75, k1_zfmisc_1(B_76)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.77/2.08  tff(c_82, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_74])).
% 5.77/2.08  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.77/2.08  tff(c_2429, plain, (![A_225]: (r1_tarski(A_225, u1_struct_0('#skF_1')) | ~r1_tarski(A_225, '#skF_3'))), inference(resolution, [status(thm)], [c_82, c_2])).
% 5.77/2.08  tff(c_10, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.77/2.08  tff(c_56, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | v3_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 5.77/2.08  tff(c_61, plain, (v3_pre_topc('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_56])).
% 5.77/2.08  tff(c_48, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | r2_hidden('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_161])).
% 5.77/2.08  tff(c_62, plain, (r2_hidden('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_48])).
% 5.77/2.08  tff(c_60, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 5.77/2.08  tff(c_106, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_60])).
% 5.77/2.08  tff(c_42, plain, (![D_70]: (~r2_hidden('#skF_2', D_70) | ~r1_tarski(D_70, '#skF_3') | ~v3_pre_topc(D_70, '#skF_1') | ~m1_subset_1(D_70, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_connsp_2('#skF_3', '#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_161])).
% 5.77/2.08  tff(c_405, plain, (~m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_42])).
% 5.77/2.08  tff(c_40, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 5.77/2.08  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 5.77/2.08  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_161])).
% 5.77/2.08  tff(c_1238, plain, (![B_171, A_172, C_173]: (m1_connsp_2(B_171, A_172, C_173) | ~r2_hidden(C_173, B_171) | ~v3_pre_topc(B_171, A_172) | ~m1_subset_1(C_173, u1_struct_0(A_172)) | ~m1_subset_1(B_171, k1_zfmisc_1(u1_struct_0(A_172))) | ~l1_pre_topc(A_172) | ~v2_pre_topc(A_172) | v2_struct_0(A_172))), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.77/2.08  tff(c_1244, plain, (![B_171]: (m1_connsp_2(B_171, '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', B_171) | ~v3_pre_topc(B_171, '#skF_1') | ~m1_subset_1(B_171, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_1238])).
% 5.77/2.08  tff(c_1255, plain, (![B_171]: (m1_connsp_2(B_171, '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', B_171) | ~v3_pre_topc(B_171, '#skF_1') | ~m1_subset_1(B_171, k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1244])).
% 5.77/2.08  tff(c_1257, plain, (![B_174]: (m1_connsp_2(B_174, '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', B_174) | ~v3_pre_topc(B_174, '#skF_1') | ~m1_subset_1(B_174, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_1255])).
% 5.77/2.08  tff(c_1260, plain, (m1_connsp_2('#skF_4', '#skF_1', '#skF_2') | ~r2_hidden('#skF_2', '#skF_4') | ~v3_pre_topc('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_106, c_1257])).
% 5.77/2.08  tff(c_1270, plain, (m1_connsp_2('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_62, c_1260])).
% 5.77/2.08  tff(c_64, plain, (![A_71, B_72]: (k3_xboole_0(A_71, B_72)=A_71 | ~r1_tarski(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.77/2.08  tff(c_68, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_63, c_64])).
% 5.77/2.08  tff(c_246, plain, (![A_95, B_96, C_97]: (k9_subset_1(A_95, B_96, C_97)=k3_xboole_0(B_96, C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(A_95)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.77/2.08  tff(c_255, plain, (![B_96]: (k9_subset_1(u1_struct_0('#skF_1'), B_96, '#skF_3')=k3_xboole_0(B_96, '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_246])).
% 5.77/2.08  tff(c_1544, plain, (![D_184, A_185, B_186, C_187]: (m1_connsp_2(D_184, A_185, B_186) | ~m1_connsp_2(k9_subset_1(u1_struct_0(A_185), C_187, D_184), A_185, B_186) | ~m1_subset_1(D_184, k1_zfmisc_1(u1_struct_0(A_185))) | ~m1_subset_1(C_187, k1_zfmisc_1(u1_struct_0(A_185))) | ~m1_subset_1(B_186, u1_struct_0(A_185)) | ~l1_pre_topc(A_185) | ~v2_pre_topc(A_185) | v2_struct_0(A_185))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.77/2.08  tff(c_1567, plain, (![B_186, B_96]: (m1_connsp_2('#skF_3', '#skF_1', B_186) | ~m1_connsp_2(k3_xboole_0(B_96, '#skF_3'), '#skF_1', B_186) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_186, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_255, c_1544])).
% 5.77/2.08  tff(c_1581, plain, (![B_186, B_96]: (m1_connsp_2('#skF_3', '#skF_1', B_186) | ~m1_connsp_2(k3_xboole_0(B_96, '#skF_3'), '#skF_1', B_186) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_186, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_32, c_1567])).
% 5.77/2.08  tff(c_2304, plain, (![B_217, B_218]: (m1_connsp_2('#skF_3', '#skF_1', B_217) | ~m1_connsp_2(k3_xboole_0(B_218, '#skF_3'), '#skF_1', B_217) | ~m1_subset_1(B_218, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_217, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_40, c_1581])).
% 5.77/2.08  tff(c_2324, plain, (![B_217]: (m1_connsp_2('#skF_3', '#skF_1', B_217) | ~m1_connsp_2('#skF_4', '#skF_1', B_217) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_217, u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_68, c_2304])).
% 5.77/2.08  tff(c_2337, plain, (![B_219]: (m1_connsp_2('#skF_3', '#skF_1', B_219) | ~m1_connsp_2('#skF_4', '#skF_1', B_219) | ~m1_subset_1(B_219, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_2324])).
% 5.77/2.08  tff(c_2346, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_connsp_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_2337])).
% 5.77/2.08  tff(c_2351, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1270, c_2346])).
% 5.77/2.08  tff(c_2353, plain, $false, inference(negUnitSimplification, [status(thm)], [c_405, c_2351])).
% 5.77/2.08  tff(c_2407, plain, (![D_224]: (~r2_hidden('#skF_2', D_224) | ~r1_tarski(D_224, '#skF_3') | ~v3_pre_topc(D_224, '#skF_1') | ~m1_subset_1(D_224, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_42])).
% 5.77/2.08  tff(c_2410, plain, (~r2_hidden('#skF_2', '#skF_4') | ~r1_tarski('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_106, c_2407])).
% 5.77/2.08  tff(c_2421, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_63, c_62, c_2410])).
% 5.77/2.08  tff(c_2423, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_60])).
% 5.77/2.08  tff(c_2427, plain, (~r1_tarski('#skF_4', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_2423])).
% 5.77/2.08  tff(c_2432, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_2429, c_2427])).
% 5.77/2.08  tff(c_2441, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_2432])).
% 5.77/2.08  tff(c_2442, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 5.77/2.08  tff(c_2444, plain, (![A_226, B_227]: (r1_tarski(A_226, B_227) | ~m1_subset_1(A_226, k1_zfmisc_1(B_227)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.77/2.08  tff(c_2448, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_2444])).
% 5.77/2.08  tff(c_2563, plain, (![A_256, B_257]: (r1_tarski(k1_tops_1(A_256, B_257), B_257) | ~m1_subset_1(B_257, k1_zfmisc_1(u1_struct_0(A_256))) | ~l1_pre_topc(A_256))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.77/2.08  tff(c_2568, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_2563])).
% 5.77/2.08  tff(c_2572, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2568])).
% 5.77/2.08  tff(c_2982, plain, (![B_309, A_310, C_311]: (r2_hidden(B_309, k1_tops_1(A_310, C_311)) | ~m1_connsp_2(C_311, A_310, B_309) | ~m1_subset_1(C_311, k1_zfmisc_1(u1_struct_0(A_310))) | ~m1_subset_1(B_309, u1_struct_0(A_310)) | ~l1_pre_topc(A_310) | ~v2_pre_topc(A_310) | v2_struct_0(A_310))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.77/2.08  tff(c_2987, plain, (![B_309]: (r2_hidden(B_309, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_309) | ~m1_subset_1(B_309, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_2982])).
% 5.77/2.08  tff(c_2991, plain, (![B_309]: (r2_hidden(B_309, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_309) | ~m1_subset_1(B_309, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_2987])).
% 5.77/2.08  tff(c_2993, plain, (![B_312]: (r2_hidden(B_312, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_312) | ~m1_subset_1(B_312, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_40, c_2991])).
% 5.77/2.08  tff(c_2587, plain, (![A_259, B_260]: (v3_pre_topc(k1_tops_1(A_259, B_260), A_259) | ~m1_subset_1(B_260, k1_zfmisc_1(u1_struct_0(A_259))) | ~l1_pre_topc(A_259) | ~v2_pre_topc(A_259))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.77/2.08  tff(c_2593, plain, (![A_259, A_9]: (v3_pre_topc(k1_tops_1(A_259, A_9), A_259) | ~l1_pre_topc(A_259) | ~v2_pre_topc(A_259) | ~r1_tarski(A_9, u1_struct_0(A_259)))), inference(resolution, [status(thm)], [c_10, c_2587])).
% 5.77/2.08  tff(c_2463, plain, (![A_232, C_233, B_234]: (r1_tarski(A_232, C_233) | ~r1_tarski(B_234, C_233) | ~r1_tarski(A_232, B_234))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.77/2.08  tff(c_2466, plain, (![A_232]: (r1_tarski(A_232, u1_struct_0('#skF_1')) | ~r1_tarski(A_232, '#skF_3'))), inference(resolution, [status(thm)], [c_2448, c_2463])).
% 5.77/2.08  tff(c_2443, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_52])).
% 5.77/2.08  tff(c_50, plain, (![D_70]: (~r2_hidden('#skF_2', D_70) | ~r1_tarski(D_70, '#skF_3') | ~v3_pre_topc(D_70, '#skF_1') | ~m1_subset_1(D_70, k1_zfmisc_1(u1_struct_0('#skF_1'))) | r1_tarski('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_161])).
% 5.77/2.08  tff(c_2638, plain, (![D_269]: (~r2_hidden('#skF_2', D_269) | ~r1_tarski(D_269, '#skF_3') | ~v3_pre_topc(D_269, '#skF_1') | ~m1_subset_1(D_269, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_2443, c_50])).
% 5.77/2.08  tff(c_2648, plain, (![A_270]: (~r2_hidden('#skF_2', A_270) | ~r1_tarski(A_270, '#skF_3') | ~v3_pre_topc(A_270, '#skF_1') | ~r1_tarski(A_270, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_10, c_2638])).
% 5.77/2.08  tff(c_2662, plain, (![A_271]: (~r2_hidden('#skF_2', A_271) | ~v3_pre_topc(A_271, '#skF_1') | ~r1_tarski(A_271, '#skF_3'))), inference(resolution, [status(thm)], [c_2466, c_2648])).
% 5.77/2.08  tff(c_2666, plain, (![A_9]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_9)) | ~r1_tarski(k1_tops_1('#skF_1', A_9), '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_9, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_2593, c_2662])).
% 5.77/2.08  tff(c_2675, plain, (![A_9]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_9)) | ~r1_tarski(k1_tops_1('#skF_1', A_9), '#skF_3') | ~r1_tarski(A_9, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_2666])).
% 5.77/2.08  tff(c_2999, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1')) | ~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_2993, c_2675])).
% 5.77/2.08  tff(c_3012, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_2442, c_2448, c_2572, c_2999])).
% 5.77/2.08  tff(c_3013, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 5.77/2.08  tff(c_3018, plain, (![A_317, B_318]: (r1_tarski(A_317, B_318) | ~m1_subset_1(A_317, k1_zfmisc_1(B_318)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.77/2.08  tff(c_3026, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_3018])).
% 5.77/2.08  tff(c_3118, plain, (![A_341, B_342]: (r1_tarski(k1_tops_1(A_341, B_342), B_342) | ~m1_subset_1(B_342, k1_zfmisc_1(u1_struct_0(A_341))) | ~l1_pre_topc(A_341))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.77/2.08  tff(c_3123, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_3118])).
% 5.77/2.08  tff(c_3127, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_3123])).
% 5.77/2.08  tff(c_3539, plain, (![B_392, A_393, C_394]: (r2_hidden(B_392, k1_tops_1(A_393, C_394)) | ~m1_connsp_2(C_394, A_393, B_392) | ~m1_subset_1(C_394, k1_zfmisc_1(u1_struct_0(A_393))) | ~m1_subset_1(B_392, u1_struct_0(A_393)) | ~l1_pre_topc(A_393) | ~v2_pre_topc(A_393) | v2_struct_0(A_393))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.77/2.08  tff(c_3544, plain, (![B_392]: (r2_hidden(B_392, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_392) | ~m1_subset_1(B_392, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_3539])).
% 5.77/2.08  tff(c_3548, plain, (![B_392]: (r2_hidden(B_392, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_392) | ~m1_subset_1(B_392, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_3544])).
% 5.77/2.08  tff(c_3551, plain, (![B_398]: (r2_hidden(B_398, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_398) | ~m1_subset_1(B_398, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_40, c_3548])).
% 5.77/2.08  tff(c_3192, plain, (![A_349, B_350]: (v3_pre_topc(k1_tops_1(A_349, B_350), A_349) | ~m1_subset_1(B_350, k1_zfmisc_1(u1_struct_0(A_349))) | ~l1_pre_topc(A_349) | ~v2_pre_topc(A_349))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.77/2.08  tff(c_3198, plain, (![A_349, A_9]: (v3_pre_topc(k1_tops_1(A_349, A_9), A_349) | ~l1_pre_topc(A_349) | ~v2_pre_topc(A_349) | ~r1_tarski(A_9, u1_struct_0(A_349)))), inference(resolution, [status(thm)], [c_10, c_3192])).
% 5.77/2.08  tff(c_3036, plain, (![A_319, C_320, B_321]: (r1_tarski(A_319, C_320) | ~r1_tarski(B_321, C_320) | ~r1_tarski(A_319, B_321))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.77/2.08  tff(c_3039, plain, (![A_319]: (r1_tarski(A_319, u1_struct_0('#skF_1')) | ~r1_tarski(A_319, '#skF_3'))), inference(resolution, [status(thm)], [c_3026, c_3036])).
% 5.77/2.08  tff(c_3014, plain, (~r2_hidden('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_48])).
% 5.77/2.08  tff(c_46, plain, (![D_70]: (~r2_hidden('#skF_2', D_70) | ~r1_tarski(D_70, '#skF_3') | ~v3_pre_topc(D_70, '#skF_1') | ~m1_subset_1(D_70, k1_zfmisc_1(u1_struct_0('#skF_1'))) | r2_hidden('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_161])).
% 5.77/2.08  tff(c_3083, plain, (![D_333]: (~r2_hidden('#skF_2', D_333) | ~r1_tarski(D_333, '#skF_3') | ~v3_pre_topc(D_333, '#skF_1') | ~m1_subset_1(D_333, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_3014, c_46])).
% 5.77/2.08  tff(c_3203, plain, (![A_353]: (~r2_hidden('#skF_2', A_353) | ~r1_tarski(A_353, '#skF_3') | ~v3_pre_topc(A_353, '#skF_1') | ~r1_tarski(A_353, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_10, c_3083])).
% 5.77/2.08  tff(c_3217, plain, (![A_354]: (~r2_hidden('#skF_2', A_354) | ~v3_pre_topc(A_354, '#skF_1') | ~r1_tarski(A_354, '#skF_3'))), inference(resolution, [status(thm)], [c_3039, c_3203])).
% 5.77/2.08  tff(c_3221, plain, (![A_9]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_9)) | ~r1_tarski(k1_tops_1('#skF_1', A_9), '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_9, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_3198, c_3217])).
% 5.77/2.08  tff(c_3230, plain, (![A_9]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_9)) | ~r1_tarski(k1_tops_1('#skF_1', A_9), '#skF_3') | ~r1_tarski(A_9, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_3221])).
% 5.77/2.08  tff(c_3557, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1')) | ~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_3551, c_3230])).
% 5.77/2.08  tff(c_3570, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_3013, c_3026, c_3127, c_3557])).
% 5.77/2.08  tff(c_3571, plain, (m1_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_56])).
% 5.77/2.08  tff(c_3576, plain, (![A_401, B_402]: (r1_tarski(A_401, B_402) | ~m1_subset_1(A_401, k1_zfmisc_1(B_402)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.77/2.08  tff(c_3580, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_3576])).
% 5.77/2.08  tff(c_3695, plain, (![A_429, B_430]: (r1_tarski(k1_tops_1(A_429, B_430), B_430) | ~m1_subset_1(B_430, k1_zfmisc_1(u1_struct_0(A_429))) | ~l1_pre_topc(A_429))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.77/2.08  tff(c_3700, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_3695])).
% 5.77/2.08  tff(c_3704, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_3700])).
% 5.77/2.08  tff(c_4120, plain, (![B_484, A_485, C_486]: (r2_hidden(B_484, k1_tops_1(A_485, C_486)) | ~m1_connsp_2(C_486, A_485, B_484) | ~m1_subset_1(C_486, k1_zfmisc_1(u1_struct_0(A_485))) | ~m1_subset_1(B_484, u1_struct_0(A_485)) | ~l1_pre_topc(A_485) | ~v2_pre_topc(A_485) | v2_struct_0(A_485))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.77/2.08  tff(c_4125, plain, (![B_484]: (r2_hidden(B_484, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_484) | ~m1_subset_1(B_484, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_4120])).
% 5.77/2.08  tff(c_4129, plain, (![B_484]: (r2_hidden(B_484, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_484) | ~m1_subset_1(B_484, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_4125])).
% 5.77/2.08  tff(c_4131, plain, (![B_487]: (r2_hidden(B_487, k1_tops_1('#skF_1', '#skF_3')) | ~m1_connsp_2('#skF_3', '#skF_1', B_487) | ~m1_subset_1(B_487, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_40, c_4129])).
% 5.77/2.08  tff(c_3719, plain, (![A_432, B_433]: (v3_pre_topc(k1_tops_1(A_432, B_433), A_432) | ~m1_subset_1(B_433, k1_zfmisc_1(u1_struct_0(A_432))) | ~l1_pre_topc(A_432) | ~v2_pre_topc(A_432))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.77/2.08  tff(c_3785, plain, (![A_439, A_440]: (v3_pre_topc(k1_tops_1(A_439, A_440), A_439) | ~l1_pre_topc(A_439) | ~v2_pre_topc(A_439) | ~r1_tarski(A_440, u1_struct_0(A_439)))), inference(resolution, [status(thm)], [c_10, c_3719])).
% 5.77/2.08  tff(c_3595, plain, (![A_405, C_406, B_407]: (r1_tarski(A_405, C_406) | ~r1_tarski(B_407, C_406) | ~r1_tarski(A_405, B_407))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.77/2.08  tff(c_3598, plain, (![A_405]: (r1_tarski(A_405, u1_struct_0('#skF_1')) | ~r1_tarski(A_405, '#skF_3'))), inference(resolution, [status(thm)], [c_3580, c_3595])).
% 5.77/2.08  tff(c_3572, plain, (~v3_pre_topc('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_56])).
% 5.77/2.08  tff(c_54, plain, (![D_70]: (~r2_hidden('#skF_2', D_70) | ~r1_tarski(D_70, '#skF_3') | ~v3_pre_topc(D_70, '#skF_1') | ~m1_subset_1(D_70, k1_zfmisc_1(u1_struct_0('#skF_1'))) | v3_pre_topc('#skF_4', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_161])).
% 5.77/2.08  tff(c_3608, plain, (![D_409]: (~r2_hidden('#skF_2', D_409) | ~r1_tarski(D_409, '#skF_3') | ~v3_pre_topc(D_409, '#skF_1') | ~m1_subset_1(D_409, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_3572, c_54])).
% 5.77/2.08  tff(c_3762, plain, (![A_437]: (~r2_hidden('#skF_2', A_437) | ~r1_tarski(A_437, '#skF_3') | ~v3_pre_topc(A_437, '#skF_1') | ~r1_tarski(A_437, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_10, c_3608])).
% 5.77/2.08  tff(c_3774, plain, (![A_405]: (~r2_hidden('#skF_2', A_405) | ~v3_pre_topc(A_405, '#skF_1') | ~r1_tarski(A_405, '#skF_3'))), inference(resolution, [status(thm)], [c_3598, c_3762])).
% 5.77/2.08  tff(c_3789, plain, (![A_440]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_440)) | ~r1_tarski(k1_tops_1('#skF_1', A_440), '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_440, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_3785, c_3774])).
% 5.77/2.08  tff(c_3792, plain, (![A_440]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', A_440)) | ~r1_tarski(k1_tops_1('#skF_1', A_440), '#skF_3') | ~r1_tarski(A_440, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_3789])).
% 5.77/2.08  tff(c_4137, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1')) | ~m1_connsp_2('#skF_3', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_4131, c_3792])).
% 5.77/2.08  tff(c_4150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_3571, c_3580, c_3704, c_4137])).
% 5.77/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.77/2.08  
% 5.77/2.08  Inference rules
% 5.77/2.08  ----------------------
% 5.77/2.08  #Ref     : 0
% 5.77/2.08  #Sup     : 901
% 5.77/2.08  #Fact    : 0
% 5.77/2.08  #Define  : 0
% 5.77/2.08  #Split   : 16
% 5.77/2.08  #Chain   : 0
% 5.77/2.08  #Close   : 0
% 5.77/2.08  
% 5.77/2.08  Ordering : KBO
% 5.77/2.08  
% 5.77/2.08  Simplification rules
% 5.77/2.08  ----------------------
% 5.77/2.08  #Subsume      : 170
% 5.77/2.08  #Demod        : 487
% 5.77/2.08  #Tautology    : 327
% 5.77/2.08  #SimpNegUnit  : 61
% 5.77/2.08  #BackRed      : 0
% 5.77/2.08  
% 5.77/2.08  #Partial instantiations: 0
% 5.77/2.08  #Strategies tried      : 1
% 5.77/2.08  
% 5.77/2.08  Timing (in seconds)
% 5.77/2.08  ----------------------
% 5.77/2.08  Preprocessing        : 0.33
% 5.77/2.08  Parsing              : 0.17
% 5.77/2.08  CNF conversion       : 0.03
% 5.77/2.08  Main loop            : 0.95
% 5.77/2.08  Inferencing          : 0.36
% 5.77/2.08  Reduction            : 0.29
% 5.77/2.08  Demodulation         : 0.19
% 5.77/2.08  BG Simplification    : 0.04
% 5.77/2.08  Subsumption          : 0.19
% 5.77/2.08  Abstraction          : 0.05
% 5.77/2.08  MUC search           : 0.00
% 5.77/2.08  Cooper               : 0.00
% 5.77/2.08  Total                : 1.33
% 5.77/2.08  Index Insertion      : 0.00
% 5.77/2.08  Index Deletion       : 0.00
% 5.77/2.08  Index Matching       : 0.00
% 5.77/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
