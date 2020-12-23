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
% DateTime   : Thu Dec  3 10:20:46 EST 2020

% Result     : Theorem 8.11s
% Output     : CNFRefutation 8.11s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 318 expanded)
%              Number of leaves         :   31 ( 117 expanded)
%              Depth                    :   15
%              Number of atoms          :  308 ( 979 expanded)
%              Number of equality atoms :   12 (  21 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_127,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B,C] :
            ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
           => ( r2_hidden(B,k1_tops_1(A,C))
            <=> ? [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                  & v3_pre_topc(D,A)
                  & r1_tarski(D,C)
                  & r2_hidden(B,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tops_1)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(c_36,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_3434,plain,(
    ! [A_365,B_366] :
      ( r1_tarski(k1_tops_1(A_365,B_366),B_366)
      | ~ m1_subset_1(B_366,k1_zfmisc_1(u1_struct_0(A_365)))
      | ~ l1_pre_topc(A_365) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_3442,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_3434])).

tff(c_3447,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3442])).

tff(c_2895,plain,(
    ! [A_301,B_302] :
      ( r1_tarski(k1_tops_1(A_301,B_302),B_302)
      | ~ m1_subset_1(B_302,k1_zfmisc_1(u1_struct_0(A_301)))
      | ~ l1_pre_topc(A_301) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2903,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_2895])).

tff(c_2908,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2903])).

tff(c_2327,plain,(
    ! [A_237,B_238] :
      ( r1_tarski(k1_tops_1(A_237,B_238),B_238)
      | ~ m1_subset_1(B_238,k1_zfmisc_1(u1_struct_0(A_237)))
      | ~ l1_pre_topc(A_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2335,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_2327])).

tff(c_2340,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2335])).

tff(c_50,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | r1_tarski('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_70,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_60,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | ~ m1_subset_1(A_46,k1_zfmisc_1(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_68,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_60])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_80,plain,(
    ! [C_53,B_54,A_55] :
      ( r2_hidden(C_53,B_54)
      | ~ r2_hidden(C_53,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1794,plain,(
    ! [A_175,B_176,B_177] :
      ( r2_hidden('#skF_1'(A_175,B_176),B_177)
      | ~ r1_tarski(A_175,B_177)
      | r1_tarski(A_175,B_176) ) ),
    inference(resolution,[status(thm)],[c_6,c_80])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2081,plain,(
    ! [A_203,B_204,B_205,B_206] :
      ( r2_hidden('#skF_1'(A_203,B_204),B_205)
      | ~ r1_tarski(B_206,B_205)
      | ~ r1_tarski(A_203,B_206)
      | r1_tarski(A_203,B_204) ) ),
    inference(resolution,[status(thm)],[c_1794,c_2])).

tff(c_2177,plain,(
    ! [A_214,B_215] :
      ( r2_hidden('#skF_1'(A_214,B_215),u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_214,'#skF_4')
      | r1_tarski(A_214,B_215) ) ),
    inference(resolution,[status(thm)],[c_68,c_2081])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2186,plain,(
    ! [A_216] :
      ( ~ r1_tarski(A_216,'#skF_4')
      | r1_tarski(A_216,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_2177,c_4])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_54,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | v3_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_69,plain,(
    v3_pre_topc('#skF_5','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_46,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_71,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_58,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_108,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_86,plain,(
    ! [B_54] :
      ( r2_hidden('#skF_3',B_54)
      | ~ r1_tarski('#skF_5',B_54) ) ),
    inference(resolution,[status(thm)],[c_71,c_80])).

tff(c_40,plain,(
    ! [D_43] :
      ( ~ r2_hidden('#skF_3',D_43)
      | ~ r1_tarski(D_43,'#skF_4')
      | ~ v3_pre_topc(D_43,'#skF_2')
      | ~ m1_subset_1(D_43,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_698,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_706,plain,(
    ~ r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_86,c_698])).

tff(c_161,plain,(
    ! [A_67,B_68] :
      ( k3_subset_1(A_67,k3_subset_1(A_67,B_68)) = B_68
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_171,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_108,c_161])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k3_subset_1(A_6,B_7),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_437,plain,(
    ! [B_95,A_96] :
      ( v4_pre_topc(B_95,A_96)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_96),B_95),A_96)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_444,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),'#skF_2')
    | ~ v3_pre_topc('#skF_5','#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_437])).

tff(c_449,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_69,c_444])).

tff(c_1013,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_449])).

tff(c_1016,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_8,c_1013])).

tff(c_1023,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_1016])).

tff(c_1024,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_449])).

tff(c_1025,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_449])).

tff(c_18,plain,(
    ! [A_12,B_14] :
      ( k2_pre_topc(A_12,B_14) = B_14
      | ~ v4_pre_topc(B_14,A_12)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1070,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1025,c_18])).

tff(c_1085,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1024,c_1070])).

tff(c_20,plain,(
    ! [A_15,B_17] :
      ( k3_subset_1(u1_struct_0(A_15),k2_pre_topc(A_15,k3_subset_1(u1_struct_0(A_15),B_17))) = k1_tops_1(A_15,B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1234,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) = k1_tops_1('#skF_2','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1085,c_20])).

tff(c_1238,plain,(
    k1_tops_1('#skF_2','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_108,c_171,c_1234])).

tff(c_32,plain,(
    ! [A_28,B_32,C_34] :
      ( r1_tarski(k1_tops_1(A_28,B_32),k1_tops_1(A_28,C_34))
      | ~ r1_tarski(B_32,C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1258,plain,(
    ! [C_34] :
      ( r1_tarski('#skF_5',k1_tops_1('#skF_2',C_34))
      | ~ r1_tarski('#skF_5',C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1238,c_32])).

tff(c_1604,plain,(
    ! [C_160] :
      ( r1_tarski('#skF_5',k1_tops_1('#skF_2',C_160))
      | ~ r1_tarski('#skF_5',C_160)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_108,c_1258])).

tff(c_1628,plain,
    ( r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_1604])).

tff(c_1641,plain,(
    r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1628])).

tff(c_1643,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_706,c_1641])).

tff(c_1649,plain,(
    ! [D_161] :
      ( ~ r2_hidden('#skF_3',D_161)
      | ~ r1_tarski(D_161,'#skF_4')
      | ~ v3_pre_topc(D_161,'#skF_2')
      | ~ m1_subset_1(D_161,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_1660,plain,
    ( ~ r2_hidden('#skF_3','#skF_5')
    | ~ r1_tarski('#skF_5','#skF_4')
    | ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_108,c_1649])).

tff(c_1675,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_70,c_71,c_1660])).

tff(c_1677,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1687,plain,(
    ~ r1_tarski('#skF_5',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_14,c_1677])).

tff(c_2207,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_2186,c_1687])).

tff(c_2225,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2207])).

tff(c_2226,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_38,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2377,plain,(
    ! [A_242,B_243] :
      ( v3_pre_topc(k1_tops_1(A_242,B_243),A_242)
      | ~ m1_subset_1(B_243,k1_zfmisc_1(u1_struct_0(A_242)))
      | ~ l1_pre_topc(A_242)
      | ~ v2_pre_topc(A_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2385,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_2377])).

tff(c_2390,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_2385])).

tff(c_2237,plain,(
    ! [C_222,B_223,A_224] :
      ( r2_hidden(C_222,B_223)
      | ~ r2_hidden(C_222,A_224)
      | ~ r1_tarski(A_224,B_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2318,plain,(
    ! [A_234,B_235,B_236] :
      ( r2_hidden('#skF_1'(A_234,B_235),B_236)
      | ~ r1_tarski(A_234,B_236)
      | r1_tarski(A_234,B_235) ) ),
    inference(resolution,[status(thm)],[c_6,c_2237])).

tff(c_2641,plain,(
    ! [A_266,B_267,B_268,B_269] :
      ( r2_hidden('#skF_1'(A_266,B_267),B_268)
      | ~ r1_tarski(B_269,B_268)
      | ~ r1_tarski(A_266,B_269)
      | r1_tarski(A_266,B_267) ) ),
    inference(resolution,[status(thm)],[c_2318,c_2])).

tff(c_2713,plain,(
    ! [A_275,B_276] :
      ( r2_hidden('#skF_1'(A_275,B_276),u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_275,'#skF_4')
      | r1_tarski(A_275,B_276) ) ),
    inference(resolution,[status(thm)],[c_68,c_2641])).

tff(c_2736,plain,(
    ! [A_279] :
      ( ~ r1_tarski(A_279,'#skF_4')
      | r1_tarski(A_279,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_2713,c_4])).

tff(c_2227,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_44,plain,(
    ! [D_43] :
      ( ~ r2_hidden('#skF_3',D_43)
      | ~ r1_tarski(D_43,'#skF_4')
      | ~ v3_pre_topc(D_43,'#skF_2')
      | ~ m1_subset_1(D_43,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r2_hidden('#skF_3','#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2402,plain,(
    ! [D_245] :
      ( ~ r2_hidden('#skF_3',D_245)
      | ~ r1_tarski(D_245,'#skF_4')
      | ~ v3_pre_topc(D_245,'#skF_2')
      | ~ m1_subset_1(D_245,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2227,c_44])).

tff(c_2415,plain,(
    ! [A_10] :
      ( ~ r2_hidden('#skF_3',A_10)
      | ~ r1_tarski(A_10,'#skF_4')
      | ~ v3_pre_topc(A_10,'#skF_2')
      | ~ r1_tarski(A_10,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_14,c_2402])).

tff(c_2767,plain,(
    ! [A_280] :
      ( ~ r2_hidden('#skF_3',A_280)
      | ~ v3_pre_topc(A_280,'#skF_2')
      | ~ r1_tarski(A_280,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2736,c_2415])).

tff(c_2774,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_2390,c_2767])).

tff(c_2784,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2340,c_2226,c_2774])).

tff(c_2785,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2960,plain,(
    ! [A_310,B_311] :
      ( v3_pre_topc(k1_tops_1(A_310,B_311),A_310)
      | ~ m1_subset_1(B_311,k1_zfmisc_1(u1_struct_0(A_310)))
      | ~ l1_pre_topc(A_310)
      | ~ v2_pre_topc(A_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2968,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_2960])).

tff(c_2973,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_2968])).

tff(c_2796,plain,(
    ! [C_286,B_287,A_288] :
      ( r2_hidden(C_286,B_287)
      | ~ r2_hidden(C_286,A_288)
      | ~ r1_tarski(A_288,B_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2951,plain,(
    ! [A_307,B_308,B_309] :
      ( r2_hidden('#skF_1'(A_307,B_308),B_309)
      | ~ r1_tarski(A_307,B_309)
      | r1_tarski(A_307,B_308) ) ),
    inference(resolution,[status(thm)],[c_6,c_2796])).

tff(c_3242,plain,(
    ! [A_337,B_338,B_339,B_340] :
      ( r2_hidden('#skF_1'(A_337,B_338),B_339)
      | ~ r1_tarski(B_340,B_339)
      | ~ r1_tarski(A_337,B_340)
      | r1_tarski(A_337,B_338) ) ),
    inference(resolution,[status(thm)],[c_2951,c_2])).

tff(c_3261,plain,(
    ! [A_341,B_342] :
      ( r2_hidden('#skF_1'(A_341,B_342),u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_341,'#skF_4')
      | r1_tarski(A_341,B_342) ) ),
    inference(resolution,[status(thm)],[c_68,c_3242])).

tff(c_3270,plain,(
    ! [A_343] :
      ( ~ r1_tarski(A_343,'#skF_4')
      | r1_tarski(A_343,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_3261,c_4])).

tff(c_2786,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,(
    ! [D_43] :
      ( ~ r2_hidden('#skF_3',D_43)
      | ~ r1_tarski(D_43,'#skF_4')
      | ~ v3_pre_topc(D_43,'#skF_2')
      | ~ m1_subset_1(D_43,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r1_tarski('#skF_5','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_3094,plain,(
    ! [D_330] :
      ( ~ r2_hidden('#skF_3',D_330)
      | ~ r1_tarski(D_330,'#skF_4')
      | ~ v3_pre_topc(D_330,'#skF_2')
      | ~ m1_subset_1(D_330,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2786,c_48])).

tff(c_3114,plain,(
    ! [A_10] :
      ( ~ r2_hidden('#skF_3',A_10)
      | ~ r1_tarski(A_10,'#skF_4')
      | ~ v3_pre_topc(A_10,'#skF_2')
      | ~ r1_tarski(A_10,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_14,c_3094])).

tff(c_3305,plain,(
    ! [A_344] :
      ( ~ r2_hidden('#skF_3',A_344)
      | ~ v3_pre_topc(A_344,'#skF_2')
      | ~ r1_tarski(A_344,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3270,c_3114])).

tff(c_3316,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_2973,c_3305])).

tff(c_3329,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2908,c_2785,c_3316])).

tff(c_3330,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_3475,plain,(
    ! [A_370,B_371] :
      ( v3_pre_topc(k1_tops_1(A_370,B_371),A_370)
      | ~ m1_subset_1(B_371,k1_zfmisc_1(u1_struct_0(A_370)))
      | ~ l1_pre_topc(A_370)
      | ~ v2_pre_topc(A_370) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3483,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_3475])).

tff(c_3488,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_3483])).

tff(c_3343,plain,(
    ! [C_350,B_351,A_352] :
      ( r2_hidden(C_350,B_351)
      | ~ r2_hidden(C_350,A_352)
      | ~ r1_tarski(A_352,B_351) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3424,plain,(
    ! [A_362,B_363,B_364] :
      ( r2_hidden('#skF_1'(A_362,B_363),B_364)
      | ~ r1_tarski(A_362,B_364)
      | r1_tarski(A_362,B_363) ) ),
    inference(resolution,[status(thm)],[c_6,c_3343])).

tff(c_3716,plain,(
    ! [A_392,B_393,B_394,B_395] :
      ( r2_hidden('#skF_1'(A_392,B_393),B_394)
      | ~ r1_tarski(B_395,B_394)
      | ~ r1_tarski(A_392,B_395)
      | r1_tarski(A_392,B_393) ) ),
    inference(resolution,[status(thm)],[c_3424,c_2])).

tff(c_3735,plain,(
    ! [A_396,B_397] :
      ( r2_hidden('#skF_1'(A_396,B_397),u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_396,'#skF_4')
      | r1_tarski(A_396,B_397) ) ),
    inference(resolution,[status(thm)],[c_68,c_3716])).

tff(c_3746,plain,(
    ! [A_398] :
      ( ~ r1_tarski(A_398,'#skF_4')
      | r1_tarski(A_398,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_3735,c_4])).

tff(c_3331,plain,(
    ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,(
    ! [D_43] :
      ( ~ r2_hidden('#skF_3',D_43)
      | ~ r1_tarski(D_43,'#skF_4')
      | ~ v3_pre_topc(D_43,'#skF_2')
      | ~ m1_subset_1(D_43,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v3_pre_topc('#skF_5','#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_3500,plain,(
    ! [D_373] :
      ( ~ r2_hidden('#skF_3',D_373)
      | ~ r1_tarski(D_373,'#skF_4')
      | ~ v3_pre_topc(D_373,'#skF_2')
      | ~ m1_subset_1(D_373,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3331,c_52])).

tff(c_3513,plain,(
    ! [A_10] :
      ( ~ r2_hidden('#skF_3',A_10)
      | ~ r1_tarski(A_10,'#skF_4')
      | ~ v3_pre_topc(A_10,'#skF_2')
      | ~ r1_tarski(A_10,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_14,c_3500])).

tff(c_3777,plain,(
    ! [A_399] :
      ( ~ r2_hidden('#skF_3',A_399)
      | ~ v3_pre_topc(A_399,'#skF_2')
      | ~ r1_tarski(A_399,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3746,c_3513])).

tff(c_3784,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_3488,c_3777])).

tff(c_3791,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3447,c_3330,c_3784])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:18:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.11/3.02  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.11/3.04  
% 8.11/3.04  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.11/3.05  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 8.11/3.05  
% 8.11/3.05  %Foreground sorts:
% 8.11/3.05  
% 8.11/3.05  
% 8.11/3.05  %Background operators:
% 8.11/3.05  
% 8.11/3.05  
% 8.11/3.05  %Foreground operators:
% 8.11/3.05  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 8.11/3.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.11/3.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.11/3.05  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.11/3.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.11/3.05  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 8.11/3.05  tff('#skF_5', type, '#skF_5': $i).
% 8.11/3.05  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 8.11/3.05  tff('#skF_2', type, '#skF_2': $i).
% 8.11/3.05  tff('#skF_3', type, '#skF_3': $i).
% 8.11/3.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.11/3.05  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 8.11/3.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.11/3.05  tff('#skF_4', type, '#skF_4': $i).
% 8.11/3.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.11/3.05  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.11/3.05  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.11/3.05  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.11/3.05  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 8.11/3.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.11/3.05  
% 8.11/3.08  tff(f_127, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B, C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k1_tops_1(A, C)) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_tops_1)).
% 8.11/3.08  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 8.11/3.08  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.11/3.08  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.11/3.08  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 8.11/3.08  tff(f_36, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 8.11/3.08  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 8.11/3.08  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 8.11/3.08  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 8.11/3.08  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 8.11/3.08  tff(f_80, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 8.11/3.08  tff(c_36, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.11/3.08  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.11/3.08  tff(c_3434, plain, (![A_365, B_366]: (r1_tarski(k1_tops_1(A_365, B_366), B_366) | ~m1_subset_1(B_366, k1_zfmisc_1(u1_struct_0(A_365))) | ~l1_pre_topc(A_365))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.11/3.08  tff(c_3442, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_3434])).
% 8.11/3.08  tff(c_3447, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_3442])).
% 8.11/3.08  tff(c_2895, plain, (![A_301, B_302]: (r1_tarski(k1_tops_1(A_301, B_302), B_302) | ~m1_subset_1(B_302, k1_zfmisc_1(u1_struct_0(A_301))) | ~l1_pre_topc(A_301))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.11/3.08  tff(c_2903, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_2895])).
% 8.11/3.08  tff(c_2908, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2903])).
% 8.11/3.08  tff(c_2327, plain, (![A_237, B_238]: (r1_tarski(k1_tops_1(A_237, B_238), B_238) | ~m1_subset_1(B_238, k1_zfmisc_1(u1_struct_0(A_237))) | ~l1_pre_topc(A_237))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.11/3.08  tff(c_2335, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_2327])).
% 8.11/3.08  tff(c_2340, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2335])).
% 8.11/3.08  tff(c_50, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | r1_tarski('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.11/3.08  tff(c_70, plain, (r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_50])).
% 8.11/3.08  tff(c_60, plain, (![A_46, B_47]: (r1_tarski(A_46, B_47) | ~m1_subset_1(A_46, k1_zfmisc_1(B_47)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.11/3.08  tff(c_68, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_60])).
% 8.11/3.08  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.11/3.08  tff(c_80, plain, (![C_53, B_54, A_55]: (r2_hidden(C_53, B_54) | ~r2_hidden(C_53, A_55) | ~r1_tarski(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.11/3.08  tff(c_1794, plain, (![A_175, B_176, B_177]: (r2_hidden('#skF_1'(A_175, B_176), B_177) | ~r1_tarski(A_175, B_177) | r1_tarski(A_175, B_176))), inference(resolution, [status(thm)], [c_6, c_80])).
% 8.11/3.08  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.11/3.08  tff(c_2081, plain, (![A_203, B_204, B_205, B_206]: (r2_hidden('#skF_1'(A_203, B_204), B_205) | ~r1_tarski(B_206, B_205) | ~r1_tarski(A_203, B_206) | r1_tarski(A_203, B_204))), inference(resolution, [status(thm)], [c_1794, c_2])).
% 8.11/3.08  tff(c_2177, plain, (![A_214, B_215]: (r2_hidden('#skF_1'(A_214, B_215), u1_struct_0('#skF_2')) | ~r1_tarski(A_214, '#skF_4') | r1_tarski(A_214, B_215))), inference(resolution, [status(thm)], [c_68, c_2081])).
% 8.11/3.08  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.11/3.08  tff(c_2186, plain, (![A_216]: (~r1_tarski(A_216, '#skF_4') | r1_tarski(A_216, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_2177, c_4])).
% 8.11/3.08  tff(c_14, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.11/3.08  tff(c_54, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | v3_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.11/3.08  tff(c_69, plain, (v3_pre_topc('#skF_5', '#skF_2')), inference(splitLeft, [status(thm)], [c_54])).
% 8.11/3.08  tff(c_46, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | r2_hidden('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.11/3.08  tff(c_71, plain, (r2_hidden('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_46])).
% 8.11/3.08  tff(c_58, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.11/3.08  tff(c_108, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_58])).
% 8.11/3.08  tff(c_86, plain, (![B_54]: (r2_hidden('#skF_3', B_54) | ~r1_tarski('#skF_5', B_54))), inference(resolution, [status(thm)], [c_71, c_80])).
% 8.11/3.08  tff(c_40, plain, (![D_43]: (~r2_hidden('#skF_3', D_43) | ~r1_tarski(D_43, '#skF_4') | ~v3_pre_topc(D_43, '#skF_2') | ~m1_subset_1(D_43, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.11/3.08  tff(c_698, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_40])).
% 8.11/3.08  tff(c_706, plain, (~r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_86, c_698])).
% 8.11/3.08  tff(c_161, plain, (![A_67, B_68]: (k3_subset_1(A_67, k3_subset_1(A_67, B_68))=B_68 | ~m1_subset_1(B_68, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.11/3.08  tff(c_171, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_108, c_161])).
% 8.11/3.08  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(k3_subset_1(A_6, B_7), k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.11/3.08  tff(c_437, plain, (![B_95, A_96]: (v4_pre_topc(B_95, A_96) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_96), B_95), A_96) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.11/3.08  tff(c_444, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), '#skF_2') | ~v3_pre_topc('#skF_5', '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_171, c_437])).
% 8.11/3.08  tff(c_449, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_69, c_444])).
% 8.11/3.08  tff(c_1013, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_449])).
% 8.11/3.08  tff(c_1016, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_8, c_1013])).
% 8.11/3.08  tff(c_1023, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_108, c_1016])).
% 8.11/3.08  tff(c_1024, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), '#skF_2')), inference(splitRight, [status(thm)], [c_449])).
% 8.11/3.08  tff(c_1025, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_449])).
% 8.11/3.08  tff(c_18, plain, (![A_12, B_14]: (k2_pre_topc(A_12, B_14)=B_14 | ~v4_pre_topc(B_14, A_12) | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.11/3.08  tff(c_1070, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_5') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_1025, c_18])).
% 8.11/3.08  tff(c_1085, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1024, c_1070])).
% 8.11/3.08  tff(c_20, plain, (![A_15, B_17]: (k3_subset_1(u1_struct_0(A_15), k2_pre_topc(A_15, k3_subset_1(u1_struct_0(A_15), B_17)))=k1_tops_1(A_15, B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.11/3.08  tff(c_1234, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'))=k1_tops_1('#skF_2', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1085, c_20])).
% 8.11/3.08  tff(c_1238, plain, (k1_tops_1('#skF_2', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_108, c_171, c_1234])).
% 8.11/3.08  tff(c_32, plain, (![A_28, B_32, C_34]: (r1_tarski(k1_tops_1(A_28, B_32), k1_tops_1(A_28, C_34)) | ~r1_tarski(B_32, C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(u1_struct_0(A_28))) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.11/3.08  tff(c_1258, plain, (![C_34]: (r1_tarski('#skF_5', k1_tops_1('#skF_2', C_34)) | ~r1_tarski('#skF_5', C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1238, c_32])).
% 8.11/3.08  tff(c_1604, plain, (![C_160]: (r1_tarski('#skF_5', k1_tops_1('#skF_2', C_160)) | ~r1_tarski('#skF_5', C_160) | ~m1_subset_1(C_160, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_108, c_1258])).
% 8.11/3.08  tff(c_1628, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_1604])).
% 8.11/3.08  tff(c_1641, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1628])).
% 8.11/3.08  tff(c_1643, plain, $false, inference(negUnitSimplification, [status(thm)], [c_706, c_1641])).
% 8.11/3.08  tff(c_1649, plain, (![D_161]: (~r2_hidden('#skF_3', D_161) | ~r1_tarski(D_161, '#skF_4') | ~v3_pre_topc(D_161, '#skF_2') | ~m1_subset_1(D_161, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_40])).
% 8.11/3.08  tff(c_1660, plain, (~r2_hidden('#skF_3', '#skF_5') | ~r1_tarski('#skF_5', '#skF_4') | ~v3_pre_topc('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_108, c_1649])).
% 8.11/3.08  tff(c_1675, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69, c_70, c_71, c_1660])).
% 8.11/3.08  tff(c_1677, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_58])).
% 8.11/3.08  tff(c_1687, plain, (~r1_tarski('#skF_5', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_14, c_1677])).
% 8.11/3.08  tff(c_2207, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_2186, c_1687])).
% 8.11/3.08  tff(c_2225, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_2207])).
% 8.11/3.08  tff(c_2226, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_46])).
% 8.11/3.08  tff(c_38, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.11/3.08  tff(c_2377, plain, (![A_242, B_243]: (v3_pre_topc(k1_tops_1(A_242, B_243), A_242) | ~m1_subset_1(B_243, k1_zfmisc_1(u1_struct_0(A_242))) | ~l1_pre_topc(A_242) | ~v2_pre_topc(A_242))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.11/3.08  tff(c_2385, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_2377])).
% 8.11/3.08  tff(c_2390, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_2385])).
% 8.11/3.08  tff(c_2237, plain, (![C_222, B_223, A_224]: (r2_hidden(C_222, B_223) | ~r2_hidden(C_222, A_224) | ~r1_tarski(A_224, B_223))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.11/3.08  tff(c_2318, plain, (![A_234, B_235, B_236]: (r2_hidden('#skF_1'(A_234, B_235), B_236) | ~r1_tarski(A_234, B_236) | r1_tarski(A_234, B_235))), inference(resolution, [status(thm)], [c_6, c_2237])).
% 8.11/3.08  tff(c_2641, plain, (![A_266, B_267, B_268, B_269]: (r2_hidden('#skF_1'(A_266, B_267), B_268) | ~r1_tarski(B_269, B_268) | ~r1_tarski(A_266, B_269) | r1_tarski(A_266, B_267))), inference(resolution, [status(thm)], [c_2318, c_2])).
% 8.11/3.08  tff(c_2713, plain, (![A_275, B_276]: (r2_hidden('#skF_1'(A_275, B_276), u1_struct_0('#skF_2')) | ~r1_tarski(A_275, '#skF_4') | r1_tarski(A_275, B_276))), inference(resolution, [status(thm)], [c_68, c_2641])).
% 8.11/3.08  tff(c_2736, plain, (![A_279]: (~r1_tarski(A_279, '#skF_4') | r1_tarski(A_279, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_2713, c_4])).
% 8.11/3.08  tff(c_2227, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_46])).
% 8.11/3.08  tff(c_44, plain, (![D_43]: (~r2_hidden('#skF_3', D_43) | ~r1_tarski(D_43, '#skF_4') | ~v3_pre_topc(D_43, '#skF_2') | ~m1_subset_1(D_43, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r2_hidden('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.11/3.08  tff(c_2402, plain, (![D_245]: (~r2_hidden('#skF_3', D_245) | ~r1_tarski(D_245, '#skF_4') | ~v3_pre_topc(D_245, '#skF_2') | ~m1_subset_1(D_245, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_2227, c_44])).
% 8.11/3.08  tff(c_2415, plain, (![A_10]: (~r2_hidden('#skF_3', A_10) | ~r1_tarski(A_10, '#skF_4') | ~v3_pre_topc(A_10, '#skF_2') | ~r1_tarski(A_10, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_14, c_2402])).
% 8.11/3.08  tff(c_2767, plain, (![A_280]: (~r2_hidden('#skF_3', A_280) | ~v3_pre_topc(A_280, '#skF_2') | ~r1_tarski(A_280, '#skF_4'))), inference(resolution, [status(thm)], [c_2736, c_2415])).
% 8.11/3.08  tff(c_2774, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_2390, c_2767])).
% 8.11/3.08  tff(c_2784, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2340, c_2226, c_2774])).
% 8.11/3.08  tff(c_2785, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_50])).
% 8.11/3.08  tff(c_2960, plain, (![A_310, B_311]: (v3_pre_topc(k1_tops_1(A_310, B_311), A_310) | ~m1_subset_1(B_311, k1_zfmisc_1(u1_struct_0(A_310))) | ~l1_pre_topc(A_310) | ~v2_pre_topc(A_310))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.11/3.08  tff(c_2968, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_2960])).
% 8.11/3.08  tff(c_2973, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_2968])).
% 8.11/3.08  tff(c_2796, plain, (![C_286, B_287, A_288]: (r2_hidden(C_286, B_287) | ~r2_hidden(C_286, A_288) | ~r1_tarski(A_288, B_287))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.11/3.08  tff(c_2951, plain, (![A_307, B_308, B_309]: (r2_hidden('#skF_1'(A_307, B_308), B_309) | ~r1_tarski(A_307, B_309) | r1_tarski(A_307, B_308))), inference(resolution, [status(thm)], [c_6, c_2796])).
% 8.11/3.08  tff(c_3242, plain, (![A_337, B_338, B_339, B_340]: (r2_hidden('#skF_1'(A_337, B_338), B_339) | ~r1_tarski(B_340, B_339) | ~r1_tarski(A_337, B_340) | r1_tarski(A_337, B_338))), inference(resolution, [status(thm)], [c_2951, c_2])).
% 8.11/3.08  tff(c_3261, plain, (![A_341, B_342]: (r2_hidden('#skF_1'(A_341, B_342), u1_struct_0('#skF_2')) | ~r1_tarski(A_341, '#skF_4') | r1_tarski(A_341, B_342))), inference(resolution, [status(thm)], [c_68, c_3242])).
% 8.11/3.08  tff(c_3270, plain, (![A_343]: (~r1_tarski(A_343, '#skF_4') | r1_tarski(A_343, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_3261, c_4])).
% 8.11/3.08  tff(c_2786, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_50])).
% 8.11/3.08  tff(c_48, plain, (![D_43]: (~r2_hidden('#skF_3', D_43) | ~r1_tarski(D_43, '#skF_4') | ~v3_pre_topc(D_43, '#skF_2') | ~m1_subset_1(D_43, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r1_tarski('#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.11/3.08  tff(c_3094, plain, (![D_330]: (~r2_hidden('#skF_3', D_330) | ~r1_tarski(D_330, '#skF_4') | ~v3_pre_topc(D_330, '#skF_2') | ~m1_subset_1(D_330, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_2786, c_48])).
% 8.11/3.08  tff(c_3114, plain, (![A_10]: (~r2_hidden('#skF_3', A_10) | ~r1_tarski(A_10, '#skF_4') | ~v3_pre_topc(A_10, '#skF_2') | ~r1_tarski(A_10, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_14, c_3094])).
% 8.11/3.08  tff(c_3305, plain, (![A_344]: (~r2_hidden('#skF_3', A_344) | ~v3_pre_topc(A_344, '#skF_2') | ~r1_tarski(A_344, '#skF_4'))), inference(resolution, [status(thm)], [c_3270, c_3114])).
% 8.11/3.08  tff(c_3316, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_2973, c_3305])).
% 8.11/3.08  tff(c_3329, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2908, c_2785, c_3316])).
% 8.11/3.08  tff(c_3330, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_54])).
% 8.11/3.08  tff(c_3475, plain, (![A_370, B_371]: (v3_pre_topc(k1_tops_1(A_370, B_371), A_370) | ~m1_subset_1(B_371, k1_zfmisc_1(u1_struct_0(A_370))) | ~l1_pre_topc(A_370) | ~v2_pre_topc(A_370))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.11/3.08  tff(c_3483, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_3475])).
% 8.11/3.08  tff(c_3488, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_3483])).
% 8.11/3.08  tff(c_3343, plain, (![C_350, B_351, A_352]: (r2_hidden(C_350, B_351) | ~r2_hidden(C_350, A_352) | ~r1_tarski(A_352, B_351))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.11/3.08  tff(c_3424, plain, (![A_362, B_363, B_364]: (r2_hidden('#skF_1'(A_362, B_363), B_364) | ~r1_tarski(A_362, B_364) | r1_tarski(A_362, B_363))), inference(resolution, [status(thm)], [c_6, c_3343])).
% 8.11/3.08  tff(c_3716, plain, (![A_392, B_393, B_394, B_395]: (r2_hidden('#skF_1'(A_392, B_393), B_394) | ~r1_tarski(B_395, B_394) | ~r1_tarski(A_392, B_395) | r1_tarski(A_392, B_393))), inference(resolution, [status(thm)], [c_3424, c_2])).
% 8.11/3.08  tff(c_3735, plain, (![A_396, B_397]: (r2_hidden('#skF_1'(A_396, B_397), u1_struct_0('#skF_2')) | ~r1_tarski(A_396, '#skF_4') | r1_tarski(A_396, B_397))), inference(resolution, [status(thm)], [c_68, c_3716])).
% 8.11/3.08  tff(c_3746, plain, (![A_398]: (~r1_tarski(A_398, '#skF_4') | r1_tarski(A_398, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_3735, c_4])).
% 8.11/3.08  tff(c_3331, plain, (~v3_pre_topc('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_54])).
% 8.11/3.08  tff(c_52, plain, (![D_43]: (~r2_hidden('#skF_3', D_43) | ~r1_tarski(D_43, '#skF_4') | ~v3_pre_topc(D_43, '#skF_2') | ~m1_subset_1(D_43, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v3_pre_topc('#skF_5', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.11/3.08  tff(c_3500, plain, (![D_373]: (~r2_hidden('#skF_3', D_373) | ~r1_tarski(D_373, '#skF_4') | ~v3_pre_topc(D_373, '#skF_2') | ~m1_subset_1(D_373, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_3331, c_52])).
% 8.11/3.08  tff(c_3513, plain, (![A_10]: (~r2_hidden('#skF_3', A_10) | ~r1_tarski(A_10, '#skF_4') | ~v3_pre_topc(A_10, '#skF_2') | ~r1_tarski(A_10, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_14, c_3500])).
% 8.11/3.08  tff(c_3777, plain, (![A_399]: (~r2_hidden('#skF_3', A_399) | ~v3_pre_topc(A_399, '#skF_2') | ~r1_tarski(A_399, '#skF_4'))), inference(resolution, [status(thm)], [c_3746, c_3513])).
% 8.11/3.08  tff(c_3784, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_3488, c_3777])).
% 8.11/3.08  tff(c_3791, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3447, c_3330, c_3784])).
% 8.11/3.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.11/3.08  
% 8.11/3.08  Inference rules
% 8.11/3.08  ----------------------
% 8.11/3.08  #Ref     : 0
% 8.11/3.08  #Sup     : 812
% 8.11/3.08  #Fact    : 0
% 8.11/3.09  #Define  : 0
% 8.11/3.09  #Split   : 22
% 8.11/3.09  #Chain   : 0
% 8.11/3.09  #Close   : 0
% 8.11/3.09  
% 8.11/3.09  Ordering : KBO
% 8.11/3.09  
% 8.11/3.09  Simplification rules
% 8.11/3.09  ----------------------
% 8.11/3.09  #Subsume      : 104
% 8.11/3.09  #Demod        : 429
% 8.11/3.09  #Tautology    : 298
% 8.11/3.09  #SimpNegUnit  : 13
% 8.11/3.09  #BackRed      : 8
% 8.11/3.09  
% 8.11/3.09  #Partial instantiations: 0
% 8.11/3.09  #Strategies tried      : 1
% 8.11/3.09  
% 8.11/3.09  Timing (in seconds)
% 8.11/3.09  ----------------------
% 8.11/3.09  Preprocessing        : 0.52
% 8.11/3.09  Parsing              : 0.28
% 8.11/3.09  CNF conversion       : 0.04
% 8.11/3.09  Main loop            : 1.58
% 8.11/3.09  Inferencing          : 0.59
% 8.11/3.09  Reduction            : 0.47
% 8.11/3.09  Demodulation         : 0.33
% 8.11/3.09  BG Simplification    : 0.06
% 8.11/3.09  Subsumption          : 0.33
% 8.11/3.09  Abstraction          : 0.06
% 8.11/3.09  MUC search           : 0.00
% 8.11/3.09  Cooper               : 0.00
% 8.11/3.09  Total                : 2.19
% 8.11/3.09  Index Insertion      : 0.00
% 8.11/3.09  Index Deletion       : 0.00
% 8.11/3.09  Index Matching       : 0.00
% 8.11/3.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
