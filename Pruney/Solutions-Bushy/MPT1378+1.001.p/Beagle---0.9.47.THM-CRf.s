%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1378+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:52 EST 2020

% Result     : Theorem 26.72s
% Output     : CNFRefutation 26.72s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 544 expanded)
%              Number of leaves         :   34 ( 204 expanded)
%              Depth                    :   21
%              Number of atoms          :  308 (1783 expanded)
%              Number of equality atoms :   33 ( 171 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k4_subset_1 > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
    ~ ! [A] :
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
                     => m1_connsp_2(k4_subset_1(u1_struct_0(A),C,D),A,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_connsp_2)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
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

tff(f_58,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_26,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => r1_tarski(k4_subset_1(u1_struct_0(A),k1_tops_1(A,B),k1_tops_1(A,C)),k1_tops_1(A,k4_subset_1(u1_struct_0(A),B,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tops_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_94,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(A_54,B_55)
      | ~ m1_subset_1(A_54,k1_zfmisc_1(B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_102,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_50,c_94])).

tff(c_58,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_56,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_46,plain,(
    m1_connsp_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_36,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(A_26,k1_zfmisc_1(B_27))
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1790,plain,(
    ! [B_149,A_150,C_151] :
      ( r2_hidden(B_149,k1_tops_1(A_150,C_151))
      | ~ m1_connsp_2(C_151,A_150,B_149)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ m1_subset_1(B_149,u1_struct_0(A_150))
      | ~ l1_pre_topc(A_150)
      | ~ v2_pre_topc(A_150)
      | v2_struct_0(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1871,plain,(
    ! [B_149,A_150,A_26] :
      ( r2_hidden(B_149,k1_tops_1(A_150,A_26))
      | ~ m1_connsp_2(A_26,A_150,B_149)
      | ~ m1_subset_1(B_149,u1_struct_0(A_150))
      | ~ l1_pre_topc(A_150)
      | ~ v2_pre_topc(A_150)
      | v2_struct_0(A_150)
      | ~ r1_tarski(A_26,u1_struct_0(A_150)) ) ),
    inference(resolution,[status(thm)],[c_36,c_1790])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_26,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k1_tops_1(A_16,B_17),k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_214,plain,(
    ! [A_96,B_97,C_98] :
      ( k4_subset_1(A_96,B_97,C_98) = k2_xboole_0(B_97,C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(A_96))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_377,plain,(
    ! [B_117] :
      ( k4_subset_1(u1_struct_0('#skF_3'),B_117,'#skF_5') = k2_xboole_0(B_117,'#skF_5')
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_52,c_214])).

tff(c_391,plain,(
    ! [B_17] :
      ( k4_subset_1(u1_struct_0('#skF_3'),k1_tops_1('#skF_3',B_17),'#skF_5') = k2_xboole_0(k1_tops_1('#skF_3',B_17),'#skF_5')
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_377])).

tff(c_9091,plain,(
    ! [B_380] :
      ( k4_subset_1(u1_struct_0('#skF_3'),k1_tops_1('#skF_3',B_380),'#skF_5') = k2_xboole_0('#skF_5',k1_tops_1('#skF_3',B_380))
      | ~ m1_subset_1(B_380,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2,c_391])).

tff(c_9153,plain,(
    k4_subset_1(u1_struct_0('#skF_3'),k1_tops_1('#skF_3','#skF_5'),'#skF_5') = k2_xboole_0('#skF_5',k1_tops_1('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_52,c_9091])).

tff(c_293,plain,(
    ! [A_114,B_115,C_116] :
      ( m1_subset_1(k4_subset_1(A_114,B_115,C_116),k1_zfmisc_1(A_114))
      | ~ m1_subset_1(C_116,k1_zfmisc_1(A_114))
      | ~ m1_subset_1(B_115,k1_zfmisc_1(A_114)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_34,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,B_27)
      | ~ m1_subset_1(A_26,k1_zfmisc_1(B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_318,plain,(
    ! [A_114,B_115,C_116] :
      ( r1_tarski(k4_subset_1(A_114,B_115,C_116),A_114)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(A_114))
      | ~ m1_subset_1(B_115,k1_zfmisc_1(A_114)) ) ),
    inference(resolution,[status(thm)],[c_293,c_34])).

tff(c_9167,plain,
    ( r1_tarski(k2_xboole_0('#skF_5',k1_tops_1('#skF_3','#skF_5')),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1(k1_tops_1('#skF_3','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_9153,c_318])).

tff(c_9180,plain,
    ( r1_tarski(k2_xboole_0('#skF_5',k1_tops_1('#skF_3','#skF_5')),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k1_tops_1('#skF_3','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_9167])).

tff(c_9213,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_3','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_9180])).

tff(c_9216,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_9213])).

tff(c_9223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_9216])).

tff(c_9225,plain,(
    m1_subset_1(k1_tops_1('#skF_3','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_9180])).

tff(c_9271,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_9225,c_34])).

tff(c_9154,plain,(
    k4_subset_1(u1_struct_0('#skF_3'),k1_tops_1('#skF_3','#skF_6'),'#skF_5') = k2_xboole_0('#skF_5',k1_tops_1('#skF_3','#skF_6')) ),
    inference(resolution,[status(thm)],[c_50,c_9091])).

tff(c_9196,plain,
    ( r1_tarski(k2_xboole_0('#skF_5',k1_tops_1('#skF_3','#skF_6')),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1(k1_tops_1('#skF_3','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_9154,c_318])).

tff(c_9209,plain,
    ( r1_tarski(k2_xboole_0('#skF_5',k1_tops_1('#skF_3','#skF_6')),u1_struct_0('#skF_3'))
    | ~ m1_subset_1(k1_tops_1('#skF_3','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_9196])).

tff(c_11267,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_3','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_9209])).

tff(c_11270,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_11267])).

tff(c_11277,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_50,c_11270])).

tff(c_11279,plain,(
    m1_subset_1(k1_tops_1('#skF_3','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_9209])).

tff(c_224,plain,(
    ! [B_27,B_97,A_26] :
      ( k4_subset_1(B_27,B_97,A_26) = k2_xboole_0(B_97,A_26)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(B_27))
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(resolution,[status(thm)],[c_36,c_214])).

tff(c_22269,plain,(
    ! [A_498] :
      ( k4_subset_1(u1_struct_0('#skF_3'),k1_tops_1('#skF_3','#skF_6'),A_498) = k2_xboole_0(k1_tops_1('#skF_3','#skF_6'),A_498)
      | ~ r1_tarski(A_498,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_11279,c_224])).

tff(c_413,plain,(
    k4_subset_1(u1_struct_0('#skF_3'),'#skF_6','#skF_5') = k2_xboole_0('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_377])).

tff(c_2453,plain,(
    ! [A_169,B_170,C_171] :
      ( r1_tarski(k4_subset_1(u1_struct_0(A_169),k1_tops_1(A_169,B_170),k1_tops_1(A_169,C_171)),k1_tops_1(A_169,k4_subset_1(u1_struct_0(A_169),B_170,C_171)))
      | ~ m1_subset_1(C_171,k1_zfmisc_1(u1_struct_0(A_169)))
      | ~ m1_subset_1(B_170,k1_zfmisc_1(u1_struct_0(A_169)))
      | ~ l1_pre_topc(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2499,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0('#skF_3'),k1_tops_1('#skF_3','#skF_6'),k1_tops_1('#skF_3','#skF_5')),k1_tops_1('#skF_3',k2_xboole_0('#skF_6','#skF_5')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_413,c_2453])).

tff(c_2538,plain,(
    r1_tarski(k4_subset_1(u1_struct_0('#skF_3'),k1_tops_1('#skF_3','#skF_6'),k1_tops_1('#skF_3','#skF_5')),k1_tops_1('#skF_3',k2_xboole_0('#skF_6','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_50,c_52,c_2499])).

tff(c_22307,plain,
    ( r1_tarski(k2_xboole_0(k1_tops_1('#skF_3','#skF_6'),k1_tops_1('#skF_3','#skF_5')),k1_tops_1('#skF_3',k2_xboole_0('#skF_6','#skF_5')))
    | ~ r1_tarski(k1_tops_1('#skF_3','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_22269,c_2538])).

tff(c_22362,plain,(
    r1_tarski(k2_xboole_0(k1_tops_1('#skF_3','#skF_6'),k1_tops_1('#skF_3','#skF_5')),k1_tops_1('#skF_3',k2_xboole_0('#skF_6','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9271,c_22307])).

tff(c_12,plain,(
    ! [D_15,A_10,B_11] :
      ( ~ r2_hidden(D_15,A_10)
      | r2_hidden(D_15,k2_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_144,plain,(
    ! [A_72,C_73,B_74] :
      ( m1_subset_1(A_72,C_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(C_73))
      | ~ r2_hidden(A_72,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_176,plain,(
    ! [A_80,B_81,A_82] :
      ( m1_subset_1(A_80,B_81)
      | ~ r2_hidden(A_80,A_82)
      | ~ r1_tarski(A_82,B_81) ) ),
    inference(resolution,[status(thm)],[c_36,c_144])).

tff(c_183,plain,(
    ! [D_15,B_81,A_10,B_11] :
      ( m1_subset_1(D_15,B_81)
      | ~ r1_tarski(k2_xboole_0(A_10,B_11),B_81)
      | ~ r2_hidden(D_15,A_10) ) ),
    inference(resolution,[status(thm)],[c_12,c_176])).

tff(c_22520,plain,(
    ! [D_15] :
      ( m1_subset_1(D_15,k1_tops_1('#skF_3',k2_xboole_0('#skF_6','#skF_5')))
      | ~ r2_hidden(D_15,k1_tops_1('#skF_3','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_22362,c_183])).

tff(c_252,plain,(
    ! [B_106] :
      ( k4_subset_1(u1_struct_0('#skF_3'),B_106,'#skF_6') = k2_xboole_0(B_106,'#skF_6')
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_50,c_214])).

tff(c_263,plain,(
    k4_subset_1(u1_struct_0('#skF_3'),'#skF_5','#skF_6') = k2_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_252])).

tff(c_272,plain,(
    k4_subset_1(u1_struct_0('#skF_3'),'#skF_5','#skF_6') = k2_xboole_0('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_263])).

tff(c_312,plain,
    ( m1_subset_1(k2_xboole_0('#skF_6','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_293])).

tff(c_322,plain,(
    m1_subset_1(k2_xboole_0('#skF_6','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_312])).

tff(c_32,plain,(
    ! [A_24,B_25] :
      ( r2_hidden(A_24,B_25)
      | v1_xboole_0(B_25)
      | ~ m1_subset_1(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2123,plain,(
    ! [C_160,A_161,B_162] :
      ( m1_connsp_2(C_160,A_161,B_162)
      | ~ r2_hidden(B_162,k1_tops_1(A_161,C_160))
      | ~ m1_subset_1(C_160,k1_zfmisc_1(u1_struct_0(A_161)))
      | ~ m1_subset_1(B_162,u1_struct_0(A_161))
      | ~ l1_pre_topc(A_161)
      | ~ v2_pre_topc(A_161)
      | v2_struct_0(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_11405,plain,(
    ! [C_415,A_416,A_417] :
      ( m1_connsp_2(C_415,A_416,A_417)
      | ~ m1_subset_1(C_415,k1_zfmisc_1(u1_struct_0(A_416)))
      | ~ m1_subset_1(A_417,u1_struct_0(A_416))
      | ~ l1_pre_topc(A_416)
      | ~ v2_pre_topc(A_416)
      | v2_struct_0(A_416)
      | v1_xboole_0(k1_tops_1(A_416,C_415))
      | ~ m1_subset_1(A_417,k1_tops_1(A_416,C_415)) ) ),
    inference(resolution,[status(thm)],[c_32,c_2123])).

tff(c_11433,plain,(
    ! [A_417] :
      ( m1_connsp_2(k2_xboole_0('#skF_6','#skF_5'),'#skF_3',A_417)
      | ~ m1_subset_1(A_417,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | v1_xboole_0(k1_tops_1('#skF_3',k2_xboole_0('#skF_6','#skF_5')))
      | ~ m1_subset_1(A_417,k1_tops_1('#skF_3',k2_xboole_0('#skF_6','#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_322,c_11405])).

tff(c_11490,plain,(
    ! [A_417] :
      ( m1_connsp_2(k2_xboole_0('#skF_6','#skF_5'),'#skF_3',A_417)
      | ~ m1_subset_1(A_417,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | v1_xboole_0(k1_tops_1('#skF_3',k2_xboole_0('#skF_6','#skF_5')))
      | ~ m1_subset_1(A_417,k1_tops_1('#skF_3',k2_xboole_0('#skF_6','#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_11433])).

tff(c_11491,plain,(
    ! [A_417] :
      ( m1_connsp_2(k2_xboole_0('#skF_6','#skF_5'),'#skF_3',A_417)
      | ~ m1_subset_1(A_417,u1_struct_0('#skF_3'))
      | v1_xboole_0(k1_tops_1('#skF_3',k2_xboole_0('#skF_6','#skF_5')))
      | ~ m1_subset_1(A_417,k1_tops_1('#skF_3',k2_xboole_0('#skF_6','#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_11490])).

tff(c_21537,plain,(
    v1_xboole_0(k1_tops_1('#skF_3',k2_xboole_0('#skF_6','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_11491])).

tff(c_21655,plain,(
    ! [A_491] :
      ( k4_subset_1(u1_struct_0('#skF_3'),k1_tops_1('#skF_3','#skF_6'),A_491) = k2_xboole_0(k1_tops_1('#skF_3','#skF_6'),A_491)
      | ~ r1_tarski(A_491,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_11279,c_224])).

tff(c_21693,plain,
    ( r1_tarski(k2_xboole_0(k1_tops_1('#skF_3','#skF_6'),k1_tops_1('#skF_3','#skF_5')),k1_tops_1('#skF_3',k2_xboole_0('#skF_6','#skF_5')))
    | ~ r1_tarski(k1_tops_1('#skF_3','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_21655,c_2538])).

tff(c_21748,plain,(
    r1_tarski(k2_xboole_0(k1_tops_1('#skF_3','#skF_6'),k1_tops_1('#skF_3','#skF_5')),k1_tops_1('#skF_3',k2_xboole_0('#skF_6','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9271,c_21693])).

tff(c_123,plain,(
    ! [C_66,B_67,A_68] :
      ( ~ v1_xboole_0(C_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(C_66))
      | ~ r2_hidden(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_134,plain,(
    ! [B_69,A_70,A_71] :
      ( ~ v1_xboole_0(B_69)
      | ~ r2_hidden(A_70,A_71)
      | ~ r1_tarski(A_71,B_69) ) ),
    inference(resolution,[status(thm)],[c_36,c_123])).

tff(c_141,plain,(
    ! [B_69,A_10,B_11,D_15] :
      ( ~ v1_xboole_0(B_69)
      | ~ r1_tarski(k2_xboole_0(A_10,B_11),B_69)
      | ~ r2_hidden(D_15,A_10) ) ),
    inference(resolution,[status(thm)],[c_12,c_134])).

tff(c_21889,plain,(
    ! [D_15] :
      ( ~ v1_xboole_0(k1_tops_1('#skF_3',k2_xboole_0('#skF_6','#skF_5')))
      | ~ r2_hidden(D_15,k1_tops_1('#skF_3','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_21748,c_141])).

tff(c_21925,plain,(
    ! [D_496] : ~ r2_hidden(D_496,k1_tops_1('#skF_3','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21537,c_21889])).

tff(c_22001,plain,(
    ! [B_149] :
      ( ~ m1_connsp_2('#skF_6','#skF_3',B_149)
      | ~ m1_subset_1(B_149,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski('#skF_6',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1871,c_21925])).

tff(c_22080,plain,(
    ! [B_149] :
      ( ~ m1_connsp_2('#skF_6','#skF_3',B_149)
      | ~ m1_subset_1(B_149,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_58,c_56,c_22001])).

tff(c_22100,plain,(
    ! [B_497] :
      ( ~ m1_connsp_2('#skF_6','#skF_3',B_497)
      | ~ m1_subset_1(B_497,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_22080])).

tff(c_22135,plain,(
    ~ m1_connsp_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_22100])).

tff(c_22149,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_22135])).

tff(c_22151,plain,(
    ~ v1_xboole_0(k1_tops_1('#skF_3',k2_xboole_0('#skF_6','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_11491])).

tff(c_951,plain,(
    ! [A_136,B_137,C_138] :
      ( r2_hidden('#skF_1'(A_136,B_137,C_138),B_137)
      | r2_hidden('#skF_1'(A_136,B_137,C_138),A_136)
      | r2_hidden('#skF_2'(A_136,B_137,C_138),C_138)
      | k2_xboole_0(A_136,B_137) = C_138 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_22,plain,(
    ! [A_10,B_11,C_12] :
      ( ~ r2_hidden('#skF_1'(A_10,B_11,C_12),C_12)
      | r2_hidden('#skF_2'(A_10,B_11,C_12),C_12)
      | k2_xboole_0(A_10,B_11) = C_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4319,plain,(
    ! [A_239,B_240] :
      ( r2_hidden('#skF_1'(A_239,B_240,B_240),A_239)
      | r2_hidden('#skF_2'(A_239,B_240,B_240),B_240)
      | k2_xboole_0(A_239,B_240) = B_240 ) ),
    inference(resolution,[status(thm)],[c_951,c_22])).

tff(c_1577,plain,(
    ! [A_146,B_147,C_148] :
      ( r2_hidden('#skF_1'(A_146,B_147,C_148),B_147)
      | r2_hidden('#skF_1'(A_146,B_147,C_148),A_146)
      | ~ r2_hidden('#skF_2'(A_146,B_147,C_148),B_147)
      | k2_xboole_0(A_146,B_147) = C_148 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] :
      ( ~ r2_hidden('#skF_1'(A_10,B_11,C_12),C_12)
      | ~ r2_hidden('#skF_2'(A_10,B_11,C_12),B_11)
      | k2_xboole_0(A_10,B_11) = C_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1699,plain,(
    ! [A_146,B_147] :
      ( r2_hidden('#skF_1'(A_146,B_147,B_147),A_146)
      | ~ r2_hidden('#skF_2'(A_146,B_147,B_147),B_147)
      | k2_xboole_0(A_146,B_147) = B_147 ) ),
    inference(resolution,[status(thm)],[c_1577,c_14])).

tff(c_4416,plain,(
    ! [A_239,B_240] :
      ( r2_hidden('#skF_1'(A_239,B_240,B_240),A_239)
      | k2_xboole_0(A_239,B_240) = B_240 ) ),
    inference(resolution,[status(thm)],[c_4319,c_1699])).

tff(c_489,plain,(
    ! [A_118,B_119,C_120] :
      ( ~ r2_hidden('#skF_1'(A_118,B_119,C_120),C_120)
      | r2_hidden('#skF_2'(A_118,B_119,C_120),C_120)
      | k2_xboole_0(A_118,B_119) = C_120 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_9416,plain,(
    ! [A_381,B_382,A_383,B_384] :
      ( r2_hidden('#skF_2'(A_381,B_382,k2_xboole_0(A_383,B_384)),k2_xboole_0(A_383,B_384))
      | k2_xboole_0(A_383,B_384) = k2_xboole_0(A_381,B_382)
      | ~ r2_hidden('#skF_1'(A_381,B_382,k2_xboole_0(A_383,B_384)),A_383) ) ),
    inference(resolution,[status(thm)],[c_12,c_489])).

tff(c_756,plain,(
    ! [A_130,B_131,C_132] :
      ( ~ r2_hidden('#skF_1'(A_130,B_131,C_132),C_132)
      | ~ r2_hidden('#skF_2'(A_130,B_131,C_132),B_131)
      | k2_xboole_0(A_130,B_131) = C_132 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_766,plain,(
    ! [A_130,B_131,A_10,B_11] :
      ( ~ r2_hidden('#skF_2'(A_130,B_131,k2_xboole_0(A_10,B_11)),B_131)
      | k2_xboole_0(A_130,B_131) = k2_xboole_0(A_10,B_11)
      | ~ r2_hidden('#skF_1'(A_130,B_131,k2_xboole_0(A_10,B_11)),A_10) ) ),
    inference(resolution,[status(thm)],[c_12,c_756])).

tff(c_29234,plain,(
    ! [A_566,A_567,B_568] :
      ( k2_xboole_0(A_566,k2_xboole_0(A_567,B_568)) = k2_xboole_0(A_567,B_568)
      | ~ r2_hidden('#skF_1'(A_566,k2_xboole_0(A_567,B_568),k2_xboole_0(A_567,B_568)),A_567) ) ),
    inference(resolution,[status(thm)],[c_9416,c_766])).

tff(c_29705,plain,(
    ! [A_239,B_568] : k2_xboole_0(A_239,k2_xboole_0(A_239,B_568)) = k2_xboole_0(A_239,B_568) ),
    inference(resolution,[status(thm)],[c_4416,c_29234])).

tff(c_226,plain,(
    ! [B_97] :
      ( k4_subset_1(u1_struct_0('#skF_3'),B_97,'#skF_6') = k2_xboole_0(B_97,'#skF_6')
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_50,c_214])).

tff(c_361,plain,(
    k4_subset_1(u1_struct_0('#skF_3'),k2_xboole_0('#skF_6','#skF_5'),'#skF_6') = k2_xboole_0(k2_xboole_0('#skF_6','#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_322,c_226])).

tff(c_372,plain,(
    k4_subset_1(u1_struct_0('#skF_3'),k2_xboole_0('#skF_6','#skF_5'),'#skF_6') = k2_xboole_0('#skF_6',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_361])).

tff(c_28,plain,(
    ! [A_18,B_19,C_20] :
      ( m1_subset_1(k4_subset_1(A_18,B_19,C_20),k1_zfmisc_1(A_18))
      | ~ m1_subset_1(C_20,k1_zfmisc_1(A_18))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_788,plain,
    ( m1_subset_1(k2_xboole_0('#skF_6',k2_xboole_0('#skF_6','#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1(k2_xboole_0('#skF_6','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_28])).

tff(c_792,plain,(
    m1_subset_1(k2_xboole_0('#skF_6',k2_xboole_0('#skF_6','#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_50,c_788])).

tff(c_11431,plain,(
    ! [A_417] :
      ( m1_connsp_2(k2_xboole_0('#skF_6',k2_xboole_0('#skF_6','#skF_5')),'#skF_3',A_417)
      | ~ m1_subset_1(A_417,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | v1_xboole_0(k1_tops_1('#skF_3',k2_xboole_0('#skF_6',k2_xboole_0('#skF_6','#skF_5'))))
      | ~ m1_subset_1(A_417,k1_tops_1('#skF_3',k2_xboole_0('#skF_6',k2_xboole_0('#skF_6','#skF_5')))) ) ),
    inference(resolution,[status(thm)],[c_792,c_11405])).

tff(c_11486,plain,(
    ! [A_417] :
      ( m1_connsp_2(k2_xboole_0('#skF_6',k2_xboole_0('#skF_6','#skF_5')),'#skF_3',A_417)
      | ~ m1_subset_1(A_417,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | v1_xboole_0(k1_tops_1('#skF_3',k2_xboole_0('#skF_6',k2_xboole_0('#skF_6','#skF_5'))))
      | ~ m1_subset_1(A_417,k1_tops_1('#skF_3',k2_xboole_0('#skF_6',k2_xboole_0('#skF_6','#skF_5')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_11431])).

tff(c_11487,plain,(
    ! [A_417] :
      ( m1_connsp_2(k2_xboole_0('#skF_6',k2_xboole_0('#skF_6','#skF_5')),'#skF_3',A_417)
      | ~ m1_subset_1(A_417,u1_struct_0('#skF_3'))
      | v1_xboole_0(k1_tops_1('#skF_3',k2_xboole_0('#skF_6',k2_xboole_0('#skF_6','#skF_5'))))
      | ~ m1_subset_1(A_417,k1_tops_1('#skF_3',k2_xboole_0('#skF_6',k2_xboole_0('#skF_6','#skF_5')))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_11486])).

tff(c_47838,plain,(
    ! [A_417] :
      ( m1_connsp_2(k2_xboole_0('#skF_6','#skF_5'),'#skF_3',A_417)
      | ~ m1_subset_1(A_417,u1_struct_0('#skF_3'))
      | v1_xboole_0(k1_tops_1('#skF_3',k2_xboole_0('#skF_6','#skF_5')))
      | ~ m1_subset_1(A_417,k1_tops_1('#skF_3',k2_xboole_0('#skF_6','#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29705,c_29705,c_29705,c_11487])).

tff(c_47840,plain,(
    ! [A_669] :
      ( m1_connsp_2(k2_xboole_0('#skF_6','#skF_5'),'#skF_3',A_669)
      | ~ m1_subset_1(A_669,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_669,k1_tops_1('#skF_3',k2_xboole_0('#skF_6','#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22151,c_47838])).

tff(c_60754,plain,(
    ! [D_830] :
      ( m1_connsp_2(k2_xboole_0('#skF_6','#skF_5'),'#skF_3',D_830)
      | ~ m1_subset_1(D_830,u1_struct_0('#skF_3'))
      | ~ r2_hidden(D_830,k1_tops_1('#skF_3','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_22520,c_47840])).

tff(c_44,plain,(
    ~ m1_connsp_2(k4_subset_1(u1_struct_0('#skF_3'),'#skF_5','#skF_6'),'#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_274,plain,(
    ~ m1_connsp_2(k2_xboole_0('#skF_6','#skF_5'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_44])).

tff(c_60760,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_6')) ),
    inference(resolution,[status(thm)],[c_60754,c_274])).

tff(c_60764,plain,(
    ~ r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_60760])).

tff(c_60770,plain,
    ( ~ m1_connsp_2('#skF_6','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1871,c_60764])).

tff(c_60780,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_58,c_56,c_54,c_46,c_60770])).

tff(c_60782,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_60780])).

%------------------------------------------------------------------------------
