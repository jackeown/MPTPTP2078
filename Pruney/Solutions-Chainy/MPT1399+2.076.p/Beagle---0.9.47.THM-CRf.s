%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:29 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 277 expanded)
%              Number of leaves         :   30 ( 102 expanded)
%              Depth                    :   15
%              Number of atoms          :  117 ( 774 expanded)
%              Number of equality atoms :    6 ( 101 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ~ ( ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ( r2_hidden(D,C)
                        <=> ( v3_pre_topc(D,A)
                            & v4_pre_topc(D,A)
                            & r2_hidden(B,D) ) ) )
                    & C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_20,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_39,plain,(
    ! [A_1] : r1_tarski('#skF_3',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2])).

tff(c_28,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_14,plain,(
    ! [A_9] :
      ( v4_pre_topc(k2_struct_0(A_9),A_9)
      | ~ l1_pre_topc(A_9)
      | ~ v2_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_30,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_12,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_48,plain,(
    ! [A_29] :
      ( u1_struct_0(A_29) = k2_struct_0(A_29)
      | ~ l1_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_53,plain,(
    ! [A_30] :
      ( u1_struct_0(A_30) = k2_struct_0(A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(resolution,[status(thm)],[c_12,c_48])).

tff(c_57,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_53])).

tff(c_68,plain,(
    ! [A_34] :
      ( m1_subset_1(k2_struct_0(A_34),k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_71,plain,
    ( m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_68])).

tff(c_86,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_91,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_86])).

tff(c_95,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_91])).

tff(c_97,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_60,plain,(
    m1_subset_1('#skF_2',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_24])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( r2_hidden(A_2,B_3)
      | v1_xboole_0(B_3)
      | ~ m1_subset_1(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [A_11] :
      ( v3_pre_topc(k2_struct_0(A_11),A_11)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_96,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_34,plain,(
    ! [D_23] :
      ( r2_hidden('#skF_2',D_23)
      | ~ r2_hidden(D_23,'#skF_3')
      | ~ m1_subset_1(D_23,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_72,plain,(
    ! [D_23] :
      ( r2_hidden('#skF_2',D_23)
      | ~ r2_hidden(D_23,'#skF_3')
      | ~ m1_subset_1(D_23,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_34])).

tff(c_106,plain,
    ( r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_72])).

tff(c_113,plain,(
    ~ r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_32,plain,(
    ! [D_23] :
      ( r2_hidden(D_23,'#skF_3')
      | ~ r2_hidden('#skF_2',D_23)
      | ~ v4_pre_topc(D_23,'#skF_1')
      | ~ v3_pre_topc(D_23,'#skF_1')
      | ~ m1_subset_1(D_23,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_124,plain,(
    ! [D_44] :
      ( r2_hidden(D_44,'#skF_3')
      | ~ r2_hidden('#skF_2',D_44)
      | ~ v4_pre_topc(D_44,'#skF_1')
      | ~ v3_pre_topc(D_44,'#skF_1')
      | ~ m1_subset_1(D_44,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_32])).

tff(c_127,plain,
    ( r2_hidden(k2_struct_0('#skF_1'),'#skF_3')
    | ~ r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_96,c_124])).

tff(c_130,plain,
    ( ~ r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_127])).

tff(c_131,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_130])).

tff(c_134,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_131])).

tff(c_138,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_134])).

tff(c_139,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ r2_hidden('#skF_2',k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_141,plain,(
    ~ r2_hidden('#skF_2',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_144,plain,
    ( v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_4,c_141])).

tff(c_147,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_144])).

tff(c_16,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(k2_struct_0(A_10))
      | ~ l1_struct_0(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_150,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_147,c_16])).

tff(c_153,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_150])).

tff(c_155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_153])).

tff(c_156,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_164,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_156])).

tff(c_168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_164])).

tff(c_170,plain,(
    r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( ~ r1_tarski(B_5,A_4)
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_177,plain,(
    ~ r1_tarski('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_170,c_6])).

tff(c_181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_177])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:14:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.24  
% 2.16/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.24  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.16/1.24  
% 2.16/1.24  %Foreground sorts:
% 2.16/1.24  
% 2.16/1.24  
% 2.16/1.24  %Background operators:
% 2.16/1.24  
% 2.16/1.24  
% 2.16/1.24  %Foreground operators:
% 2.16/1.24  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.16/1.24  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.16/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.24  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.16/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.16/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.16/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.16/1.24  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.16/1.24  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.16/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.24  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.16/1.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.16/1.24  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.16/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.16/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.16/1.24  
% 2.24/1.26  tff(f_98, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.24/1.26  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.24/1.26  tff(f_56, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.24/1.26  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.24/1.26  tff(f_42, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.24/1.26  tff(f_46, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 2.24/1.26  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.24/1.26  tff(f_70, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 2.24/1.26  tff(f_64, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 2.24/1.26  tff(f_38, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.24/1.26  tff(c_20, plain, (k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.24/1.26  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.24/1.26  tff(c_39, plain, (![A_1]: (r1_tarski('#skF_3', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2])).
% 2.24/1.26  tff(c_28, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.24/1.26  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.24/1.26  tff(c_14, plain, (![A_9]: (v4_pre_topc(k2_struct_0(A_9), A_9) | ~l1_pre_topc(A_9) | ~v2_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.24/1.26  tff(c_30, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.24/1.26  tff(c_12, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.24/1.26  tff(c_48, plain, (![A_29]: (u1_struct_0(A_29)=k2_struct_0(A_29) | ~l1_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.24/1.26  tff(c_53, plain, (![A_30]: (u1_struct_0(A_30)=k2_struct_0(A_30) | ~l1_pre_topc(A_30))), inference(resolution, [status(thm)], [c_12, c_48])).
% 2.24/1.26  tff(c_57, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_53])).
% 2.24/1.26  tff(c_68, plain, (![A_34]: (m1_subset_1(k2_struct_0(A_34), k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.24/1.26  tff(c_71, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_57, c_68])).
% 2.24/1.26  tff(c_86, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_71])).
% 2.24/1.26  tff(c_91, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_86])).
% 2.24/1.26  tff(c_95, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_91])).
% 2.24/1.26  tff(c_97, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_71])).
% 2.24/1.26  tff(c_24, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.24/1.26  tff(c_60, plain, (m1_subset_1('#skF_2', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_24])).
% 2.24/1.26  tff(c_4, plain, (![A_2, B_3]: (r2_hidden(A_2, B_3) | v1_xboole_0(B_3) | ~m1_subset_1(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.24/1.26  tff(c_18, plain, (![A_11]: (v3_pre_topc(k2_struct_0(A_11), A_11) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.24/1.26  tff(c_96, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_71])).
% 2.24/1.26  tff(c_34, plain, (![D_23]: (r2_hidden('#skF_2', D_23) | ~r2_hidden(D_23, '#skF_3') | ~m1_subset_1(D_23, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.24/1.26  tff(c_72, plain, (![D_23]: (r2_hidden('#skF_2', D_23) | ~r2_hidden(D_23, '#skF_3') | ~m1_subset_1(D_23, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_34])).
% 2.24/1.26  tff(c_106, plain, (r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_96, c_72])).
% 2.24/1.26  tff(c_113, plain, (~r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(splitLeft, [status(thm)], [c_106])).
% 2.24/1.26  tff(c_32, plain, (![D_23]: (r2_hidden(D_23, '#skF_3') | ~r2_hidden('#skF_2', D_23) | ~v4_pre_topc(D_23, '#skF_1') | ~v3_pre_topc(D_23, '#skF_1') | ~m1_subset_1(D_23, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.24/1.26  tff(c_124, plain, (![D_44]: (r2_hidden(D_44, '#skF_3') | ~r2_hidden('#skF_2', D_44) | ~v4_pre_topc(D_44, '#skF_1') | ~v3_pre_topc(D_44, '#skF_1') | ~m1_subset_1(D_44, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_32])).
% 2.24/1.26  tff(c_127, plain, (r2_hidden(k2_struct_0('#skF_1'), '#skF_3') | ~r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_96, c_124])).
% 2.24/1.26  tff(c_130, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_113, c_127])).
% 2.24/1.26  tff(c_131, plain, (~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_130])).
% 2.24/1.26  tff(c_134, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_131])).
% 2.24/1.26  tff(c_138, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_134])).
% 2.24/1.26  tff(c_139, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~r2_hidden('#skF_2', k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_130])).
% 2.24/1.26  tff(c_141, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_139])).
% 2.24/1.26  tff(c_144, plain, (v1_xboole_0(k2_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_4, c_141])).
% 2.24/1.26  tff(c_147, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_144])).
% 2.24/1.26  tff(c_16, plain, (![A_10]: (~v1_xboole_0(k2_struct_0(A_10)) | ~l1_struct_0(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.24/1.26  tff(c_150, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_147, c_16])).
% 2.24/1.26  tff(c_153, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_150])).
% 2.24/1.26  tff(c_155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_153])).
% 2.24/1.26  tff(c_156, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_139])).
% 2.24/1.26  tff(c_164, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_156])).
% 2.24/1.26  tff(c_168, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_164])).
% 2.24/1.26  tff(c_170, plain, (r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(splitRight, [status(thm)], [c_106])).
% 2.24/1.26  tff(c_6, plain, (![B_5, A_4]: (~r1_tarski(B_5, A_4) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.24/1.26  tff(c_177, plain, (~r1_tarski('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_170, c_6])).
% 2.24/1.26  tff(c_181, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39, c_177])).
% 2.24/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.26  
% 2.24/1.26  Inference rules
% 2.24/1.26  ----------------------
% 2.24/1.26  #Ref     : 0
% 2.24/1.26  #Sup     : 23
% 2.24/1.26  #Fact    : 0
% 2.24/1.26  #Define  : 0
% 2.24/1.26  #Split   : 5
% 2.24/1.26  #Chain   : 0
% 2.24/1.26  #Close   : 0
% 2.24/1.26  
% 2.24/1.26  Ordering : KBO
% 2.24/1.26  
% 2.24/1.26  Simplification rules
% 2.24/1.26  ----------------------
% 2.24/1.26  #Subsume      : 3
% 2.24/1.26  #Demod        : 17
% 2.24/1.26  #Tautology    : 5
% 2.24/1.26  #SimpNegUnit  : 2
% 2.24/1.26  #BackRed      : 3
% 2.24/1.26  
% 2.24/1.26  #Partial instantiations: 0
% 2.24/1.26  #Strategies tried      : 1
% 2.24/1.26  
% 2.24/1.26  Timing (in seconds)
% 2.24/1.26  ----------------------
% 2.24/1.27  Preprocessing        : 0.31
% 2.24/1.27  Parsing              : 0.16
% 2.24/1.27  CNF conversion       : 0.02
% 2.24/1.27  Main loop            : 0.18
% 2.24/1.27  Inferencing          : 0.07
% 2.24/1.27  Reduction            : 0.05
% 2.24/1.27  Demodulation         : 0.04
% 2.24/1.27  BG Simplification    : 0.01
% 2.24/1.27  Subsumption          : 0.03
% 2.24/1.27  Abstraction          : 0.01
% 2.24/1.27  MUC search           : 0.00
% 2.24/1.27  Cooper               : 0.00
% 2.24/1.27  Total                : 0.53
% 2.24/1.27  Index Insertion      : 0.00
% 2.24/1.27  Index Deletion       : 0.00
% 2.24/1.27  Index Matching       : 0.00
% 2.24/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
