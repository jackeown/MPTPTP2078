%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:29 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 243 expanded)
%              Number of leaves         :   30 (  94 expanded)
%              Depth                    :   13
%              Number of atoms          :  109 ( 711 expanded)
%              Number of equality atoms :   11 ( 101 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(f_100,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_32,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_20,plain,(
    ! [A_11] :
      ( v4_pre_topc(k2_struct_0(A_11),A_11)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_16,plain,(
    ! [A_9] :
      ( l1_struct_0(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_81,plain,(
    ! [A_31] :
      ( u1_struct_0(A_31) = k2_struct_0(A_31)
      | ~ l1_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_86,plain,(
    ! [A_32] :
      ( u1_struct_0(A_32) = k2_struct_0(A_32)
      | ~ l1_pre_topc(A_32) ) ),
    inference(resolution,[status(thm)],[c_16,c_81])).

tff(c_90,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_86])).

tff(c_97,plain,(
    ! [A_33] :
      ( ~ v1_xboole_0(u1_struct_0(A_33))
      | ~ l1_struct_0(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_100,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_97])).

tff(c_101,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_100])).

tff(c_102,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_101])).

tff(c_105,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_102])).

tff(c_109,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_105])).

tff(c_110,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_92,plain,(
    m1_subset_1('#skF_2',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_28])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_22,plain,(
    ! [A_12] :
      ( v3_pre_topc(k2_struct_0(A_12),A_12)
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_111,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_145,plain,(
    ! [A_41] :
      ( m1_subset_1(k2_struct_0(A_41),k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_148,plain,
    ( m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_145])).

tff(c_150,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_148])).

tff(c_24,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_4])).

tff(c_73,plain,(
    ! [A_28,B_29] : ~ r2_hidden(A_28,k2_zfmisc_1(A_28,B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_76,plain,(
    ! [A_1] : ~ r2_hidden(A_1,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_73])).

tff(c_36,plain,(
    ! [D_24] :
      ( r2_hidden(D_24,'#skF_3')
      | ~ r2_hidden('#skF_2',D_24)
      | ~ v4_pre_topc(D_24,'#skF_1')
      | ~ v3_pre_topc(D_24,'#skF_1')
      | ~ m1_subset_1(D_24,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_161,plain,(
    ! [D_24] :
      ( r2_hidden(D_24,'#skF_3')
      | ~ r2_hidden('#skF_2',D_24)
      | ~ v4_pre_topc(D_24,'#skF_1')
      | ~ v3_pre_topc(D_24,'#skF_1')
      | ~ m1_subset_1(D_24,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_36])).

tff(c_163,plain,(
    ! [D_44] :
      ( ~ r2_hidden('#skF_2',D_44)
      | ~ v4_pre_topc(D_44,'#skF_1')
      | ~ v3_pre_topc(D_44,'#skF_1')
      | ~ m1_subset_1(D_44,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_161])).

tff(c_167,plain,
    ( ~ r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_150,c_163])).

tff(c_168,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_167])).

tff(c_171,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_168])).

tff(c_175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_171])).

tff(c_176,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ r2_hidden('#skF_2',k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_178,plain,(
    ~ r2_hidden('#skF_2',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_181,plain,
    ( v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_10,c_178])).

tff(c_184,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_181])).

tff(c_186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_184])).

tff(c_187,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_191,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_187])).

tff(c_195,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_191])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:23:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.29  
% 2.01/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.30  %$ v4_pre_topc > v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.01/1.30  
% 2.01/1.30  %Foreground sorts:
% 2.01/1.30  
% 2.01/1.30  
% 2.01/1.30  %Background operators:
% 2.01/1.30  
% 2.01/1.30  
% 2.01/1.30  %Foreground operators:
% 2.01/1.30  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.01/1.30  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.01/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.01/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.01/1.30  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.01/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.01/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.01/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.01/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.01/1.30  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.01/1.30  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.01/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.01/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.30  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.01/1.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.01/1.30  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.01/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.01/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.01/1.30  
% 2.28/1.31  tff(f_100, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.28/1.31  tff(f_66, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.28/1.31  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.28/1.31  tff(f_44, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.28/1.31  tff(f_60, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.28/1.31  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.28/1.31  tff(f_72, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 2.28/1.31  tff(f_48, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 2.28/1.31  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.28/1.31  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.28/1.31  tff(c_32, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.28/1.31  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.28/1.31  tff(c_20, plain, (![A_11]: (v4_pre_topc(k2_struct_0(A_11), A_11) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.28/1.31  tff(c_16, plain, (![A_9]: (l1_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.28/1.31  tff(c_34, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.28/1.31  tff(c_81, plain, (![A_31]: (u1_struct_0(A_31)=k2_struct_0(A_31) | ~l1_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.28/1.31  tff(c_86, plain, (![A_32]: (u1_struct_0(A_32)=k2_struct_0(A_32) | ~l1_pre_topc(A_32))), inference(resolution, [status(thm)], [c_16, c_81])).
% 2.28/1.31  tff(c_90, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_30, c_86])).
% 2.28/1.31  tff(c_97, plain, (![A_33]: (~v1_xboole_0(u1_struct_0(A_33)) | ~l1_struct_0(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.28/1.31  tff(c_100, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_90, c_97])).
% 2.28/1.31  tff(c_101, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_34, c_100])).
% 2.28/1.31  tff(c_102, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_101])).
% 2.28/1.31  tff(c_105, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_102])).
% 2.28/1.31  tff(c_109, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_105])).
% 2.28/1.31  tff(c_110, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_101])).
% 2.28/1.31  tff(c_28, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.28/1.31  tff(c_92, plain, (m1_subset_1('#skF_2', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_28])).
% 2.28/1.31  tff(c_10, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.28/1.31  tff(c_22, plain, (![A_12]: (v3_pre_topc(k2_struct_0(A_12), A_12) | ~l1_pre_topc(A_12) | ~v2_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.28/1.31  tff(c_111, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_101])).
% 2.28/1.31  tff(c_145, plain, (![A_41]: (m1_subset_1(k2_struct_0(A_41), k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.28/1.31  tff(c_148, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_90, c_145])).
% 2.28/1.31  tff(c_150, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_148])).
% 2.28/1.31  tff(c_24, plain, (k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.28/1.31  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.28/1.31  tff(c_44, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_4])).
% 2.28/1.31  tff(c_73, plain, (![A_28, B_29]: (~r2_hidden(A_28, k2_zfmisc_1(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.28/1.31  tff(c_76, plain, (![A_1]: (~r2_hidden(A_1, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_73])).
% 2.28/1.31  tff(c_36, plain, (![D_24]: (r2_hidden(D_24, '#skF_3') | ~r2_hidden('#skF_2', D_24) | ~v4_pre_topc(D_24, '#skF_1') | ~v3_pre_topc(D_24, '#skF_1') | ~m1_subset_1(D_24, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.28/1.31  tff(c_161, plain, (![D_24]: (r2_hidden(D_24, '#skF_3') | ~r2_hidden('#skF_2', D_24) | ~v4_pre_topc(D_24, '#skF_1') | ~v3_pre_topc(D_24, '#skF_1') | ~m1_subset_1(D_24, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_36])).
% 2.28/1.31  tff(c_163, plain, (![D_44]: (~r2_hidden('#skF_2', D_44) | ~v4_pre_topc(D_44, '#skF_1') | ~v3_pre_topc(D_44, '#skF_1') | ~m1_subset_1(D_44, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_76, c_161])).
% 2.28/1.31  tff(c_167, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_150, c_163])).
% 2.28/1.31  tff(c_168, plain, (~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_167])).
% 2.28/1.31  tff(c_171, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_168])).
% 2.28/1.31  tff(c_175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_171])).
% 2.28/1.31  tff(c_176, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~r2_hidden('#skF_2', k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_167])).
% 2.28/1.31  tff(c_178, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_176])).
% 2.28/1.31  tff(c_181, plain, (v1_xboole_0(k2_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_178])).
% 2.28/1.31  tff(c_184, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_181])).
% 2.28/1.31  tff(c_186, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_184])).
% 2.28/1.31  tff(c_187, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_176])).
% 2.28/1.31  tff(c_191, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_187])).
% 2.28/1.31  tff(c_195, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_191])).
% 2.28/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.31  
% 2.28/1.31  Inference rules
% 2.28/1.31  ----------------------
% 2.28/1.31  #Ref     : 0
% 2.28/1.31  #Sup     : 28
% 2.28/1.31  #Fact    : 0
% 2.28/1.31  #Define  : 0
% 2.28/1.31  #Split   : 4
% 2.28/1.31  #Chain   : 0
% 2.28/1.31  #Close   : 0
% 2.28/1.31  
% 2.28/1.31  Ordering : KBO
% 2.28/1.31  
% 2.28/1.31  Simplification rules
% 2.28/1.31  ----------------------
% 2.28/1.31  #Subsume      : 6
% 2.28/1.31  #Demod        : 23
% 2.28/1.31  #Tautology    : 13
% 2.28/1.31  #SimpNegUnit  : 3
% 2.28/1.31  #BackRed      : 2
% 2.28/1.31  
% 2.28/1.31  #Partial instantiations: 0
% 2.28/1.31  #Strategies tried      : 1
% 2.28/1.31  
% 2.28/1.31  Timing (in seconds)
% 2.28/1.31  ----------------------
% 2.28/1.32  Preprocessing        : 0.32
% 2.28/1.32  Parsing              : 0.18
% 2.28/1.32  CNF conversion       : 0.02
% 2.28/1.32  Main loop            : 0.16
% 2.28/1.32  Inferencing          : 0.05
% 2.28/1.32  Reduction            : 0.05
% 2.28/1.32  Demodulation         : 0.04
% 2.28/1.32  BG Simplification    : 0.01
% 2.28/1.32  Subsumption          : 0.02
% 2.28/1.32  Abstraction          : 0.01
% 2.28/1.32  MUC search           : 0.00
% 2.28/1.32  Cooper               : 0.00
% 2.28/1.32  Total                : 0.52
% 2.28/1.32  Index Insertion      : 0.00
% 2.28/1.32  Index Deletion       : 0.00
% 2.28/1.32  Index Matching       : 0.00
% 2.28/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
