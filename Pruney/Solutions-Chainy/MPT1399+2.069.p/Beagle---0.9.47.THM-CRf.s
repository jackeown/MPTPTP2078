%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:28 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 178 expanded)
%              Number of leaves         :   32 (  74 expanded)
%              Depth                    :   11
%              Number of atoms          :  106 ( 495 expanded)
%              Number of equality atoms :   13 (  74 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_36,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_22,plain,(
    ! [A_12] :
      ( v4_pre_topc(k2_struct_0(A_12),A_12)
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_18,plain,(
    ! [A_10] :
      ( l1_struct_0(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_94,plain,(
    ! [A_34] :
      ( u1_struct_0(A_34) = k2_struct_0(A_34)
      | ~ l1_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_100,plain,(
    ! [A_36] :
      ( u1_struct_0(A_36) = k2_struct_0(A_36)
      | ~ l1_pre_topc(A_36) ) ),
    inference(resolution,[status(thm)],[c_18,c_94])).

tff(c_104,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_100])).

tff(c_20,plain,(
    ! [A_11] :
      ( ~ v1_xboole_0(u1_struct_0(A_11))
      | ~ l1_struct_0(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_110,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_20])).

tff(c_113,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_110])).

tff(c_116,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_113])).

tff(c_119,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_116])).

tff(c_123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_119])).

tff(c_124,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_106,plain,(
    m1_subset_1('#skF_2',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_30])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_24,plain,(
    ! [A_13] :
      ( v3_pre_topc(k2_struct_0(A_13),A_13)
      | ~ l1_pre_topc(A_13)
      | ~ v2_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_10,plain,(
    ! [A_5] : k2_subset_1(A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12,plain,(
    ! [A_6] : m1_subset_1(k2_subset_1(A_6),k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_45,plain,(
    ! [A_6] : m1_subset_1(A_6,k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_26,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_47,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_4])).

tff(c_86,plain,(
    ! [A_31,B_32] : ~ r2_hidden(A_31,k2_zfmisc_1(A_31,B_32)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_92,plain,(
    ! [A_1] : ~ r2_hidden(A_1,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_86])).

tff(c_38,plain,(
    ! [D_25] :
      ( r2_hidden(D_25,'#skF_3')
      | ~ r2_hidden('#skF_2',D_25)
      | ~ v4_pre_topc(D_25,'#skF_1')
      | ~ v3_pre_topc(D_25,'#skF_1')
      | ~ m1_subset_1(D_25,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_168,plain,(
    ! [D_25] :
      ( r2_hidden(D_25,'#skF_3')
      | ~ r2_hidden('#skF_2',D_25)
      | ~ v4_pre_topc(D_25,'#skF_1')
      | ~ v3_pre_topc(D_25,'#skF_1')
      | ~ m1_subset_1(D_25,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_38])).

tff(c_170,plain,(
    ! [D_46] :
      ( ~ r2_hidden('#skF_2',D_46)
      | ~ v4_pre_topc(D_46,'#skF_1')
      | ~ v3_pre_topc(D_46,'#skF_1')
      | ~ m1_subset_1(D_46,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_168])).

tff(c_175,plain,
    ( ~ r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_45,c_170])).

tff(c_176,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_175])).

tff(c_179,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_176])).

tff(c_183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_179])).

tff(c_184,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ r2_hidden('#skF_2',k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_186,plain,(
    ~ r2_hidden('#skF_2',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_189,plain,
    ( v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_14,c_186])).

tff(c_192,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_189])).

tff(c_194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_192])).

tff(c_195,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_199,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_195])).

tff(c_203,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_199])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:48:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.31  
% 2.04/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.32  %$ v4_pre_topc > v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.04/1.32  
% 2.04/1.32  %Foreground sorts:
% 2.04/1.32  
% 2.04/1.32  
% 2.04/1.32  %Background operators:
% 2.04/1.32  
% 2.04/1.32  
% 2.04/1.32  %Foreground operators:
% 2.04/1.32  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.04/1.32  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.04/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.04/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.04/1.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.04/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.04/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.04/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.04/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.04/1.32  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.04/1.32  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.04/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.04/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.32  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.04/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.04/1.32  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.04/1.32  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.04/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.04/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.04/1.32  
% 2.34/1.33  tff(f_100, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.34/1.33  tff(f_66, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.34/1.33  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.34/1.33  tff(f_48, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.34/1.33  tff(f_60, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.34/1.33  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.34/1.33  tff(f_72, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 2.34/1.33  tff(f_36, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.34/1.33  tff(f_38, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.34/1.33  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.34/1.33  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.34/1.33  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.34/1.33  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.34/1.33  tff(c_22, plain, (![A_12]: (v4_pre_topc(k2_struct_0(A_12), A_12) | ~l1_pre_topc(A_12) | ~v2_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.34/1.33  tff(c_18, plain, (![A_10]: (l1_struct_0(A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.34/1.33  tff(c_36, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.34/1.33  tff(c_94, plain, (![A_34]: (u1_struct_0(A_34)=k2_struct_0(A_34) | ~l1_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.34/1.33  tff(c_100, plain, (![A_36]: (u1_struct_0(A_36)=k2_struct_0(A_36) | ~l1_pre_topc(A_36))), inference(resolution, [status(thm)], [c_18, c_94])).
% 2.34/1.33  tff(c_104, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_100])).
% 2.34/1.33  tff(c_20, plain, (![A_11]: (~v1_xboole_0(u1_struct_0(A_11)) | ~l1_struct_0(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.34/1.33  tff(c_110, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_104, c_20])).
% 2.34/1.33  tff(c_113, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_36, c_110])).
% 2.34/1.33  tff(c_116, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_113])).
% 2.34/1.33  tff(c_119, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_116])).
% 2.34/1.33  tff(c_123, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_119])).
% 2.34/1.33  tff(c_124, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_113])).
% 2.34/1.33  tff(c_30, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.34/1.33  tff(c_106, plain, (m1_subset_1('#skF_2', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_30])).
% 2.34/1.33  tff(c_14, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.34/1.33  tff(c_24, plain, (![A_13]: (v3_pre_topc(k2_struct_0(A_13), A_13) | ~l1_pre_topc(A_13) | ~v2_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.34/1.33  tff(c_10, plain, (![A_5]: (k2_subset_1(A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.34/1.33  tff(c_12, plain, (![A_6]: (m1_subset_1(k2_subset_1(A_6), k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.34/1.33  tff(c_45, plain, (![A_6]: (m1_subset_1(A_6, k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 2.34/1.33  tff(c_26, plain, (k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.34/1.33  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.34/1.33  tff(c_47, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_4])).
% 2.34/1.33  tff(c_86, plain, (![A_31, B_32]: (~r2_hidden(A_31, k2_zfmisc_1(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.34/1.33  tff(c_92, plain, (![A_1]: (~r2_hidden(A_1, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_47, c_86])).
% 2.34/1.33  tff(c_38, plain, (![D_25]: (r2_hidden(D_25, '#skF_3') | ~r2_hidden('#skF_2', D_25) | ~v4_pre_topc(D_25, '#skF_1') | ~v3_pre_topc(D_25, '#skF_1') | ~m1_subset_1(D_25, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.34/1.33  tff(c_168, plain, (![D_25]: (r2_hidden(D_25, '#skF_3') | ~r2_hidden('#skF_2', D_25) | ~v4_pre_topc(D_25, '#skF_1') | ~v3_pre_topc(D_25, '#skF_1') | ~m1_subset_1(D_25, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_38])).
% 2.34/1.33  tff(c_170, plain, (![D_46]: (~r2_hidden('#skF_2', D_46) | ~v4_pre_topc(D_46, '#skF_1') | ~v3_pre_topc(D_46, '#skF_1') | ~m1_subset_1(D_46, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_92, c_168])).
% 2.34/1.33  tff(c_175, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_45, c_170])).
% 2.34/1.33  tff(c_176, plain, (~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_175])).
% 2.34/1.33  tff(c_179, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_176])).
% 2.34/1.33  tff(c_183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_179])).
% 2.34/1.33  tff(c_184, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~r2_hidden('#skF_2', k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_175])).
% 2.34/1.33  tff(c_186, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_184])).
% 2.34/1.33  tff(c_189, plain, (v1_xboole_0(k2_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_14, c_186])).
% 2.34/1.33  tff(c_192, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_189])).
% 2.34/1.33  tff(c_194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_124, c_192])).
% 2.34/1.33  tff(c_195, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_184])).
% 2.34/1.33  tff(c_199, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_195])).
% 2.34/1.33  tff(c_203, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_199])).
% 2.34/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.33  
% 2.34/1.33  Inference rules
% 2.34/1.33  ----------------------
% 2.34/1.33  #Ref     : 0
% 2.34/1.33  #Sup     : 29
% 2.34/1.33  #Fact    : 0
% 2.34/1.33  #Define  : 0
% 2.34/1.33  #Split   : 4
% 2.34/1.33  #Chain   : 0
% 2.34/1.33  #Close   : 0
% 2.34/1.33  
% 2.34/1.33  Ordering : KBO
% 2.34/1.33  
% 2.34/1.33  Simplification rules
% 2.34/1.33  ----------------------
% 2.34/1.33  #Subsume      : 6
% 2.34/1.33  #Demod        : 23
% 2.34/1.33  #Tautology    : 15
% 2.34/1.33  #SimpNegUnit  : 3
% 2.34/1.33  #BackRed      : 2
% 2.34/1.33  
% 2.34/1.33  #Partial instantiations: 0
% 2.34/1.33  #Strategies tried      : 1
% 2.34/1.33  
% 2.34/1.33  Timing (in seconds)
% 2.34/1.33  ----------------------
% 2.34/1.33  Preprocessing        : 0.33
% 2.34/1.33  Parsing              : 0.18
% 2.34/1.33  CNF conversion       : 0.02
% 2.34/1.33  Main loop            : 0.16
% 2.34/1.33  Inferencing          : 0.05
% 2.34/1.33  Reduction            : 0.06
% 2.34/1.33  Demodulation         : 0.04
% 2.34/1.33  BG Simplification    : 0.01
% 2.34/1.33  Subsumption          : 0.02
% 2.34/1.34  Abstraction          : 0.01
% 2.34/1.34  MUC search           : 0.00
% 2.34/1.34  Cooper               : 0.00
% 2.34/1.34  Total                : 0.53
% 2.34/1.34  Index Insertion      : 0.00
% 2.34/1.34  Index Deletion       : 0.00
% 2.34/1.34  Index Matching       : 0.00
% 2.34/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
