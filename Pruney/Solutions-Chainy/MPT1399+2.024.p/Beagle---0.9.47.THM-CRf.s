%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:22 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 178 expanded)
%              Number of leaves         :   32 (  74 expanded)
%              Depth                    :   12
%              Number of atoms          :  113 ( 516 expanded)
%              Number of equality atoms :   12 (  71 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_106,negated_conjecture,(
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

tff(f_72,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_66,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_40,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_28,plain,(
    ! [A_14] :
      ( v4_pre_topc(k2_struct_0(A_14),A_14)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_24,plain,(
    ! [A_12] :
      ( l1_struct_0(A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_91,plain,(
    ! [A_35] :
      ( u1_struct_0(A_35) = k2_struct_0(A_35)
      | ~ l1_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_96,plain,(
    ! [A_36] :
      ( u1_struct_0(A_36) = k2_struct_0(A_36)
      | ~ l1_pre_topc(A_36) ) ),
    inference(resolution,[status(thm)],[c_24,c_91])).

tff(c_100,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_96])).

tff(c_109,plain,(
    ! [A_39] :
      ( ~ v1_xboole_0(u1_struct_0(A_39))
      | ~ l1_struct_0(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_112,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_109])).

tff(c_113,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_112])).

tff(c_114,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_113])).

tff(c_117,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_114])).

tff(c_121,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_117])).

tff(c_122,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_103,plain,(
    m1_subset_1('#skF_2',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_36])).

tff(c_16,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_30,plain,(
    ! [A_15] :
      ( v3_pre_topc(k2_struct_0(A_15),A_15)
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_32,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_52,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32,c_10])).

tff(c_83,plain,(
    ! [A_32,B_33] : ~ r2_hidden(A_32,k2_zfmisc_1(A_32,B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_86,plain,(
    ! [A_3] : ~ r2_hidden(A_3,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_83])).

tff(c_44,plain,(
    ! [D_27] :
      ( r2_hidden(D_27,'#skF_3')
      | ~ r2_hidden('#skF_2',D_27)
      | ~ v4_pre_topc(D_27,'#skF_1')
      | ~ v3_pre_topc(D_27,'#skF_1')
      | ~ m1_subset_1(D_27,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_186,plain,(
    ! [D_27] :
      ( r2_hidden(D_27,'#skF_3')
      | ~ r2_hidden('#skF_2',D_27)
      | ~ v4_pre_topc(D_27,'#skF_1')
      | ~ v3_pre_topc(D_27,'#skF_1')
      | ~ m1_subset_1(D_27,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_44])).

tff(c_188,plain,(
    ! [D_53] :
      ( ~ r2_hidden('#skF_2',D_53)
      | ~ v4_pre_topc(D_53,'#skF_1')
      | ~ v3_pre_topc(D_53,'#skF_1')
      | ~ m1_subset_1(D_53,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_186])).

tff(c_194,plain,(
    ! [A_54] :
      ( ~ r2_hidden('#skF_2',A_54)
      | ~ v4_pre_topc(A_54,'#skF_1')
      | ~ v3_pre_topc(A_54,'#skF_1')
      | ~ r1_tarski(A_54,k2_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_20,c_188])).

tff(c_199,plain,
    ( ~ r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_194])).

tff(c_200,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_199])).

tff(c_203,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_200])).

tff(c_207,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_203])).

tff(c_208,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ r2_hidden('#skF_2',k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_199])).

tff(c_210,plain,(
    ~ r2_hidden('#skF_2',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_208])).

tff(c_213,plain,
    ( v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_16,c_210])).

tff(c_216,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_213])).

tff(c_218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_216])).

tff(c_219,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_208])).

tff(c_223,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_219])).

tff(c_227,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_223])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:03:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.25  
% 2.30/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.25  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.30/1.25  
% 2.30/1.25  %Foreground sorts:
% 2.30/1.25  
% 2.30/1.25  
% 2.30/1.25  %Background operators:
% 2.30/1.25  
% 2.30/1.25  
% 2.30/1.25  %Foreground operators:
% 2.30/1.25  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.30/1.25  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.30/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.30/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.30/1.25  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.30/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.30/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.30/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.30/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.30/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.30/1.25  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.30/1.25  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.30/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.30/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.25  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.30/1.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.30/1.25  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.30/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.30/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.30/1.25  
% 2.30/1.27  tff(f_106, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.30/1.27  tff(f_72, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.30/1.27  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.30/1.27  tff(f_54, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.30/1.27  tff(f_66, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.30/1.27  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.30/1.27  tff(f_78, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 2.30/1.27  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.30/1.27  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.30/1.27  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.30/1.27  tff(f_40, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.30/1.27  tff(c_40, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.30/1.27  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.30/1.27  tff(c_28, plain, (![A_14]: (v4_pre_topc(k2_struct_0(A_14), A_14) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.30/1.27  tff(c_24, plain, (![A_12]: (l1_struct_0(A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.30/1.27  tff(c_42, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.30/1.27  tff(c_91, plain, (![A_35]: (u1_struct_0(A_35)=k2_struct_0(A_35) | ~l1_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.30/1.27  tff(c_96, plain, (![A_36]: (u1_struct_0(A_36)=k2_struct_0(A_36) | ~l1_pre_topc(A_36))), inference(resolution, [status(thm)], [c_24, c_91])).
% 2.30/1.27  tff(c_100, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_96])).
% 2.30/1.27  tff(c_109, plain, (![A_39]: (~v1_xboole_0(u1_struct_0(A_39)) | ~l1_struct_0(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.30/1.27  tff(c_112, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_100, c_109])).
% 2.30/1.27  tff(c_113, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_42, c_112])).
% 2.30/1.27  tff(c_114, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_113])).
% 2.30/1.27  tff(c_117, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_114])).
% 2.30/1.27  tff(c_121, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_117])).
% 2.30/1.27  tff(c_122, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_113])).
% 2.30/1.27  tff(c_36, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.30/1.27  tff(c_103, plain, (m1_subset_1('#skF_2', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_36])).
% 2.30/1.27  tff(c_16, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.30/1.27  tff(c_30, plain, (![A_15]: (v3_pre_topc(k2_struct_0(A_15), A_15) | ~l1_pre_topc(A_15) | ~v2_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.30/1.27  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.30/1.27  tff(c_20, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.30/1.27  tff(c_32, plain, (k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.30/1.27  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.30/1.27  tff(c_52, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_32, c_10])).
% 2.30/1.27  tff(c_83, plain, (![A_32, B_33]: (~r2_hidden(A_32, k2_zfmisc_1(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.30/1.27  tff(c_86, plain, (![A_3]: (~r2_hidden(A_3, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_83])).
% 2.30/1.27  tff(c_44, plain, (![D_27]: (r2_hidden(D_27, '#skF_3') | ~r2_hidden('#skF_2', D_27) | ~v4_pre_topc(D_27, '#skF_1') | ~v3_pre_topc(D_27, '#skF_1') | ~m1_subset_1(D_27, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.30/1.27  tff(c_186, plain, (![D_27]: (r2_hidden(D_27, '#skF_3') | ~r2_hidden('#skF_2', D_27) | ~v4_pre_topc(D_27, '#skF_1') | ~v3_pre_topc(D_27, '#skF_1') | ~m1_subset_1(D_27, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_44])).
% 2.30/1.27  tff(c_188, plain, (![D_53]: (~r2_hidden('#skF_2', D_53) | ~v4_pre_topc(D_53, '#skF_1') | ~v3_pre_topc(D_53, '#skF_1') | ~m1_subset_1(D_53, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_86, c_186])).
% 2.30/1.27  tff(c_194, plain, (![A_54]: (~r2_hidden('#skF_2', A_54) | ~v4_pre_topc(A_54, '#skF_1') | ~v3_pre_topc(A_54, '#skF_1') | ~r1_tarski(A_54, k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_20, c_188])).
% 2.30/1.27  tff(c_199, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_6, c_194])).
% 2.30/1.27  tff(c_200, plain, (~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_199])).
% 2.30/1.27  tff(c_203, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_200])).
% 2.30/1.27  tff(c_207, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_203])).
% 2.30/1.27  tff(c_208, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~r2_hidden('#skF_2', k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_199])).
% 2.30/1.27  tff(c_210, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_208])).
% 2.30/1.27  tff(c_213, plain, (v1_xboole_0(k2_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_16, c_210])).
% 2.30/1.27  tff(c_216, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_213])).
% 2.30/1.27  tff(c_218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_122, c_216])).
% 2.30/1.27  tff(c_219, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_208])).
% 2.30/1.27  tff(c_223, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_219])).
% 2.30/1.27  tff(c_227, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_223])).
% 2.30/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.27  
% 2.30/1.27  Inference rules
% 2.30/1.27  ----------------------
% 2.30/1.27  #Ref     : 0
% 2.30/1.27  #Sup     : 32
% 2.30/1.27  #Fact    : 0
% 2.30/1.27  #Define  : 0
% 2.30/1.27  #Split   : 5
% 2.30/1.27  #Chain   : 0
% 2.30/1.27  #Close   : 0
% 2.30/1.27  
% 2.30/1.27  Ordering : KBO
% 2.30/1.27  
% 2.30/1.27  Simplification rules
% 2.30/1.27  ----------------------
% 2.30/1.27  #Subsume      : 6
% 2.30/1.27  #Demod        : 24
% 2.30/1.27  #Tautology    : 16
% 2.30/1.27  #SimpNegUnit  : 3
% 2.30/1.27  #BackRed      : 2
% 2.30/1.27  
% 2.30/1.27  #Partial instantiations: 0
% 2.30/1.27  #Strategies tried      : 1
% 2.30/1.27  
% 2.30/1.27  Timing (in seconds)
% 2.30/1.27  ----------------------
% 2.30/1.27  Preprocessing        : 0.31
% 2.30/1.27  Parsing              : 0.16
% 2.30/1.27  CNF conversion       : 0.02
% 2.30/1.27  Main loop            : 0.17
% 2.30/1.27  Inferencing          : 0.06
% 2.30/1.27  Reduction            : 0.06
% 2.30/1.27  Demodulation         : 0.04
% 2.30/1.27  BG Simplification    : 0.01
% 2.30/1.27  Subsumption          : 0.02
% 2.30/1.27  Abstraction          : 0.01
% 2.30/1.27  MUC search           : 0.00
% 2.30/1.27  Cooper               : 0.00
% 2.30/1.27  Total                : 0.51
% 2.30/1.27  Index Insertion      : 0.00
% 2.30/1.27  Index Deletion       : 0.00
% 2.30/1.27  Index Matching       : 0.00
% 2.30/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
