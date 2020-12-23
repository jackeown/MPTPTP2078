%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:24 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 193 expanded)
%              Number of leaves         :   32 (  79 expanded)
%              Depth                    :   11
%              Number of atoms          :  120 ( 547 expanded)
%              Number of equality atoms :   15 (  80 expanded)
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

tff(f_107,negated_conjecture,(
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

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_49,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_51,axiom,(
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

tff(f_67,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_24,plain,(
    ! [A_10] :
      ( l1_struct_0(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_100,plain,(
    ! [A_34] :
      ( u1_struct_0(A_34) = k2_struct_0(A_34)
      | ~ l1_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_250,plain,(
    ! [A_54] :
      ( u1_struct_0(A_54) = k2_struct_0(A_54)
      | ~ l1_pre_topc(A_54) ) ),
    inference(resolution,[status(thm)],[c_24,c_100])).

tff(c_254,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_250])).

tff(c_40,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_28,plain,(
    ! [A_12] :
      ( v4_pre_topc(k2_struct_0(A_12),A_12)
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_120,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(resolution,[status(thm)],[c_24,c_100])).

tff(c_124,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_120])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_105,plain,(
    ! [B_35,A_36] :
      ( v1_xboole_0(B_35)
      | ~ m1_subset_1(B_35,A_36)
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_117,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_36,c_105])).

tff(c_119,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_125,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_119])).

tff(c_127,plain,(
    m1_subset_1('#skF_2',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_36])).

tff(c_12,plain,(
    ! [B_6,A_5] :
      ( r2_hidden(B_6,A_5)
      | ~ m1_subset_1(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_30,plain,(
    ! [A_13] :
      ( v3_pre_topc(k2_struct_0(A_13),A_13)
      | ~ l1_pre_topc(A_13)
      | ~ v2_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_18,plain,(
    ! [A_7] : k2_subset_1(A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    ! [A_8] : m1_subset_1(k2_subset_1(A_8),k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_51,plain,(
    ! [A_8] : m1_subset_1(A_8,k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20])).

tff(c_32,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_53,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32,c_4])).

tff(c_92,plain,(
    ! [A_31,B_32] : ~ r2_hidden(A_31,k2_zfmisc_1(A_31,B_32)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_98,plain,(
    ! [A_1] : ~ r2_hidden(A_1,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_92])).

tff(c_44,plain,(
    ! [D_25] :
      ( r2_hidden(D_25,'#skF_3')
      | ~ r2_hidden('#skF_2',D_25)
      | ~ v4_pre_topc(D_25,'#skF_1')
      | ~ v3_pre_topc(D_25,'#skF_1')
      | ~ m1_subset_1(D_25,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_207,plain,(
    ! [D_25] :
      ( r2_hidden(D_25,'#skF_3')
      | ~ r2_hidden('#skF_2',D_25)
      | ~ v4_pre_topc(D_25,'#skF_1')
      | ~ v3_pre_topc(D_25,'#skF_1')
      | ~ m1_subset_1(D_25,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_44])).

tff(c_209,plain,(
    ! [D_53] :
      ( ~ r2_hidden('#skF_2',D_53)
      | ~ v4_pre_topc(D_53,'#skF_1')
      | ~ v3_pre_topc(D_53,'#skF_1')
      | ~ m1_subset_1(D_53,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_207])).

tff(c_219,plain,
    ( ~ r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_51,c_209])).

tff(c_220,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_219])).

tff(c_223,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_220])).

tff(c_227,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_223])).

tff(c_228,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ r2_hidden('#skF_2',k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_230,plain,(
    ~ r2_hidden('#skF_2',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_228])).

tff(c_233,plain,
    ( ~ m1_subset_1('#skF_2',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_12,c_230])).

tff(c_236,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_233])).

tff(c_238,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_236])).

tff(c_239,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_243,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_239])).

tff(c_247,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_243])).

tff(c_249,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_255,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_249])).

tff(c_262,plain,(
    ! [A_55] :
      ( ~ v1_xboole_0(u1_struct_0(A_55))
      | ~ l1_struct_0(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_265,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_262])).

tff(c_267,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_265])).

tff(c_268,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_267])).

tff(c_271,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_268])).

tff(c_275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_271])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:15:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.25  
% 2.17/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.25  %$ v4_pre_topc > v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.17/1.25  
% 2.17/1.25  %Foreground sorts:
% 2.17/1.25  
% 2.17/1.25  
% 2.17/1.25  %Background operators:
% 2.17/1.25  
% 2.17/1.25  
% 2.17/1.25  %Foreground operators:
% 2.17/1.25  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.17/1.25  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.17/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.25  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.17/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.17/1.25  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.17/1.25  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.17/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.17/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.25  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.17/1.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.17/1.25  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.17/1.25  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.17/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.17/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.17/1.25  
% 2.17/1.27  tff(f_107, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.17/1.27  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.17/1.27  tff(f_55, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.17/1.27  tff(f_73, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.17/1.27  tff(f_47, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.17/1.27  tff(f_79, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 2.17/1.27  tff(f_49, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.17/1.27  tff(f_51, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.17/1.27  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.17/1.27  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.17/1.27  tff(f_67, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.17/1.27  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.17/1.27  tff(c_24, plain, (![A_10]: (l1_struct_0(A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.17/1.27  tff(c_42, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.17/1.27  tff(c_100, plain, (![A_34]: (u1_struct_0(A_34)=k2_struct_0(A_34) | ~l1_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.17/1.27  tff(c_250, plain, (![A_54]: (u1_struct_0(A_54)=k2_struct_0(A_54) | ~l1_pre_topc(A_54))), inference(resolution, [status(thm)], [c_24, c_100])).
% 2.17/1.27  tff(c_254, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_250])).
% 2.17/1.27  tff(c_40, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.17/1.27  tff(c_28, plain, (![A_12]: (v4_pre_topc(k2_struct_0(A_12), A_12) | ~l1_pre_topc(A_12) | ~v2_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.17/1.27  tff(c_120, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_pre_topc(A_38))), inference(resolution, [status(thm)], [c_24, c_100])).
% 2.17/1.27  tff(c_124, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_120])).
% 2.17/1.27  tff(c_36, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.17/1.27  tff(c_105, plain, (![B_35, A_36]: (v1_xboole_0(B_35) | ~m1_subset_1(B_35, A_36) | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.17/1.27  tff(c_117, plain, (v1_xboole_0('#skF_2') | ~v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_105])).
% 2.17/1.27  tff(c_119, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_117])).
% 2.17/1.27  tff(c_125, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_119])).
% 2.17/1.27  tff(c_127, plain, (m1_subset_1('#skF_2', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_36])).
% 2.17/1.27  tff(c_12, plain, (![B_6, A_5]: (r2_hidden(B_6, A_5) | ~m1_subset_1(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.17/1.27  tff(c_30, plain, (![A_13]: (v3_pre_topc(k2_struct_0(A_13), A_13) | ~l1_pre_topc(A_13) | ~v2_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.17/1.27  tff(c_18, plain, (![A_7]: (k2_subset_1(A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.17/1.27  tff(c_20, plain, (![A_8]: (m1_subset_1(k2_subset_1(A_8), k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.17/1.27  tff(c_51, plain, (![A_8]: (m1_subset_1(A_8, k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20])).
% 2.17/1.27  tff(c_32, plain, (k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.17/1.27  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.17/1.27  tff(c_53, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_32, c_4])).
% 2.17/1.27  tff(c_92, plain, (![A_31, B_32]: (~r2_hidden(A_31, k2_zfmisc_1(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.17/1.27  tff(c_98, plain, (![A_1]: (~r2_hidden(A_1, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_53, c_92])).
% 2.17/1.27  tff(c_44, plain, (![D_25]: (r2_hidden(D_25, '#skF_3') | ~r2_hidden('#skF_2', D_25) | ~v4_pre_topc(D_25, '#skF_1') | ~v3_pre_topc(D_25, '#skF_1') | ~m1_subset_1(D_25, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.17/1.27  tff(c_207, plain, (![D_25]: (r2_hidden(D_25, '#skF_3') | ~r2_hidden('#skF_2', D_25) | ~v4_pre_topc(D_25, '#skF_1') | ~v3_pre_topc(D_25, '#skF_1') | ~m1_subset_1(D_25, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_44])).
% 2.17/1.27  tff(c_209, plain, (![D_53]: (~r2_hidden('#skF_2', D_53) | ~v4_pre_topc(D_53, '#skF_1') | ~v3_pre_topc(D_53, '#skF_1') | ~m1_subset_1(D_53, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_98, c_207])).
% 2.17/1.27  tff(c_219, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_51, c_209])).
% 2.17/1.27  tff(c_220, plain, (~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_219])).
% 2.17/1.27  tff(c_223, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_220])).
% 2.17/1.27  tff(c_227, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_223])).
% 2.17/1.27  tff(c_228, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~r2_hidden('#skF_2', k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_219])).
% 2.17/1.27  tff(c_230, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_228])).
% 2.17/1.27  tff(c_233, plain, (~m1_subset_1('#skF_2', k2_struct_0('#skF_1')) | v1_xboole_0(k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_12, c_230])).
% 2.17/1.27  tff(c_236, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_233])).
% 2.17/1.27  tff(c_238, plain, $false, inference(negUnitSimplification, [status(thm)], [c_125, c_236])).
% 2.17/1.27  tff(c_239, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_228])).
% 2.17/1.27  tff(c_243, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_239])).
% 2.17/1.27  tff(c_247, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_243])).
% 2.17/1.27  tff(c_249, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_117])).
% 2.17/1.27  tff(c_255, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_254, c_249])).
% 2.17/1.27  tff(c_262, plain, (![A_55]: (~v1_xboole_0(u1_struct_0(A_55)) | ~l1_struct_0(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.17/1.27  tff(c_265, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_254, c_262])).
% 2.17/1.27  tff(c_267, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_255, c_265])).
% 2.17/1.27  tff(c_268, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_42, c_267])).
% 2.17/1.27  tff(c_271, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_268])).
% 2.17/1.27  tff(c_275, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_271])).
% 2.17/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.27  
% 2.17/1.27  Inference rules
% 2.17/1.27  ----------------------
% 2.17/1.27  #Ref     : 0
% 2.17/1.27  #Sup     : 42
% 2.17/1.27  #Fact    : 0
% 2.17/1.27  #Define  : 0
% 2.17/1.27  #Split   : 6
% 2.17/1.27  #Chain   : 0
% 2.17/1.27  #Close   : 0
% 2.17/1.27  
% 2.17/1.27  Ordering : KBO
% 2.17/1.27  
% 2.17/1.27  Simplification rules
% 2.17/1.27  ----------------------
% 2.17/1.27  #Subsume      : 10
% 2.17/1.27  #Demod        : 27
% 2.17/1.27  #Tautology    : 19
% 2.17/1.27  #SimpNegUnit  : 6
% 2.17/1.27  #BackRed      : 6
% 2.17/1.27  
% 2.17/1.27  #Partial instantiations: 0
% 2.17/1.27  #Strategies tried      : 1
% 2.17/1.27  
% 2.17/1.27  Timing (in seconds)
% 2.17/1.27  ----------------------
% 2.17/1.27  Preprocessing        : 0.31
% 2.17/1.27  Parsing              : 0.17
% 2.17/1.27  CNF conversion       : 0.02
% 2.17/1.27  Main loop            : 0.19
% 2.17/1.27  Inferencing          : 0.06
% 2.17/1.27  Reduction            : 0.06
% 2.17/1.27  Demodulation         : 0.04
% 2.17/1.27  BG Simplification    : 0.01
% 2.17/1.27  Subsumption          : 0.03
% 2.17/1.27  Abstraction          : 0.01
% 2.17/1.27  MUC search           : 0.00
% 2.17/1.27  Cooper               : 0.00
% 2.17/1.27  Total                : 0.54
% 2.17/1.27  Index Insertion      : 0.00
% 2.17/1.27  Index Deletion       : 0.00
% 2.17/1.27  Index Matching       : 0.00
% 2.17/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
