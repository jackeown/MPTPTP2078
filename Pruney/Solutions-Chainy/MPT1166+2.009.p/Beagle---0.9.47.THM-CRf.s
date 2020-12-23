%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:51 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 131 expanded)
%              Number of leaves         :   23 (  63 expanded)
%              Depth                    :   10
%              Number of atoms          :  102 ( 562 expanded)
%              Number of equality atoms :   13 (  53 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_orders_2 > r2_xboole_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(m1_orders_2,type,(
    m1_orders_2: ( $i * $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( B != k1_xboole_0
                    & m1_orders_2(B,A,C)
                    & m1_orders_2(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_orders_2)).

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_orders_2(C,A,B)
             => r1_tarski(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_orders_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ~ ( B != k1_xboole_0
                & m1_orders_2(B,A,B) )
            & ~ ( ~ m1_orders_2(B,A,B)
                & B = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_orders_2)).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_32,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_30,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_28,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_26,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_18,plain,(
    m1_orders_2('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_56,plain,(
    ! [C_31,B_32,A_33] :
      ( r1_tarski(C_31,B_32)
      | ~ m1_orders_2(C_31,A_33,B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_orders_2(A_33)
      | ~ v5_orders_2(A_33)
      | ~ v4_orders_2(A_33)
      | ~ v3_orders_2(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_58,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_56])).

tff(c_63,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_26,c_22,c_58])).

tff(c_64,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_63])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_16,plain,(
    m1_orders_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_60,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_56])).

tff(c_67,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_26,c_24,c_60])).

tff(c_68,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_67])).

tff(c_38,plain,(
    ! [A_24,B_25] :
      ( r2_xboole_0(A_24,B_25)
      | B_25 = A_24
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( ~ r2_xboole_0(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_50,plain,(
    ! [B_25,A_24] :
      ( ~ r1_tarski(B_25,A_24)
      | B_25 = A_24
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(resolution,[status(thm)],[c_38,c_8])).

tff(c_73,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_50])).

tff(c_76,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_73])).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_82,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_20])).

tff(c_80,plain,(
    m1_orders_2('#skF_3','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_18])).

tff(c_14,plain,(
    ! [B_14,A_12] :
      ( ~ m1_orders_2(B_14,A_12,B_14)
      | k1_xboole_0 = B_14
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_orders_2(A_12)
      | ~ v5_orders_2(A_12)
      | ~ v4_orders_2(A_12)
      | ~ v3_orders_2(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_98,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_14])).

tff(c_105,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_26,c_22,c_98])).

tff(c_107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_82,c_105])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:00:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.21  
% 1.82/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.21  %$ m1_orders_2 > r2_xboole_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.82/1.21  
% 1.82/1.21  %Foreground sorts:
% 1.82/1.21  
% 1.82/1.21  
% 1.82/1.21  %Background operators:
% 1.82/1.21  
% 1.82/1.21  
% 1.82/1.21  %Foreground operators:
% 1.82/1.21  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.82/1.21  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 1.82/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.82/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.82/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.82/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.82/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.82/1.21  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 1.82/1.21  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 1.82/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.82/1.21  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.82/1.21  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.82/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.21  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 1.82/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.21  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.82/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.82/1.22  
% 1.82/1.23  tff(f_108, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_orders_2)).
% 1.82/1.23  tff(f_56, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_orders_2)).
% 1.82/1.23  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.82/1.23  tff(f_37, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_xboole_1)).
% 1.82/1.23  tff(f_82, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (~(~(B = k1_xboole_0) & m1_orders_2(B, A, B)) & ~(~m1_orders_2(B, A, B) & (B = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_orders_2)).
% 1.82/1.23  tff(c_34, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 1.82/1.23  tff(c_32, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 1.82/1.23  tff(c_30, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 1.82/1.23  tff(c_28, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 1.82/1.23  tff(c_26, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 1.82/1.23  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 1.82/1.23  tff(c_18, plain, (m1_orders_2('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 1.82/1.23  tff(c_56, plain, (![C_31, B_32, A_33]: (r1_tarski(C_31, B_32) | ~m1_orders_2(C_31, A_33, B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_orders_2(A_33) | ~v5_orders_2(A_33) | ~v4_orders_2(A_33) | ~v3_orders_2(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.82/1.23  tff(c_58, plain, (r1_tarski('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_56])).
% 1.82/1.23  tff(c_63, plain, (r1_tarski('#skF_2', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_26, c_22, c_58])).
% 1.82/1.23  tff(c_64, plain, (r1_tarski('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_34, c_63])).
% 1.82/1.23  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 1.82/1.23  tff(c_16, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 1.82/1.23  tff(c_60, plain, (r1_tarski('#skF_3', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_56])).
% 1.82/1.23  tff(c_67, plain, (r1_tarski('#skF_3', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_26, c_24, c_60])).
% 1.82/1.23  tff(c_68, plain, (r1_tarski('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_34, c_67])).
% 1.82/1.23  tff(c_38, plain, (![A_24, B_25]: (r2_xboole_0(A_24, B_25) | B_25=A_24 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.82/1.23  tff(c_8, plain, (![B_4, A_3]: (~r2_xboole_0(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.82/1.23  tff(c_50, plain, (![B_25, A_24]: (~r1_tarski(B_25, A_24) | B_25=A_24 | ~r1_tarski(A_24, B_25))), inference(resolution, [status(thm)], [c_38, c_8])).
% 1.82/1.23  tff(c_73, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_50])).
% 1.82/1.23  tff(c_76, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_73])).
% 1.82/1.23  tff(c_20, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_108])).
% 1.82/1.23  tff(c_82, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_20])).
% 1.82/1.23  tff(c_80, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_18])).
% 1.82/1.23  tff(c_14, plain, (![B_14, A_12]: (~m1_orders_2(B_14, A_12, B_14) | k1_xboole_0=B_14 | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_orders_2(A_12) | ~v5_orders_2(A_12) | ~v4_orders_2(A_12) | ~v3_orders_2(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.82/1.23  tff(c_98, plain, (k1_xboole_0='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_80, c_14])).
% 1.82/1.23  tff(c_105, plain, (k1_xboole_0='#skF_3' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_26, c_22, c_98])).
% 1.82/1.23  tff(c_107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_82, c_105])).
% 1.82/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.23  
% 1.82/1.23  Inference rules
% 1.82/1.23  ----------------------
% 1.82/1.23  #Ref     : 0
% 1.82/1.23  #Sup     : 12
% 1.82/1.23  #Fact    : 0
% 1.82/1.23  #Define  : 0
% 1.82/1.23  #Split   : 0
% 1.82/1.23  #Chain   : 0
% 1.82/1.23  #Close   : 0
% 1.82/1.23  
% 1.82/1.23  Ordering : KBO
% 1.82/1.23  
% 1.82/1.23  Simplification rules
% 1.82/1.23  ----------------------
% 1.82/1.23  #Subsume      : 0
% 1.82/1.23  #Demod        : 31
% 1.82/1.23  #Tautology    : 8
% 1.82/1.23  #SimpNegUnit  : 4
% 1.82/1.23  #BackRed      : 6
% 1.82/1.23  
% 1.82/1.23  #Partial instantiations: 0
% 1.82/1.23  #Strategies tried      : 1
% 1.82/1.23  
% 1.82/1.23  Timing (in seconds)
% 1.82/1.23  ----------------------
% 1.82/1.23  Preprocessing        : 0.28
% 1.82/1.23  Parsing              : 0.15
% 1.82/1.23  CNF conversion       : 0.02
% 1.82/1.23  Main loop            : 0.12
% 1.82/1.23  Inferencing          : 0.05
% 1.82/1.23  Reduction            : 0.04
% 1.82/1.23  Demodulation         : 0.03
% 1.82/1.23  BG Simplification    : 0.01
% 1.82/1.23  Subsumption          : 0.02
% 1.82/1.23  Abstraction          : 0.01
% 1.82/1.23  MUC search           : 0.00
% 1.82/1.23  Cooper               : 0.00
% 1.82/1.23  Total                : 0.44
% 1.82/1.23  Index Insertion      : 0.00
% 1.82/1.23  Index Deletion       : 0.00
% 1.82/1.23  Index Matching       : 0.00
% 1.82/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
