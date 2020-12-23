%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:50 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 124 expanded)
%              Number of leaves         :   21 (  60 expanded)
%              Depth                    :   10
%              Number of atoms          :   95 ( 548 expanded)
%              Number of equality atoms :   12 (  51 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_102,negated_conjecture,(
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

tff(f_50,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_76,axiom,(
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

tff(c_32,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_30,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_28,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_26,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_24,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_16,plain,(
    m1_orders_2('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_44,plain,(
    ! [C_23,B_24,A_25] :
      ( r1_tarski(C_23,B_24)
      | ~ m1_orders_2(C_23,A_25,B_24)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_orders_2(A_25)
      | ~ v5_orders_2(A_25)
      | ~ v4_orders_2(A_25)
      | ~ v3_orders_2(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_46,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_44])).

tff(c_51,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_20,c_46])).

tff(c_52,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_51])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_14,plain,(
    m1_orders_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_48,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_44])).

tff(c_55,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_22,c_48])).

tff(c_56,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_55])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_61,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_2])).

tff(c_64,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_61])).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_70,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_18])).

tff(c_68,plain,(
    m1_orders_2('#skF_3','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_16])).

tff(c_12,plain,(
    ! [B_12,A_10] :
      ( ~ m1_orders_2(B_12,A_10,B_12)
      | k1_xboole_0 = B_12
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_orders_2(A_10)
      | ~ v5_orders_2(A_10)
      | ~ v4_orders_2(A_10)
      | ~ v3_orders_2(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_81,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_12])).

tff(c_88,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_20,c_81])).

tff(c_90,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_70,c_88])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:49:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.23  
% 2.00/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.23  %$ m1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.00/1.23  
% 2.00/1.23  %Foreground sorts:
% 2.00/1.23  
% 2.00/1.23  
% 2.00/1.23  %Background operators:
% 2.00/1.23  
% 2.00/1.23  
% 2.00/1.23  %Foreground operators:
% 2.00/1.23  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.00/1.23  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.00/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.00/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.00/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.00/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.23  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.00/1.23  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.00/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.00/1.23  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.00/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.23  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 2.00/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.23  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.00/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.00/1.23  
% 2.00/1.25  tff(f_102, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_orders_2)).
% 2.00/1.25  tff(f_50, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_orders_2)).
% 2.00/1.25  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.00/1.25  tff(f_76, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (~(~(B = k1_xboole_0) & m1_orders_2(B, A, B)) & ~(~m1_orders_2(B, A, B) & (B = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_orders_2)).
% 2.00/1.25  tff(c_32, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.00/1.25  tff(c_30, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.00/1.25  tff(c_28, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.00/1.25  tff(c_26, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.00/1.25  tff(c_24, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.00/1.25  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.00/1.25  tff(c_16, plain, (m1_orders_2('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.00/1.25  tff(c_44, plain, (![C_23, B_24, A_25]: (r1_tarski(C_23, B_24) | ~m1_orders_2(C_23, A_25, B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_orders_2(A_25) | ~v5_orders_2(A_25) | ~v4_orders_2(A_25) | ~v3_orders_2(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.00/1.25  tff(c_46, plain, (r1_tarski('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_44])).
% 2.00/1.25  tff(c_51, plain, (r1_tarski('#skF_2', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_20, c_46])).
% 2.00/1.25  tff(c_52, plain, (r1_tarski('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_32, c_51])).
% 2.00/1.25  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.00/1.25  tff(c_14, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.00/1.25  tff(c_48, plain, (r1_tarski('#skF_3', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_14, c_44])).
% 2.00/1.25  tff(c_55, plain, (r1_tarski('#skF_3', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_22, c_48])).
% 2.00/1.25  tff(c_56, plain, (r1_tarski('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_32, c_55])).
% 2.00/1.25  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.00/1.25  tff(c_61, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_2])).
% 2.00/1.25  tff(c_64, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_61])).
% 2.00/1.25  tff(c_18, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.00/1.25  tff(c_70, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_18])).
% 2.00/1.25  tff(c_68, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_16])).
% 2.00/1.25  tff(c_12, plain, (![B_12, A_10]: (~m1_orders_2(B_12, A_10, B_12) | k1_xboole_0=B_12 | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_orders_2(A_10) | ~v5_orders_2(A_10) | ~v4_orders_2(A_10) | ~v3_orders_2(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.00/1.25  tff(c_81, plain, (k1_xboole_0='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_68, c_12])).
% 2.00/1.25  tff(c_88, plain, (k1_xboole_0='#skF_3' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_20, c_81])).
% 2.00/1.25  tff(c_90, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_70, c_88])).
% 2.00/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.25  
% 2.00/1.25  Inference rules
% 2.00/1.25  ----------------------
% 2.00/1.25  #Ref     : 0
% 2.00/1.25  #Sup     : 9
% 2.00/1.25  #Fact    : 0
% 2.00/1.25  #Define  : 0
% 2.00/1.25  #Split   : 0
% 2.00/1.25  #Chain   : 0
% 2.00/1.25  #Close   : 0
% 2.00/1.25  
% 2.00/1.25  Ordering : KBO
% 2.00/1.25  
% 2.00/1.25  Simplification rules
% 2.00/1.25  ----------------------
% 2.00/1.25  #Subsume      : 0
% 2.00/1.25  #Demod        : 33
% 2.00/1.25  #Tautology    : 8
% 2.00/1.25  #SimpNegUnit  : 4
% 2.00/1.25  #BackRed      : 6
% 2.00/1.25  
% 2.00/1.25  #Partial instantiations: 0
% 2.00/1.25  #Strategies tried      : 1
% 2.00/1.25  
% 2.00/1.25  Timing (in seconds)
% 2.00/1.25  ----------------------
% 2.00/1.25  Preprocessing        : 0.32
% 2.00/1.25  Parsing              : 0.17
% 2.00/1.25  CNF conversion       : 0.02
% 2.00/1.25  Main loop            : 0.12
% 2.00/1.25  Inferencing          : 0.04
% 2.00/1.25  Reduction            : 0.04
% 2.00/1.25  Demodulation         : 0.03
% 2.00/1.25  BG Simplification    : 0.01
% 2.00/1.25  Subsumption          : 0.02
% 2.00/1.25  Abstraction          : 0.01
% 2.00/1.25  MUC search           : 0.00
% 2.00/1.25  Cooper               : 0.00
% 2.00/1.25  Total                : 0.47
% 2.00/1.25  Index Insertion      : 0.00
% 2.00/1.25  Index Deletion       : 0.00
% 2.00/1.25  Index Matching       : 0.00
% 2.00/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
