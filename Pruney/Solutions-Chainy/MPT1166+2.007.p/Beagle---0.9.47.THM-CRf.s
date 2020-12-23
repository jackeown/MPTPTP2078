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
% DateTime   : Thu Dec  3 10:19:50 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 137 expanded)
%              Number of leaves         :   23 (  65 expanded)
%              Depth                    :   11
%              Number of atoms          :  109 ( 582 expanded)
%              Number of equality atoms :   14 (  57 expanded)
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

tff(f_109,negated_conjecture,(
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

tff(f_57,axiom,(
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

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r2_xboole_0(B,C) )
     => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l58_xboole_1)).

tff(f_83,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_32,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_30,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_28,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_26,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_16,plain,(
    m1_orders_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_55,plain,(
    ! [C_34,B_35,A_36] :
      ( r1_tarski(C_34,B_35)
      | ~ m1_orders_2(C_34,A_36,B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_orders_2(A_36)
      | ~ v5_orders_2(A_36)
      | ~ v4_orders_2(A_36)
      | ~ v3_orders_2(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_59,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_55])).

tff(c_66,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_26,c_24,c_59])).

tff(c_67,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_66])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_18,plain,(
    m1_orders_2('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_57,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_55])).

tff(c_62,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_26,c_22,c_57])).

tff(c_63,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_62])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_xboole_0(A_1,B_2)
      | B_2 = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_48,plain,(
    ! [A_25,C_26,B_27] :
      ( r2_xboole_0(A_25,C_26)
      | ~ r2_xboole_0(B_27,C_26)
      | ~ r1_tarski(A_25,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_51,plain,(
    ! [A_25,B_2,A_1] :
      ( r2_xboole_0(A_25,B_2)
      | ~ r1_tarski(A_25,A_1)
      | B_2 = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_2,c_48])).

tff(c_74,plain,(
    ! [B_37] :
      ( r2_xboole_0('#skF_2',B_37)
      | B_37 = '#skF_3'
      | ~ r1_tarski('#skF_3',B_37) ) ),
    inference(resolution,[status(thm)],[c_63,c_51])).

tff(c_4,plain,(
    ! [B_2] : ~ r2_xboole_0(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_83,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_4])).

tff(c_88,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_83])).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_95,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_20])).

tff(c_94,plain,(
    m1_orders_2('#skF_3','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_16])).

tff(c_14,plain,(
    ! [B_15,A_13] :
      ( ~ m1_orders_2(B_15,A_13,B_15)
      | k1_xboole_0 = B_15
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_orders_2(A_13)
      | ~ v5_orders_2(A_13)
      | ~ v4_orders_2(A_13)
      | ~ v3_orders_2(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_109,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_94,c_14])).

tff(c_116,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_26,c_22,c_109])).

tff(c_118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_95,c_116])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:46:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.35  
% 1.88/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.35  %$ m1_orders_2 > r2_xboole_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.88/1.35  
% 1.88/1.35  %Foreground sorts:
% 1.88/1.35  
% 1.88/1.35  
% 1.88/1.35  %Background operators:
% 1.88/1.35  
% 1.88/1.35  
% 1.88/1.35  %Foreground operators:
% 1.88/1.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.88/1.35  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 1.88/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.88/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.88/1.35  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.35  tff('#skF_3', type, '#skF_3': $i).
% 1.88/1.35  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.35  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 1.88/1.35  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 1.88/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.88/1.35  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.88/1.35  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.88/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.35  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 1.88/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.88/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.88/1.35  
% 2.04/1.37  tff(f_109, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_orders_2)).
% 2.04/1.37  tff(f_57, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_orders_2)).
% 2.04/1.37  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.04/1.37  tff(f_38, axiom, (![A, B, C]: ((r1_tarski(A, B) & r2_xboole_0(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l58_xboole_1)).
% 2.04/1.37  tff(f_83, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (~(~(B = k1_xboole_0) & m1_orders_2(B, A, B)) & ~(~m1_orders_2(B, A, B) & (B = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_orders_2)).
% 2.04/1.37  tff(c_34, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.04/1.37  tff(c_32, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.04/1.37  tff(c_30, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.04/1.37  tff(c_28, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.04/1.37  tff(c_26, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.04/1.37  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.04/1.37  tff(c_16, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.04/1.37  tff(c_55, plain, (![C_34, B_35, A_36]: (r1_tarski(C_34, B_35) | ~m1_orders_2(C_34, A_36, B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_orders_2(A_36) | ~v5_orders_2(A_36) | ~v4_orders_2(A_36) | ~v3_orders_2(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.04/1.37  tff(c_59, plain, (r1_tarski('#skF_3', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_55])).
% 2.04/1.37  tff(c_66, plain, (r1_tarski('#skF_3', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_26, c_24, c_59])).
% 2.04/1.37  tff(c_67, plain, (r1_tarski('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_34, c_66])).
% 2.04/1.37  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.04/1.37  tff(c_18, plain, (m1_orders_2('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.04/1.37  tff(c_57, plain, (r1_tarski('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_55])).
% 2.04/1.37  tff(c_62, plain, (r1_tarski('#skF_2', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_26, c_22, c_57])).
% 2.04/1.37  tff(c_63, plain, (r1_tarski('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_34, c_62])).
% 2.04/1.37  tff(c_2, plain, (![A_1, B_2]: (r2_xboole_0(A_1, B_2) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.04/1.37  tff(c_48, plain, (![A_25, C_26, B_27]: (r2_xboole_0(A_25, C_26) | ~r2_xboole_0(B_27, C_26) | ~r1_tarski(A_25, B_27))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.04/1.37  tff(c_51, plain, (![A_25, B_2, A_1]: (r2_xboole_0(A_25, B_2) | ~r1_tarski(A_25, A_1) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_2, c_48])).
% 2.04/1.37  tff(c_74, plain, (![B_37]: (r2_xboole_0('#skF_2', B_37) | B_37='#skF_3' | ~r1_tarski('#skF_3', B_37))), inference(resolution, [status(thm)], [c_63, c_51])).
% 2.04/1.37  tff(c_4, plain, (![B_2]: (~r2_xboole_0(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.04/1.37  tff(c_83, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_74, c_4])).
% 2.04/1.37  tff(c_88, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_67, c_83])).
% 2.04/1.37  tff(c_20, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.04/1.37  tff(c_95, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_20])).
% 2.04/1.37  tff(c_94, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_16])).
% 2.04/1.37  tff(c_14, plain, (![B_15, A_13]: (~m1_orders_2(B_15, A_13, B_15) | k1_xboole_0=B_15 | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_orders_2(A_13) | ~v5_orders_2(A_13) | ~v4_orders_2(A_13) | ~v3_orders_2(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.04/1.37  tff(c_109, plain, (k1_xboole_0='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_94, c_14])).
% 2.04/1.37  tff(c_116, plain, (k1_xboole_0='#skF_3' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_26, c_22, c_109])).
% 2.04/1.37  tff(c_118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_95, c_116])).
% 2.04/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.37  
% 2.04/1.37  Inference rules
% 2.04/1.37  ----------------------
% 2.04/1.37  #Ref     : 0
% 2.04/1.37  #Sup     : 15
% 2.04/1.37  #Fact    : 0
% 2.04/1.37  #Define  : 0
% 2.04/1.37  #Split   : 0
% 2.04/1.37  #Chain   : 0
% 2.04/1.37  #Close   : 0
% 2.04/1.37  
% 2.04/1.37  Ordering : KBO
% 2.04/1.37  
% 2.04/1.37  Simplification rules
% 2.04/1.37  ----------------------
% 2.04/1.37  #Subsume      : 3
% 2.04/1.37  #Demod        : 33
% 2.04/1.37  #Tautology    : 7
% 2.04/1.37  #SimpNegUnit  : 4
% 2.04/1.37  #BackRed      : 7
% 2.04/1.37  
% 2.04/1.37  #Partial instantiations: 0
% 2.04/1.37  #Strategies tried      : 1
% 2.04/1.37  
% 2.04/1.37  Timing (in seconds)
% 2.04/1.37  ----------------------
% 2.04/1.37  Preprocessing        : 0.33
% 2.04/1.37  Parsing              : 0.17
% 2.04/1.37  CNF conversion       : 0.02
% 2.04/1.37  Main loop            : 0.14
% 2.04/1.37  Inferencing          : 0.05
% 2.04/1.37  Reduction            : 0.05
% 2.04/1.37  Demodulation         : 0.03
% 2.04/1.37  BG Simplification    : 0.01
% 2.04/1.37  Subsumption          : 0.03
% 2.04/1.37  Abstraction          : 0.01
% 2.04/1.37  MUC search           : 0.00
% 2.04/1.37  Cooper               : 0.00
% 2.04/1.37  Total                : 0.51
% 2.04/1.37  Index Insertion      : 0.00
% 2.04/1.37  Index Deletion       : 0.00
% 2.04/1.37  Index Matching       : 0.00
% 2.04/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
