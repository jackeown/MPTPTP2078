%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:50 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 137 expanded)
%              Number of leaves         :   23 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :  105 ( 574 expanded)
%              Number of equality atoms :   12 (  53 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_orders_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r2_xboole_0(A,B)
        & r1_tarski(B,C) )
     => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_xboole_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_orders_2)).

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

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_18,plain,(
    m1_orders_2('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_51,plain,(
    ! [C_31,B_32,A_33] :
      ( r1_tarski(C_31,B_32)
      | ~ m1_orders_2(C_31,A_33,B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_orders_2(A_33)
      | ~ v5_orders_2(A_33)
      | ~ v4_orders_2(A_33)
      | ~ v3_orders_2(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_53,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_51])).

tff(c_58,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_26,c_22,c_53])).

tff(c_59,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_58])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_xboole_0(A_1,B_2)
      | B_2 = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_16,plain,(
    m1_orders_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_55,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_51])).

tff(c_62,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_26,c_24,c_55])).

tff(c_63,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_62])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r2_xboole_0(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r2_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_76,plain,(
    ! [A_35] :
      ( r2_xboole_0(A_35,'#skF_2')
      | ~ r2_xboole_0(A_35,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_63,c_8])).

tff(c_4,plain,(
    ! [B_2] : ~ r2_xboole_0(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_89,plain,(
    ~ r2_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_4])).

tff(c_92,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_89])).

tff(c_95,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_92])).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_104,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_20])).

tff(c_102,plain,(
    m1_orders_2('#skF_3','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_18])).

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

tff(c_118,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_102,c_14])).

tff(c_125,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_26,c_22,c_118])).

tff(c_127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_104,c_125])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.06/0.25  % Computer   : n012.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % DateTime   : Tue Dec  1 17:10:07 EST 2020
% 0.06/0.25  % CPUTime    : 
% 0.06/0.26  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.03  
% 1.92/1.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.03  %$ m1_orders_2 > r2_xboole_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.92/1.03  
% 1.92/1.03  %Foreground sorts:
% 1.92/1.03  
% 1.92/1.03  
% 1.92/1.03  %Background operators:
% 1.92/1.03  
% 1.92/1.03  
% 1.92/1.03  %Foreground operators:
% 1.92/1.03  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.92/1.03  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 1.92/1.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.92/1.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.92/1.03  tff('#skF_2', type, '#skF_2': $i).
% 1.92/1.03  tff('#skF_3', type, '#skF_3': $i).
% 1.92/1.03  tff('#skF_1', type, '#skF_1': $i).
% 1.92/1.03  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 1.92/1.03  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 1.92/1.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.92/1.03  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.92/1.03  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.92/1.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.03  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 1.92/1.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.03  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.92/1.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.92/1.03  
% 1.92/1.04  tff(f_109, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_orders_2)).
% 1.92/1.04  tff(f_57, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_orders_2)).
% 1.92/1.04  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.92/1.04  tff(f_38, axiom, (![A, B, C]: ((r2_xboole_0(A, B) & r1_tarski(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_xboole_1)).
% 1.92/1.04  tff(f_83, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (~(~(B = k1_xboole_0) & m1_orders_2(B, A, B)) & ~(~m1_orders_2(B, A, B) & (B = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_orders_2)).
% 1.92/1.04  tff(c_34, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 1.92/1.04  tff(c_32, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 1.92/1.04  tff(c_30, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 1.92/1.04  tff(c_28, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 1.92/1.04  tff(c_26, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 1.92/1.04  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 1.92/1.04  tff(c_18, plain, (m1_orders_2('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 1.92/1.04  tff(c_51, plain, (![C_31, B_32, A_33]: (r1_tarski(C_31, B_32) | ~m1_orders_2(C_31, A_33, B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_orders_2(A_33) | ~v5_orders_2(A_33) | ~v4_orders_2(A_33) | ~v3_orders_2(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.92/1.04  tff(c_53, plain, (r1_tarski('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_51])).
% 1.92/1.04  tff(c_58, plain, (r1_tarski('#skF_2', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_26, c_22, c_53])).
% 1.92/1.04  tff(c_59, plain, (r1_tarski('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_34, c_58])).
% 1.92/1.04  tff(c_2, plain, (![A_1, B_2]: (r2_xboole_0(A_1, B_2) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.92/1.04  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 1.92/1.04  tff(c_16, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 1.92/1.04  tff(c_55, plain, (r1_tarski('#skF_3', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_51])).
% 1.92/1.04  tff(c_62, plain, (r1_tarski('#skF_3', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_26, c_24, c_55])).
% 1.92/1.04  tff(c_63, plain, (r1_tarski('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_34, c_62])).
% 1.92/1.04  tff(c_8, plain, (![A_3, C_5, B_4]: (r2_xboole_0(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.92/1.04  tff(c_76, plain, (![A_35]: (r2_xboole_0(A_35, '#skF_2') | ~r2_xboole_0(A_35, '#skF_3'))), inference(resolution, [status(thm)], [c_63, c_8])).
% 1.92/1.04  tff(c_4, plain, (![B_2]: (~r2_xboole_0(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.92/1.04  tff(c_89, plain, (~r2_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_76, c_4])).
% 1.92/1.04  tff(c_92, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_2, c_89])).
% 1.92/1.04  tff(c_95, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_59, c_92])).
% 1.92/1.04  tff(c_20, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_109])).
% 1.92/1.04  tff(c_104, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_95, c_20])).
% 1.92/1.04  tff(c_102, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_18])).
% 1.92/1.04  tff(c_14, plain, (![B_15, A_13]: (~m1_orders_2(B_15, A_13, B_15) | k1_xboole_0=B_15 | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_orders_2(A_13) | ~v5_orders_2(A_13) | ~v4_orders_2(A_13) | ~v3_orders_2(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.92/1.04  tff(c_118, plain, (k1_xboole_0='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_102, c_14])).
% 1.92/1.04  tff(c_125, plain, (k1_xboole_0='#skF_3' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_26, c_22, c_118])).
% 1.92/1.04  tff(c_127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_104, c_125])).
% 1.92/1.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.04  
% 1.92/1.04  Inference rules
% 1.92/1.04  ----------------------
% 1.92/1.04  #Ref     : 0
% 1.92/1.04  #Sup     : 16
% 1.92/1.04  #Fact    : 0
% 1.92/1.04  #Define  : 0
% 1.92/1.04  #Split   : 0
% 1.92/1.04  #Chain   : 0
% 1.92/1.04  #Close   : 0
% 1.92/1.04  
% 1.92/1.04  Ordering : KBO
% 1.92/1.04  
% 1.92/1.04  Simplification rules
% 1.92/1.04  ----------------------
% 1.92/1.04  #Subsume      : 2
% 1.92/1.04  #Demod        : 34
% 1.92/1.04  #Tautology    : 11
% 1.92/1.04  #SimpNegUnit  : 4
% 1.92/1.04  #BackRed      : 7
% 1.92/1.04  
% 1.92/1.04  #Partial instantiations: 0
% 1.92/1.04  #Strategies tried      : 1
% 1.92/1.04  
% 1.92/1.04  Timing (in seconds)
% 1.92/1.04  ----------------------
% 1.92/1.05  Preprocessing        : 0.31
% 1.92/1.05  Parsing              : 0.17
% 1.92/1.05  CNF conversion       : 0.02
% 1.92/1.05  Main loop            : 0.14
% 1.92/1.05  Inferencing          : 0.05
% 1.92/1.05  Reduction            : 0.04
% 1.92/1.05  Demodulation         : 0.03
% 1.92/1.05  BG Simplification    : 0.01
% 1.92/1.05  Subsumption          : 0.02
% 1.92/1.05  Abstraction          : 0.01
% 1.92/1.05  MUC search           : 0.00
% 1.92/1.05  Cooper               : 0.00
% 1.92/1.05  Total                : 0.47
% 1.92/1.05  Index Insertion      : 0.00
% 1.92/1.05  Index Deletion       : 0.00
% 1.92/1.05  Index Matching       : 0.00
% 1.92/1.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
