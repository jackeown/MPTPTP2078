%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:37 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   60 (  90 expanded)
%              Number of leaves         :   30 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :   90 ( 213 expanded)
%              Number of equality atoms :    5 (  15 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k1_enumset1 > k6_domain_1 > k2_tarski > k2_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k2_orders_2,type,(
    k2_orders_2: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ~ r2_hidden(B,k2_orders_2(A,k6_domain_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_orders_2)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ~ ( r2_hidden(B,C)
                  & r2_hidden(B,k2_orders_2(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_orders_2)).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_38,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_36,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_34,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_32,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_22,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_orders_2(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_85,plain,(
    ! [A_38,B_39] :
      ( k6_domain_1(A_38,B_39) = k1_tarski(B_39)
      | ~ m1_subset_1(B_39,A_38)
      | v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_89,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_85])).

tff(c_90,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_18,plain,(
    ! [A_11] :
      ( ~ v1_xboole_0(u1_struct_0(A_11))
      | ~ l1_struct_0(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_93,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_90,c_18])).

tff(c_96,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_93])).

tff(c_99,plain,(
    ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_96])).

tff(c_103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_99])).

tff(c_105,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_104,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2') ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_126,plain,(
    ! [A_45,B_46] :
      ( m1_subset_1(k6_domain_1(A_45,B_46),k1_zfmisc_1(A_45))
      | ~ m1_subset_1(B_46,A_45)
      | v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_134,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_126])).

tff(c_138,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_134])).

tff(c_139,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_138])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    ! [A_30,B_31] :
      ( r2_hidden(A_30,B_31)
      | ~ r1_tarski(k1_tarski(A_30),B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_67,plain,(
    ! [A_30] : r2_hidden(A_30,k1_tarski(A_30)) ),
    inference(resolution,[status(thm)],[c_6,c_62])).

tff(c_28,plain,(
    r2_hidden('#skF_2',k2_orders_2('#skF_1',k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_106,plain,(
    r2_hidden('#skF_2',k2_orders_2('#skF_1',k1_tarski('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_28])).

tff(c_225,plain,(
    ! [B_60,A_61,C_62] :
      ( ~ r2_hidden(B_60,k2_orders_2(A_61,C_62))
      | ~ r2_hidden(B_60,C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ m1_subset_1(B_60,u1_struct_0(A_61))
      | ~ l1_orders_2(A_61)
      | ~ v5_orders_2(A_61)
      | ~ v4_orders_2(A_61)
      | ~ v3_orders_2(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_227,plain,
    ( ~ r2_hidden('#skF_2',k1_tarski('#skF_2'))
    | ~ m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_106,c_225])).

tff(c_230,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_139,c_67,c_227])).

tff(c_232,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_230])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:58:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.31  
% 2.16/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.31  %$ r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k1_enumset1 > k6_domain_1 > k2_tarski > k2_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1
% 2.16/1.31  
% 2.16/1.31  %Foreground sorts:
% 2.16/1.31  
% 2.16/1.31  
% 2.16/1.31  %Background operators:
% 2.16/1.31  
% 2.16/1.31  
% 2.16/1.31  %Foreground operators:
% 2.16/1.31  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.16/1.31  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.16/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.16/1.31  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.16/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.16/1.31  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 2.16/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.16/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.16/1.31  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.16/1.31  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.16/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.16/1.31  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.16/1.31  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.16/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.16/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.16/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.16/1.31  
% 2.16/1.33  tff(f_111, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~r2_hidden(B, k2_orders_2(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_orders_2)).
% 2.16/1.33  tff(f_64, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.16/1.33  tff(f_71, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.16/1.33  tff(f_53, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.16/1.33  tff(f_60, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.16/1.33  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.16/1.33  tff(f_39, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.16/1.33  tff(f_93, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k2_orders_2(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_orders_2)).
% 2.16/1.33  tff(c_40, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.16/1.33  tff(c_38, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.16/1.33  tff(c_36, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.16/1.33  tff(c_34, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.16/1.33  tff(c_32, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.16/1.33  tff(c_30, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.16/1.33  tff(c_22, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_orders_2(A_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.16/1.33  tff(c_85, plain, (![A_38, B_39]: (k6_domain_1(A_38, B_39)=k1_tarski(B_39) | ~m1_subset_1(B_39, A_38) | v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.16/1.33  tff(c_89, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_85])).
% 2.16/1.33  tff(c_90, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_89])).
% 2.16/1.33  tff(c_18, plain, (![A_11]: (~v1_xboole_0(u1_struct_0(A_11)) | ~l1_struct_0(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.16/1.33  tff(c_93, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_90, c_18])).
% 2.16/1.33  tff(c_96, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_40, c_93])).
% 2.16/1.33  tff(c_99, plain, (~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_22, c_96])).
% 2.16/1.33  tff(c_103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_99])).
% 2.16/1.33  tff(c_105, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_89])).
% 2.16/1.33  tff(c_104, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2')), inference(splitRight, [status(thm)], [c_89])).
% 2.16/1.33  tff(c_126, plain, (![A_45, B_46]: (m1_subset_1(k6_domain_1(A_45, B_46), k1_zfmisc_1(A_45)) | ~m1_subset_1(B_46, A_45) | v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.16/1.33  tff(c_134, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_104, c_126])).
% 2.16/1.33  tff(c_138, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_134])).
% 2.16/1.33  tff(c_139, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_105, c_138])).
% 2.16/1.33  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.16/1.33  tff(c_62, plain, (![A_30, B_31]: (r2_hidden(A_30, B_31) | ~r1_tarski(k1_tarski(A_30), B_31))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.16/1.33  tff(c_67, plain, (![A_30]: (r2_hidden(A_30, k1_tarski(A_30)))), inference(resolution, [status(thm)], [c_6, c_62])).
% 2.16/1.33  tff(c_28, plain, (r2_hidden('#skF_2', k2_orders_2('#skF_1', k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.16/1.33  tff(c_106, plain, (r2_hidden('#skF_2', k2_orders_2('#skF_1', k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_28])).
% 2.16/1.33  tff(c_225, plain, (![B_60, A_61, C_62]: (~r2_hidden(B_60, k2_orders_2(A_61, C_62)) | ~r2_hidden(B_60, C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~m1_subset_1(B_60, u1_struct_0(A_61)) | ~l1_orders_2(A_61) | ~v5_orders_2(A_61) | ~v4_orders_2(A_61) | ~v3_orders_2(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.16/1.33  tff(c_227, plain, (~r2_hidden('#skF_2', k1_tarski('#skF_2')) | ~m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_106, c_225])).
% 2.16/1.33  tff(c_230, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_30, c_139, c_67, c_227])).
% 2.16/1.33  tff(c_232, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_230])).
% 2.16/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.33  
% 2.16/1.33  Inference rules
% 2.16/1.33  ----------------------
% 2.16/1.33  #Ref     : 0
% 2.16/1.33  #Sup     : 38
% 2.16/1.33  #Fact    : 0
% 2.16/1.33  #Define  : 0
% 2.16/1.33  #Split   : 2
% 2.16/1.33  #Chain   : 0
% 2.16/1.33  #Close   : 0
% 2.16/1.33  
% 2.16/1.33  Ordering : KBO
% 2.16/1.33  
% 2.16/1.33  Simplification rules
% 2.16/1.33  ----------------------
% 2.16/1.33  #Subsume      : 2
% 2.16/1.33  #Demod        : 28
% 2.16/1.33  #Tautology    : 17
% 2.16/1.33  #SimpNegUnit  : 7
% 2.16/1.33  #BackRed      : 1
% 2.16/1.33  
% 2.16/1.33  #Partial instantiations: 0
% 2.16/1.33  #Strategies tried      : 1
% 2.16/1.33  
% 2.16/1.33  Timing (in seconds)
% 2.16/1.33  ----------------------
% 2.16/1.33  Preprocessing        : 0.33
% 2.16/1.33  Parsing              : 0.18
% 2.16/1.33  CNF conversion       : 0.02
% 2.16/1.33  Main loop            : 0.20
% 2.16/1.33  Inferencing          : 0.07
% 2.16/1.33  Reduction            : 0.06
% 2.16/1.33  Demodulation         : 0.04
% 2.16/1.33  BG Simplification    : 0.01
% 2.16/1.33  Subsumption          : 0.03
% 2.16/1.33  Abstraction          : 0.01
% 2.16/1.33  MUC search           : 0.00
% 2.16/1.33  Cooper               : 0.00
% 2.16/1.33  Total                : 0.56
% 2.16/1.33  Index Insertion      : 0.00
% 2.16/1.33  Index Deletion       : 0.00
% 2.16/1.33  Index Matching       : 0.00
% 2.16/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
