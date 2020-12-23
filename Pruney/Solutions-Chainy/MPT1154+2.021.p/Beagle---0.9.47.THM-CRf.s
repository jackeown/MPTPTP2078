%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:35 EST 2020

% Result     : Theorem 4.60s
% Output     : CNFRefutation 4.83s
% Verified   : 
% Statistics : Number of formulae       :   63 (  87 expanded)
%              Number of leaves         :   31 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :   93 ( 199 expanded)
%              Number of equality atoms :    9 (  15 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(k1_orders_2,type,(
    k1_orders_2: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

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
           => ~ r2_hidden(B,k1_orders_2(A,k6_domain_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_orders_2)).

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

tff(f_60,axiom,(
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

tff(f_40,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

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
                  & r2_hidden(B,k1_orders_2(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_orders_2)).

tff(c_40,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_30,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_orders_2(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_103,plain,(
    ! [A_46,B_47] :
      ( k6_domain_1(A_46,B_47) = k1_tarski(B_47)
      | ~ m1_subset_1(B_47,A_46)
      | v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_111,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_103])).

tff(c_112,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_111])).

tff(c_28,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0(u1_struct_0(A_15))
      | ~ l1_struct_0(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_115,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_112,c_28])).

tff(c_118,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_115])).

tff(c_121,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_118])).

tff(c_125,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_121])).

tff(c_127,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_24,plain,(
    ! [A_10,B_11] :
      ( r2_hidden(A_10,B_11)
      | v1_xboole_0(B_11)
      | ~ m1_subset_1(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_22,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(k1_tarski(A_8),k1_zfmisc_1(B_9))
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_46,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_44,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_42,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_59,plain,(
    ! [D_29,B_30] : r2_hidden(D_29,k2_tarski(D_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_62,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_59])).

tff(c_126,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_36,plain,(
    r2_hidden('#skF_4',k1_orders_2('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_128,plain,(
    r2_hidden('#skF_4',k1_orders_2('#skF_3',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_36])).

tff(c_2429,plain,(
    ! [B_2715,A_2716,C_2717] :
      ( ~ r2_hidden(B_2715,k1_orders_2(A_2716,C_2717))
      | ~ r2_hidden(B_2715,C_2717)
      | ~ m1_subset_1(C_2717,k1_zfmisc_1(u1_struct_0(A_2716)))
      | ~ m1_subset_1(B_2715,u1_struct_0(A_2716))
      | ~ l1_orders_2(A_2716)
      | ~ v5_orders_2(A_2716)
      | ~ v4_orders_2(A_2716)
      | ~ v3_orders_2(A_2716)
      | v2_struct_0(A_2716) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2437,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_128,c_2429])).

tff(c_2444,plain,
    ( ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_62,c_2437])).

tff(c_2445,plain,(
    ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_2444])).

tff(c_2459,plain,(
    ~ r2_hidden('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_2445])).

tff(c_2463,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_2459])).

tff(c_2466,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2463])).

tff(c_2468,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_2466])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:06:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.60/2.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.60/2.65  
% 4.60/2.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.60/2.66  %$ r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_domain_1 > k2_tarski > k1_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 4.60/2.66  
% 4.60/2.66  %Foreground sorts:
% 4.60/2.66  
% 4.60/2.66  
% 4.60/2.66  %Background operators:
% 4.60/2.66  
% 4.60/2.66  
% 4.60/2.66  %Foreground operators:
% 4.60/2.66  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.60/2.66  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.60/2.66  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.60/2.66  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 4.60/2.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.60/2.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.60/2.66  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.60/2.66  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.60/2.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.60/2.66  tff('#skF_3', type, '#skF_3': $i).
% 4.60/2.66  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.60/2.66  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.60/2.66  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.60/2.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.60/2.66  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.60/2.66  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.60/2.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.60/2.66  tff('#skF_4', type, '#skF_4': $i).
% 4.60/2.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.60/2.66  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.60/2.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.60/2.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.60/2.66  
% 4.83/2.68  tff(f_111, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~r2_hidden(B, k1_orders_2(A, k6_domain_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_orders_2)).
% 4.83/2.68  tff(f_64, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 4.83/2.68  tff(f_71, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.83/2.68  tff(f_60, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.83/2.68  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.83/2.68  tff(f_40, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 4.83/2.68  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.83/2.68  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 4.83/2.68  tff(f_93, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r2_hidden(B, C) & r2_hidden(B, k1_orders_2(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_orders_2)).
% 4.83/2.68  tff(c_40, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.83/2.68  tff(c_30, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_orders_2(A_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.83/2.68  tff(c_48, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.83/2.68  tff(c_38, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.83/2.68  tff(c_103, plain, (![A_46, B_47]: (k6_domain_1(A_46, B_47)=k1_tarski(B_47) | ~m1_subset_1(B_47, A_46) | v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.83/2.68  tff(c_111, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_103])).
% 4.83/2.68  tff(c_112, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_111])).
% 4.83/2.68  tff(c_28, plain, (![A_15]: (~v1_xboole_0(u1_struct_0(A_15)) | ~l1_struct_0(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.83/2.68  tff(c_115, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_112, c_28])).
% 4.83/2.68  tff(c_118, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_48, c_115])).
% 4.83/2.68  tff(c_121, plain, (~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_30, c_118])).
% 4.83/2.68  tff(c_125, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_121])).
% 4.83/2.68  tff(c_127, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_111])).
% 4.83/2.68  tff(c_24, plain, (![A_10, B_11]: (r2_hidden(A_10, B_11) | v1_xboole_0(B_11) | ~m1_subset_1(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.83/2.68  tff(c_22, plain, (![A_8, B_9]: (m1_subset_1(k1_tarski(A_8), k1_zfmisc_1(B_9)) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.83/2.68  tff(c_46, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.83/2.68  tff(c_44, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.83/2.68  tff(c_42, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.83/2.68  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.83/2.68  tff(c_59, plain, (![D_29, B_30]: (r2_hidden(D_29, k2_tarski(D_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.83/2.68  tff(c_62, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_59])).
% 4.83/2.68  tff(c_126, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_111])).
% 4.83/2.68  tff(c_36, plain, (r2_hidden('#skF_4', k1_orders_2('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.83/2.68  tff(c_128, plain, (r2_hidden('#skF_4', k1_orders_2('#skF_3', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_36])).
% 4.83/2.68  tff(c_2429, plain, (![B_2715, A_2716, C_2717]: (~r2_hidden(B_2715, k1_orders_2(A_2716, C_2717)) | ~r2_hidden(B_2715, C_2717) | ~m1_subset_1(C_2717, k1_zfmisc_1(u1_struct_0(A_2716))) | ~m1_subset_1(B_2715, u1_struct_0(A_2716)) | ~l1_orders_2(A_2716) | ~v5_orders_2(A_2716) | ~v4_orders_2(A_2716) | ~v3_orders_2(A_2716) | v2_struct_0(A_2716))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.83/2.68  tff(c_2437, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_128, c_2429])).
% 4.83/2.68  tff(c_2444, plain, (~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_62, c_2437])).
% 4.83/2.68  tff(c_2445, plain, (~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_48, c_2444])).
% 4.83/2.68  tff(c_2459, plain, (~r2_hidden('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_2445])).
% 4.83/2.68  tff(c_2463, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_24, c_2459])).
% 4.83/2.68  tff(c_2466, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2463])).
% 4.83/2.68  tff(c_2468, plain, $false, inference(negUnitSimplification, [status(thm)], [c_127, c_2466])).
% 4.83/2.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.83/2.68  
% 4.83/2.68  Inference rules
% 4.83/2.68  ----------------------
% 4.83/2.68  #Ref     : 0
% 4.83/2.68  #Sup     : 279
% 4.83/2.68  #Fact    : 4
% 4.83/2.68  #Define  : 0
% 4.83/2.68  #Split   : 7
% 4.83/2.68  #Chain   : 0
% 4.83/2.68  #Close   : 0
% 4.83/2.68  
% 4.83/2.68  Ordering : KBO
% 4.83/2.68  
% 4.83/2.68  Simplification rules
% 4.83/2.68  ----------------------
% 4.83/2.68  #Subsume      : 49
% 4.83/2.68  #Demod        : 54
% 4.83/2.68  #Tautology    : 72
% 4.83/2.68  #SimpNegUnit  : 3
% 4.83/2.68  #BackRed      : 1
% 4.83/2.68  
% 4.83/2.68  #Partial instantiations: 1830
% 4.83/2.68  #Strategies tried      : 1
% 4.83/2.68  
% 4.83/2.68  Timing (in seconds)
% 4.83/2.68  ----------------------
% 4.83/2.68  Preprocessing        : 0.60
% 4.83/2.68  Parsing              : 0.32
% 4.83/2.68  CNF conversion       : 0.04
% 4.83/2.68  Main loop            : 1.14
% 4.83/2.68  Inferencing          : 0.60
% 4.83/2.68  Reduction            : 0.25
% 4.83/2.68  Demodulation         : 0.18
% 4.83/2.68  BG Simplification    : 0.06
% 4.83/2.68  Subsumption          : 0.17
% 4.83/2.68  Abstraction          : 0.05
% 4.83/2.68  MUC search           : 0.00
% 4.83/2.68  Cooper               : 0.00
% 4.83/2.68  Total                : 1.79
% 4.83/2.68  Index Insertion      : 0.00
% 4.83/2.68  Index Deletion       : 0.00
% 4.83/2.68  Index Matching       : 0.00
% 4.83/2.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
