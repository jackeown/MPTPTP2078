%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:22 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   47 (  59 expanded)
%              Number of leaves         :   22 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   70 ( 133 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_orders_2 > r7_relat_2 > r1_tarski > m1_subset_1 > v1_relat_1 > l1_orders_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(r7_relat_2,type,(
    r7_relat_2: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( ( v6_orders_2(B,A)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r1_tarski(C,B)
                 => ( v6_orders_2(C,A)
                    & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_orders_2)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_orders_2(B,A)
          <=> r7_relat_2(u1_orders_2(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_orders_2)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r7_relat_2(C,A)
          & r1_tarski(B,A) )
       => r7_relat_2(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_orders_1)).

tff(c_24,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_44,plain,(
    ! [A_25] :
      ( m1_subset_1(u1_orders_2(A_25),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_25),u1_struct_0(A_25))))
      | ~ l1_orders_2(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_47,plain,(
    ! [A_25] :
      ( v1_relat_1(u1_orders_2(A_25))
      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(A_25),u1_struct_0(A_25)))
      | ~ l1_orders_2(A_25) ) ),
    inference(resolution,[status(thm)],[c_44,c_2])).

tff(c_50,plain,(
    ! [A_25] :
      ( v1_relat_1(u1_orders_2(A_25))
      | ~ l1_orders_2(A_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_47])).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_14,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v6_orders_2('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    ~ v6_orders_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_14])).

tff(c_51,plain,(
    ! [B_26,A_27] :
      ( v6_orders_2(B_26,A_27)
      | ~ r7_relat_2(u1_orders_2(A_27),B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_57,plain,
    ( v6_orders_2('#skF_3','#skF_1')
    | ~ r7_relat_2(u1_orders_2('#skF_1'),'#skF_3')
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_51])).

tff(c_63,plain,
    ( v6_orders_2('#skF_3','#skF_1')
    | ~ r7_relat_2(u1_orders_2('#skF_1'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_57])).

tff(c_64,plain,(
    ~ r7_relat_2(u1_orders_2('#skF_1'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_63])).

tff(c_22,plain,(
    v6_orders_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_66,plain,(
    ! [A_29,B_30] :
      ( r7_relat_2(u1_orders_2(A_29),B_30)
      | ~ v6_orders_2(B_30,A_29)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_orders_2(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_69,plain,
    ( r7_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ v6_orders_2('#skF_2','#skF_1')
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_66])).

tff(c_75,plain,(
    r7_relat_2(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_69])).

tff(c_16,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_39,plain,(
    ! [C_21,B_22,A_23] :
      ( r7_relat_2(C_21,B_22)
      | ~ r1_tarski(B_22,A_23)
      | ~ r7_relat_2(C_21,A_23)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_42,plain,(
    ! [C_21] :
      ( r7_relat_2(C_21,'#skF_3')
      | ~ r7_relat_2(C_21,'#skF_2')
      | ~ v1_relat_1(C_21) ) ),
    inference(resolution,[status(thm)],[c_16,c_39])).

tff(c_82,plain,
    ( r7_relat_2(u1_orders_2('#skF_1'),'#skF_3')
    | ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(resolution,[status(thm)],[c_75,c_42])).

tff(c_85,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_82])).

tff(c_88,plain,(
    ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_85])).

tff(c_92,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_88])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:01:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.22  
% 1.96/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.22  %$ v6_orders_2 > r7_relat_2 > r1_tarski > m1_subset_1 > v1_relat_1 > l1_orders_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.96/1.22  
% 1.96/1.22  %Foreground sorts:
% 1.96/1.22  
% 1.96/1.22  
% 1.96/1.22  %Background operators:
% 1.96/1.22  
% 1.96/1.22  
% 1.96/1.22  %Foreground operators:
% 1.96/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.96/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.96/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.96/1.22  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.96/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.96/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.96/1.22  tff(r7_relat_2, type, r7_relat_2: ($i * $i) > $o).
% 1.96/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.22  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 1.96/1.22  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 1.96/1.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.96/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.96/1.22  
% 1.96/1.23  tff(f_72, negated_conjecture, ~(![A]: (l1_orders_2(A) => (![B]: ((v6_orders_2(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_orders_2)).
% 1.96/1.23  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.96/1.23  tff(f_47, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 1.96/1.23  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.96/1.23  tff(f_43, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_orders_2(B, A) <=> r7_relat_2(u1_orders_2(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_orders_2)).
% 1.96/1.23  tff(f_55, axiom, (![A, B, C]: (v1_relat_1(C) => ((r7_relat_2(C, A) & r1_tarski(B, A)) => r7_relat_2(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_orders_1)).
% 1.96/1.23  tff(c_24, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.96/1.23  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.96/1.23  tff(c_44, plain, (![A_25]: (m1_subset_1(u1_orders_2(A_25), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_25), u1_struct_0(A_25)))) | ~l1_orders_2(A_25))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.96/1.23  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.96/1.23  tff(c_47, plain, (![A_25]: (v1_relat_1(u1_orders_2(A_25)) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(A_25), u1_struct_0(A_25))) | ~l1_orders_2(A_25))), inference(resolution, [status(thm)], [c_44, c_2])).
% 1.96/1.23  tff(c_50, plain, (![A_25]: (v1_relat_1(u1_orders_2(A_25)) | ~l1_orders_2(A_25))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_47])).
% 1.96/1.23  tff(c_18, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.96/1.23  tff(c_14, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v6_orders_2('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.96/1.23  tff(c_26, plain, (~v6_orders_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_14])).
% 1.96/1.23  tff(c_51, plain, (![B_26, A_27]: (v6_orders_2(B_26, A_27) | ~r7_relat_2(u1_orders_2(A_27), B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_orders_2(A_27))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.96/1.23  tff(c_57, plain, (v6_orders_2('#skF_3', '#skF_1') | ~r7_relat_2(u1_orders_2('#skF_1'), '#skF_3') | ~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_18, c_51])).
% 1.96/1.23  tff(c_63, plain, (v6_orders_2('#skF_3', '#skF_1') | ~r7_relat_2(u1_orders_2('#skF_1'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_57])).
% 1.96/1.23  tff(c_64, plain, (~r7_relat_2(u1_orders_2('#skF_1'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_26, c_63])).
% 1.96/1.23  tff(c_22, plain, (v6_orders_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.96/1.23  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.96/1.23  tff(c_66, plain, (![A_29, B_30]: (r7_relat_2(u1_orders_2(A_29), B_30) | ~v6_orders_2(B_30, A_29) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_orders_2(A_29))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.96/1.23  tff(c_69, plain, (r7_relat_2(u1_orders_2('#skF_1'), '#skF_2') | ~v6_orders_2('#skF_2', '#skF_1') | ~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_20, c_66])).
% 1.96/1.23  tff(c_75, plain, (r7_relat_2(u1_orders_2('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_69])).
% 1.96/1.23  tff(c_16, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.96/1.23  tff(c_39, plain, (![C_21, B_22, A_23]: (r7_relat_2(C_21, B_22) | ~r1_tarski(B_22, A_23) | ~r7_relat_2(C_21, A_23) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.96/1.23  tff(c_42, plain, (![C_21]: (r7_relat_2(C_21, '#skF_3') | ~r7_relat_2(C_21, '#skF_2') | ~v1_relat_1(C_21))), inference(resolution, [status(thm)], [c_16, c_39])).
% 1.96/1.23  tff(c_82, plain, (r7_relat_2(u1_orders_2('#skF_1'), '#skF_3') | ~v1_relat_1(u1_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_75, c_42])).
% 1.96/1.23  tff(c_85, plain, (~v1_relat_1(u1_orders_2('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_64, c_82])).
% 1.96/1.23  tff(c_88, plain, (~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_50, c_85])).
% 1.96/1.23  tff(c_92, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_88])).
% 1.96/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.23  
% 1.96/1.23  Inference rules
% 1.96/1.23  ----------------------
% 1.96/1.23  #Ref     : 0
% 1.96/1.23  #Sup     : 10
% 1.96/1.23  #Fact    : 0
% 1.96/1.23  #Define  : 0
% 1.96/1.23  #Split   : 2
% 1.96/1.23  #Chain   : 0
% 1.96/1.23  #Close   : 0
% 1.96/1.23  
% 1.96/1.23  Ordering : KBO
% 1.96/1.23  
% 1.96/1.23  Simplification rules
% 1.96/1.23  ----------------------
% 1.96/1.23  #Subsume      : 2
% 1.96/1.23  #Demod        : 9
% 1.96/1.23  #Tautology    : 1
% 1.96/1.23  #SimpNegUnit  : 3
% 1.96/1.23  #BackRed      : 0
% 1.96/1.23  
% 1.96/1.23  #Partial instantiations: 0
% 1.96/1.23  #Strategies tried      : 1
% 1.96/1.23  
% 1.96/1.23  Timing (in seconds)
% 1.96/1.23  ----------------------
% 2.05/1.23  Preprocessing        : 0.26
% 2.05/1.23  Parsing              : 0.14
% 2.05/1.23  CNF conversion       : 0.02
% 2.05/1.23  Main loop            : 0.12
% 2.05/1.23  Inferencing          : 0.05
% 2.05/1.23  Reduction            : 0.03
% 2.05/1.23  Demodulation         : 0.03
% 2.05/1.23  BG Simplification    : 0.01
% 2.05/1.23  Subsumption          : 0.02
% 2.05/1.23  Abstraction          : 0.00
% 2.05/1.23  MUC search           : 0.00
% 2.05/1.23  Cooper               : 0.00
% 2.05/1.23  Total                : 0.41
% 2.05/1.23  Index Insertion      : 0.00
% 2.05/1.23  Index Deletion       : 0.00
% 2.05/1.23  Index Matching       : 0.00
% 2.05/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
