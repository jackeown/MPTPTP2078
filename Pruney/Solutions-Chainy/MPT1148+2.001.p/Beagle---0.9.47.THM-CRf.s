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
% DateTime   : Thu Dec  3 10:19:23 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   53 (  83 expanded)
%              Number of leaves         :   26 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :   75 ( 184 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_orders_2 > r8_relat_2 > r7_relat_2 > r6_relat_2 > r4_relat_2 > r2_wellord1 > r1_wellord1 > r1_relat_2 > m1_subset_1 > v1_relat_1 > l1_orders_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r4_relat_2,type,(
    r4_relat_2: ( $i * $i ) > $o )).

tff(r1_wellord1,type,(
    r1_wellord1: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r6_relat_2,type,(
    r6_relat_2: ( $i * $i ) > $o )).

tff(r1_relat_2,type,(
    r1_relat_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_wellord1,type,(
    r2_wellord1: ( $i * $i ) > $o )).

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

tff(r8_relat_2,type,(
    r8_relat_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( r2_wellord1(u1_orders_2(A),B)
             => ( v6_orders_2(B,A)
                & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_orders_2)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r2_wellord1(A,B)
        <=> ( r1_relat_2(A,B)
            & r8_relat_2(A,B)
            & r4_relat_2(A,B)
            & r6_relat_2(A,B)
            & r1_wellord1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_wellord1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r7_relat_2(B,A)
      <=> ( r1_relat_2(B,A)
          & r6_relat_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_orders_1)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_orders_2(B,A)
          <=> r7_relat_2(u1_orders_2(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_orders_2)).

tff(c_34,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_63,plain,(
    ! [A_33] :
      ( m1_subset_1(u1_orders_2(A_33),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_33),u1_struct_0(A_33))))
      | ~ l1_orders_2(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_14,plain,(
    ! [C_6,A_4,B_5] :
      ( v1_relat_1(C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(A_4,B_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_68,plain,(
    ! [A_34] :
      ( v1_relat_1(u1_orders_2(A_34))
      | ~ l1_orders_2(A_34) ) ),
    inference(resolution,[status(thm)],[c_63,c_14])).

tff(c_30,plain,(
    r2_wellord1(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_40,plain,(
    ! [A_20,B_21] :
      ( r1_wellord1(A_20,B_21)
      | ~ r2_wellord1(A_20,B_21)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_44,plain,
    ( r1_wellord1(u1_orders_2('#skF_1'),'#skF_2')
    | ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_40])).

tff(c_45,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_71,plain,(
    ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_45])).

tff(c_75,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_71])).

tff(c_77,plain,(
    v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_6,plain,(
    ! [A_1,B_3] :
      ( r6_relat_2(A_1,B_3)
      | ~ r2_wellord1(A_1,B_3)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_79,plain,(
    ! [A_38,B_39] :
      ( r1_relat_2(A_38,B_39)
      | ~ r2_wellord1(A_38,B_39)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_82,plain,
    ( r1_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_79])).

tff(c_85,plain,(
    r1_relat_2(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_82])).

tff(c_22,plain,(
    ! [B_12,A_11] :
      ( r7_relat_2(B_12,A_11)
      | ~ r6_relat_2(B_12,A_11)
      | ~ r1_relat_2(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_28,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v6_orders_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_36,plain,(
    ~ v6_orders_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28])).

tff(c_110,plain,(
    ! [B_50,A_51] :
      ( v6_orders_2(B_50,A_51)
      | ~ r7_relat_2(u1_orders_2(A_51),B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_orders_2(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_113,plain,
    ( v6_orders_2('#skF_2','#skF_1')
    | ~ r7_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_110])).

tff(c_116,plain,
    ( v6_orders_2('#skF_2','#skF_1')
    | ~ r7_relat_2(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_113])).

tff(c_117,plain,(
    ~ r7_relat_2(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_116])).

tff(c_120,plain,
    ( ~ r6_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ r1_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(resolution,[status(thm)],[c_22,c_117])).

tff(c_123,plain,(
    ~ r6_relat_2(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_85,c_120])).

tff(c_126,plain,
    ( ~ r2_wellord1(u1_orders_2('#skF_1'),'#skF_2')
    | ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_123])).

tff(c_130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_30,c_126])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:23:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.29  
% 1.98/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.29  %$ v6_orders_2 > r8_relat_2 > r7_relat_2 > r6_relat_2 > r4_relat_2 > r2_wellord1 > r1_wellord1 > r1_relat_2 > m1_subset_1 > v1_relat_1 > l1_orders_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.98/1.29  
% 1.98/1.29  %Foreground sorts:
% 1.98/1.29  
% 1.98/1.29  
% 1.98/1.29  %Background operators:
% 1.98/1.29  
% 1.98/1.29  
% 1.98/1.29  %Foreground operators:
% 1.98/1.29  tff(r4_relat_2, type, r4_relat_2: ($i * $i) > $o).
% 1.98/1.29  tff(r1_wellord1, type, r1_wellord1: ($i * $i) > $o).
% 1.98/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.29  tff(r6_relat_2, type, r6_relat_2: ($i * $i) > $o).
% 1.98/1.29  tff(r1_relat_2, type, r1_relat_2: ($i * $i) > $o).
% 1.98/1.29  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.29  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.98/1.29  tff(r2_wellord1, type, r2_wellord1: ($i * $i) > $o).
% 1.98/1.29  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.98/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.98/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.98/1.29  tff(r7_relat_2, type, r7_relat_2: ($i * $i) > $o).
% 1.98/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.29  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 1.98/1.29  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 1.98/1.29  tff(r8_relat_2, type, r8_relat_2: ($i * $i) > $o).
% 1.98/1.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.98/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.98/1.29  
% 1.98/1.31  tff(f_77, negated_conjecture, ~(![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_wellord1(u1_orders_2(A), B) => (v6_orders_2(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_orders_2)).
% 1.98/1.31  tff(f_57, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 1.98/1.31  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.98/1.31  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (r2_wellord1(A, B) <=> ((((r1_relat_2(A, B) & r8_relat_2(A, B)) & r4_relat_2(A, B)) & r6_relat_2(A, B)) & r1_wellord1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_wellord1)).
% 1.98/1.31  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (r7_relat_2(B, A) <=> (r1_relat_2(B, A) & r6_relat_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_orders_1)).
% 1.98/1.31  tff(f_53, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_orders_2(B, A) <=> r7_relat_2(u1_orders_2(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_orders_2)).
% 1.98/1.31  tff(c_34, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.98/1.31  tff(c_63, plain, (![A_33]: (m1_subset_1(u1_orders_2(A_33), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_33), u1_struct_0(A_33)))) | ~l1_orders_2(A_33))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.98/1.31  tff(c_14, plain, (![C_6, A_4, B_5]: (v1_relat_1(C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1(A_4, B_5))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.98/1.31  tff(c_68, plain, (![A_34]: (v1_relat_1(u1_orders_2(A_34)) | ~l1_orders_2(A_34))), inference(resolution, [status(thm)], [c_63, c_14])).
% 1.98/1.31  tff(c_30, plain, (r2_wellord1(u1_orders_2('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.98/1.31  tff(c_40, plain, (![A_20, B_21]: (r1_wellord1(A_20, B_21) | ~r2_wellord1(A_20, B_21) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.98/1.31  tff(c_44, plain, (r1_wellord1(u1_orders_2('#skF_1'), '#skF_2') | ~v1_relat_1(u1_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_40])).
% 1.98/1.31  tff(c_45, plain, (~v1_relat_1(u1_orders_2('#skF_1'))), inference(splitLeft, [status(thm)], [c_44])).
% 1.98/1.31  tff(c_71, plain, (~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_68, c_45])).
% 1.98/1.31  tff(c_75, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_71])).
% 1.98/1.31  tff(c_77, plain, (v1_relat_1(u1_orders_2('#skF_1'))), inference(splitRight, [status(thm)], [c_44])).
% 1.98/1.31  tff(c_6, plain, (![A_1, B_3]: (r6_relat_2(A_1, B_3) | ~r2_wellord1(A_1, B_3) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.98/1.31  tff(c_79, plain, (![A_38, B_39]: (r1_relat_2(A_38, B_39) | ~r2_wellord1(A_38, B_39) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.98/1.31  tff(c_82, plain, (r1_relat_2(u1_orders_2('#skF_1'), '#skF_2') | ~v1_relat_1(u1_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_79])).
% 1.98/1.31  tff(c_85, plain, (r1_relat_2(u1_orders_2('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_82])).
% 1.98/1.31  tff(c_22, plain, (![B_12, A_11]: (r7_relat_2(B_12, A_11) | ~r6_relat_2(B_12, A_11) | ~r1_relat_2(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.98/1.31  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.98/1.31  tff(c_28, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v6_orders_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.98/1.31  tff(c_36, plain, (~v6_orders_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28])).
% 1.98/1.31  tff(c_110, plain, (![B_50, A_51]: (v6_orders_2(B_50, A_51) | ~r7_relat_2(u1_orders_2(A_51), B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_orders_2(A_51))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.98/1.31  tff(c_113, plain, (v6_orders_2('#skF_2', '#skF_1') | ~r7_relat_2(u1_orders_2('#skF_1'), '#skF_2') | ~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_32, c_110])).
% 1.98/1.31  tff(c_116, plain, (v6_orders_2('#skF_2', '#skF_1') | ~r7_relat_2(u1_orders_2('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_113])).
% 1.98/1.31  tff(c_117, plain, (~r7_relat_2(u1_orders_2('#skF_1'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_36, c_116])).
% 1.98/1.31  tff(c_120, plain, (~r6_relat_2(u1_orders_2('#skF_1'), '#skF_2') | ~r1_relat_2(u1_orders_2('#skF_1'), '#skF_2') | ~v1_relat_1(u1_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_117])).
% 1.98/1.31  tff(c_123, plain, (~r6_relat_2(u1_orders_2('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_85, c_120])).
% 1.98/1.31  tff(c_126, plain, (~r2_wellord1(u1_orders_2('#skF_1'), '#skF_2') | ~v1_relat_1(u1_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_6, c_123])).
% 1.98/1.31  tff(c_130, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77, c_30, c_126])).
% 1.98/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.31  
% 1.98/1.31  Inference rules
% 1.98/1.31  ----------------------
% 1.98/1.31  #Ref     : 0
% 1.98/1.31  #Sup     : 14
% 1.98/1.31  #Fact    : 0
% 1.98/1.31  #Define  : 0
% 1.98/1.31  #Split   : 1
% 1.98/1.31  #Chain   : 0
% 1.98/1.31  #Close   : 0
% 1.98/1.31  
% 1.98/1.31  Ordering : KBO
% 1.98/1.31  
% 1.98/1.31  Simplification rules
% 1.98/1.31  ----------------------
% 1.98/1.31  #Subsume      : 2
% 1.98/1.31  #Demod        : 9
% 1.98/1.31  #Tautology    : 4
% 1.98/1.31  #SimpNegUnit  : 1
% 1.98/1.31  #BackRed      : 0
% 1.98/1.31  
% 1.98/1.31  #Partial instantiations: 0
% 1.98/1.31  #Strategies tried      : 1
% 1.98/1.31  
% 1.98/1.31  Timing (in seconds)
% 1.98/1.31  ----------------------
% 1.98/1.31  Preprocessing        : 0.30
% 1.98/1.31  Parsing              : 0.17
% 1.98/1.31  CNF conversion       : 0.02
% 1.98/1.31  Main loop            : 0.17
% 1.98/1.31  Inferencing          : 0.07
% 1.98/1.31  Reduction            : 0.05
% 1.98/1.31  Demodulation         : 0.03
% 1.98/1.31  BG Simplification    : 0.01
% 1.98/1.31  Subsumption          : 0.02
% 1.98/1.31  Abstraction          : 0.01
% 1.98/1.31  MUC search           : 0.00
% 1.98/1.31  Cooper               : 0.00
% 1.98/1.31  Total                : 0.50
% 1.98/1.31  Index Insertion      : 0.00
% 1.98/1.31  Index Deletion       : 0.00
% 1.98/1.31  Index Matching       : 0.00
% 1.98/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
