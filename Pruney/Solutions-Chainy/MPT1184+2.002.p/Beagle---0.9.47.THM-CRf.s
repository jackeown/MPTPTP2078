%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:11 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   57 (  83 expanded)
%              Number of leaves         :   30 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :   80 ( 207 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_orders_2 > r8_relat_2 > r7_relat_2 > r6_relat_2 > r4_relat_2 > r3_orders_1 > r1_relat_2 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_relat_1 > l1_orders_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r3_orders_1,type,(
    r3_orders_1: ( $i * $i ) > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r4_relat_2,type,(
    r4_relat_2: ( $i * $i ) > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

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

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( r3_orders_1(u1_orders_2(A),B)
             => ( v6_orders_2(B,A)
                & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_orders_2)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_60,axiom,(
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

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r3_orders_1(A,B)
        <=> ( r1_relat_2(A,B)
            & r8_relat_2(A,B)
            & r4_relat_2(A,B)
            & r6_relat_2(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_orders_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r7_relat_2(B,A)
      <=> ( r1_relat_2(B,A)
          & r6_relat_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_orders_1)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_orders_2(B,A)
          <=> r7_relat_2(u1_orders_2(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_orders_2)).

tff(c_34,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_63,plain,(
    ! [A_32] :
      ( m1_subset_1(u1_orders_2(A_32),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_32),u1_struct_0(A_32))))
      | ~ l1_orders_2(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_66,plain,(
    ! [A_32] :
      ( v1_relat_1(u1_orders_2(A_32))
      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(A_32),u1_struct_0(A_32)))
      | ~ l1_orders_2(A_32) ) ),
    inference(resolution,[status(thm)],[c_63,c_2])).

tff(c_70,plain,(
    ! [A_33] :
      ( v1_relat_1(u1_orders_2(A_33))
      | ~ l1_orders_2(A_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_66])).

tff(c_30,plain,(
    r3_orders_1(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_49,plain,(
    ! [A_24,B_25] :
      ( r1_relat_2(A_24,B_25)
      | ~ r3_orders_1(A_24,B_25)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_53,plain,
    ( r1_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_49])).

tff(c_54,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_53])).

tff(c_73,plain,(
    ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_54])).

tff(c_77,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_73])).

tff(c_79,plain,(
    v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_12,plain,(
    ! [A_9,B_11] :
      ( r6_relat_2(A_9,B_11)
      | ~ r3_orders_1(A_9,B_11)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_78,plain,(
    r1_relat_2(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( r7_relat_2(B_14,A_13)
      | ~ r6_relat_2(B_14,A_13)
      | ~ r1_relat_2(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_28,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v6_orders_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_44,plain,(
    ~ v6_orders_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28])).

tff(c_112,plain,(
    ! [B_46,A_47] :
      ( v6_orders_2(B_46,A_47)
      | ~ r7_relat_2(u1_orders_2(A_47),B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_orders_2(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_115,plain,
    ( v6_orders_2('#skF_2','#skF_1')
    | ~ r7_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_112])).

tff(c_118,plain,
    ( v6_orders_2('#skF_2','#skF_1')
    | ~ r7_relat_2(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_115])).

tff(c_119,plain,(
    ~ r7_relat_2(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_118])).

tff(c_122,plain,
    ( ~ r6_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ r1_relat_2(u1_orders_2('#skF_1'),'#skF_2')
    | ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(resolution,[status(thm)],[c_22,c_119])).

tff(c_125,plain,(
    ~ r6_relat_2(u1_orders_2('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_78,c_122])).

tff(c_133,plain,
    ( ~ r3_orders_1(u1_orders_2('#skF_1'),'#skF_2')
    | ~ v1_relat_1(u1_orders_2('#skF_1')) ),
    inference(resolution,[status(thm)],[c_12,c_125])).

tff(c_137,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_30,c_133])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:13:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.27  
% 1.98/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.27  %$ v6_orders_2 > r8_relat_2 > r7_relat_2 > r6_relat_2 > r4_relat_2 > r3_orders_1 > r1_relat_2 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_relat_1 > l1_orders_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.98/1.27  
% 1.98/1.27  %Foreground sorts:
% 1.98/1.27  
% 1.98/1.27  
% 1.98/1.27  %Background operators:
% 1.98/1.27  
% 1.98/1.27  
% 1.98/1.27  %Foreground operators:
% 1.98/1.27  tff(r3_orders_1, type, r3_orders_1: ($i * $i) > $o).
% 1.98/1.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.98/1.27  tff(r4_relat_2, type, r4_relat_2: ($i * $i) > $o).
% 1.98/1.27  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 1.98/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.27  tff(r6_relat_2, type, r6_relat_2: ($i * $i) > $o).
% 1.98/1.27  tff(r1_relat_2, type, r1_relat_2: ($i * $i) > $o).
% 1.98/1.27  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.27  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.27  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 1.98/1.27  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 1.98/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.98/1.27  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.98/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.98/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.98/1.27  tff(r7_relat_2, type, r7_relat_2: ($i * $i) > $o).
% 1.98/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.27  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 1.98/1.27  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 1.98/1.27  tff(r8_relat_2, type, r8_relat_2: ($i * $i) > $o).
% 1.98/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.98/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.98/1.27  
% 2.17/1.29  tff(f_89, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r3_orders_1(u1_orders_2(A), B) => (v6_orders_2(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t135_orders_2)).
% 2.17/1.29  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.17/1.29  tff(f_60, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 2.17/1.29  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.17/1.29  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (r3_orders_1(A, B) <=> (((r1_relat_2(A, B) & r8_relat_2(A, B)) & r4_relat_2(A, B)) & r6_relat_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_orders_1)).
% 2.17/1.29  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (r7_relat_2(B, A) <=> (r1_relat_2(B, A) & r6_relat_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_orders_1)).
% 2.17/1.29  tff(f_43, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_orders_2(B, A) <=> r7_relat_2(u1_orders_2(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_orders_2)).
% 2.17/1.29  tff(c_34, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.17/1.29  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.17/1.29  tff(c_63, plain, (![A_32]: (m1_subset_1(u1_orders_2(A_32), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_32), u1_struct_0(A_32)))) | ~l1_orders_2(A_32))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.17/1.29  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.17/1.29  tff(c_66, plain, (![A_32]: (v1_relat_1(u1_orders_2(A_32)) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(A_32), u1_struct_0(A_32))) | ~l1_orders_2(A_32))), inference(resolution, [status(thm)], [c_63, c_2])).
% 2.17/1.29  tff(c_70, plain, (![A_33]: (v1_relat_1(u1_orders_2(A_33)) | ~l1_orders_2(A_33))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_66])).
% 2.17/1.29  tff(c_30, plain, (r3_orders_1(u1_orders_2('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.17/1.29  tff(c_49, plain, (![A_24, B_25]: (r1_relat_2(A_24, B_25) | ~r3_orders_1(A_24, B_25) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.17/1.29  tff(c_53, plain, (r1_relat_2(u1_orders_2('#skF_1'), '#skF_2') | ~v1_relat_1(u1_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_49])).
% 2.17/1.29  tff(c_54, plain, (~v1_relat_1(u1_orders_2('#skF_1'))), inference(splitLeft, [status(thm)], [c_53])).
% 2.17/1.29  tff(c_73, plain, (~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_70, c_54])).
% 2.17/1.29  tff(c_77, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_73])).
% 2.17/1.29  tff(c_79, plain, (v1_relat_1(u1_orders_2('#skF_1'))), inference(splitRight, [status(thm)], [c_53])).
% 2.17/1.29  tff(c_12, plain, (![A_9, B_11]: (r6_relat_2(A_9, B_11) | ~r3_orders_1(A_9, B_11) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.17/1.29  tff(c_78, plain, (r1_relat_2(u1_orders_2('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_53])).
% 2.17/1.29  tff(c_22, plain, (![B_14, A_13]: (r7_relat_2(B_14, A_13) | ~r6_relat_2(B_14, A_13) | ~r1_relat_2(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.17/1.29  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.17/1.29  tff(c_28, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v6_orders_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.17/1.29  tff(c_44, plain, (~v6_orders_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28])).
% 2.17/1.29  tff(c_112, plain, (![B_46, A_47]: (v6_orders_2(B_46, A_47) | ~r7_relat_2(u1_orders_2(A_47), B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_orders_2(A_47))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.17/1.29  tff(c_115, plain, (v6_orders_2('#skF_2', '#skF_1') | ~r7_relat_2(u1_orders_2('#skF_1'), '#skF_2') | ~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_32, c_112])).
% 2.17/1.29  tff(c_118, plain, (v6_orders_2('#skF_2', '#skF_1') | ~r7_relat_2(u1_orders_2('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_115])).
% 2.17/1.29  tff(c_119, plain, (~r7_relat_2(u1_orders_2('#skF_1'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_44, c_118])).
% 2.17/1.29  tff(c_122, plain, (~r6_relat_2(u1_orders_2('#skF_1'), '#skF_2') | ~r1_relat_2(u1_orders_2('#skF_1'), '#skF_2') | ~v1_relat_1(u1_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_119])).
% 2.17/1.29  tff(c_125, plain, (~r6_relat_2(u1_orders_2('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_78, c_122])).
% 2.17/1.29  tff(c_133, plain, (~r3_orders_1(u1_orders_2('#skF_1'), '#skF_2') | ~v1_relat_1(u1_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_12, c_125])).
% 2.17/1.29  tff(c_137, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79, c_30, c_133])).
% 2.17/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.29  
% 2.17/1.29  Inference rules
% 2.17/1.29  ----------------------
% 2.17/1.29  #Ref     : 0
% 2.17/1.29  #Sup     : 13
% 2.17/1.29  #Fact    : 0
% 2.17/1.29  #Define  : 0
% 2.17/1.29  #Split   : 3
% 2.17/1.29  #Chain   : 0
% 2.17/1.29  #Close   : 0
% 2.17/1.29  
% 2.17/1.29  Ordering : KBO
% 2.17/1.29  
% 2.17/1.29  Simplification rules
% 2.17/1.29  ----------------------
% 2.17/1.29  #Subsume      : 1
% 2.17/1.29  #Demod        : 10
% 2.17/1.29  #Tautology    : 3
% 2.17/1.29  #SimpNegUnit  : 1
% 2.17/1.29  #BackRed      : 0
% 2.17/1.29  
% 2.17/1.29  #Partial instantiations: 0
% 2.17/1.29  #Strategies tried      : 1
% 2.17/1.29  
% 2.17/1.29  Timing (in seconds)
% 2.17/1.29  ----------------------
% 2.17/1.29  Preprocessing        : 0.29
% 2.17/1.29  Parsing              : 0.16
% 2.17/1.29  CNF conversion       : 0.02
% 2.17/1.29  Main loop            : 0.16
% 2.17/1.29  Inferencing          : 0.07
% 2.17/1.29  Reduction            : 0.04
% 2.17/1.29  Demodulation         : 0.03
% 2.17/1.29  BG Simplification    : 0.01
% 2.17/1.29  Subsumption          : 0.02
% 2.17/1.29  Abstraction          : 0.01
% 2.17/1.29  MUC search           : 0.00
% 2.17/1.29  Cooper               : 0.00
% 2.17/1.29  Total                : 0.47
% 2.17/1.29  Index Insertion      : 0.00
% 2.17/1.29  Index Deletion       : 0.00
% 2.17/1.29  Index Matching       : 0.00
% 2.17/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
